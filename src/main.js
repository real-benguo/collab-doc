/* ============================================================
 * 共笔 · 多人在线协同文档
 *   编辑器：Quill 2
 *   协同内核：Yjs (CRDT)
 *   传输：公共 MQTT（broker.emqx.io）
 *   加密：PBKDF2 派生密钥 + AES-GCM，端到端
 * ============================================================ */

import * as Y from 'yjs'
import Quill from 'quill'
import QuillCursors from 'quill-cursors'
import { QuillBinding } from 'y-quill'
import {
  Awareness,
  applyAwarenessUpdate,
  encodeAwarenessUpdate,
  removeAwarenessStates
} from 'y-protocols/awareness'
import 'quill/dist/quill.snow.css'
import 'quill-cursors/css'

/* ---------------- 常量 ---------------- */

const BROKER   = 'wss://broker.emqx.io:8084/mqtt'
const PREFIX   = 'benguo/collab/v1'
const SNAP_MS  = 8000    // 全量快照心跳
const AW_MS    = 3000    // 在线状态心跳
const PEER_TTL = 15000   // 多久没动静算掉线
const LOCAL_MS = 1200    // 本地缓存防抖

const T_UPDATE = 1
const T_SNAP   = 2
const T_AWARE  = 3
const T_VERIFY = 4

const PALETTE = [
  '#e5534b', '#e8842c', '#d4a72c', '#4caf7d', '#2f9e8f',
  '#3d8bd4', '#6a6ee0', '#a563d6', '#d6558f', '#8a6a4f'
]

/* ---------------- 小工具 ---------------- */

const $ = id => document.getElementById(id)
const te = new TextEncoder()
const td = new TextDecoder()

function toast (msg, ms = 2200) {
  const el = $('toast')
  el.textContent = msg
  el.classList.remove('hidden')
  clearTimeout(toast._t)
  toast._t = setTimeout(() => el.classList.add('hidden'), ms)
}

function hex (buf) {
  return [...new Uint8Array(buf)].map(b => b.toString(16).padStart(2, '0')).join('')
}

function toBase64 (u8) {
  let s = ''
  for (let i = 0; i < u8.length; i += 0x8000) {
    s += String.fromCharCode.apply(null, u8.subarray(i, i + 0x8000))
  }
  return btoa(s)
}

function fromBase64 (b64) {
  const bin = atob(b64)
  const out = new Uint8Array(bin.length)
  for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i)
  return out
}

/* ---------------- 加密 ---------------- */

async function deriveKey (room, password) {
  const base = await crypto.subtle.importKey(
    'raw', te.encode(password), 'PBKDF2', false, ['deriveKey']
  )
  return crypto.subtle.deriveKey(
    {
      name: 'PBKDF2',
      salt: te.encode('gongbi|' + room.trim().toLowerCase()),
      iterations: 150000,
      hash: 'SHA-256'
    },
    base,
    { name: 'AES-GCM', length: 256 },
    false,
    ['encrypt', 'decrypt']
  )
}

async function encrypt (key, bytes) {
  const iv = crypto.getRandomValues(new Uint8Array(12))
  const ct = new Uint8Array(await crypto.subtle.encrypt({ name: 'AES-GCM', iv }, key, bytes))
  const out = new Uint8Array(12 + ct.length)
  out.set(iv, 0)
  out.set(ct, 12)
  return out
}

async function decrypt (key, buf) {
  const iv = buf.subarray(0, 12)
  const ct = buf.subarray(12)
  const pt = await crypto.subtle.decrypt({ name: 'AES-GCM', iv }, key, ct)
  return new Uint8Array(pt)
}

/* 房间号不直接出现在公共主题上，先哈希一层 */
async function roomHash (room) {
  const d = await crypto.subtle.digest('SHA-256', te.encode('gongbi-topic|' + room.trim().toLowerCase()))
  return hex(d).slice(0, 20)
}

/* ---------------- 信封 ---------------- */
/* [1B type][4B yjsClientId][1B idLen][id...][data...] */

function pack (type, clientId, myId, data) {
  const idb = te.encode(myId)
  const out = new Uint8Array(1 + 4 + 1 + idb.length + data.length)
  const dv = new DataView(out.buffer)
  dv.setUint8(0, type)
  dv.setUint32(1, clientId)
  dv.setUint8(5, idb.length)
  out.set(idb, 6)
  out.set(data, 6 + idb.length)
  return out
}

function unpack (u8) {
  const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength)
  const type = dv.getUint8(0)
  const clientId = dv.getUint32(1)
  const idLen = dv.getUint8(5)
  const myId = td.decode(u8.subarray(6, 6 + idLen))
  const data = u8.subarray(6 + idLen)
  return { type, clientId, myId, data }
}

/* ---------------- 全局状态 ---------------- */

let room = ''
let pass = ''
let myName = ''
let rh = ''
let key = null
let myMqttId = ''
let client = null
let ydoc = null
let ytext = null
let quill = null
let binding = null
let awareness = null
let connected = false
let joined = false

const topics = {
  update: '', snap: '', snapAll: '', aware: '', awareAll: '', verify: '', verifyAll: ''
}
const lastSeen = new Map()      // mqttId -> { clientId, ts }
let snapTimer = null
let awareTimer = null
let localTimer = null

/* ---------------- MQTT ---------------- */

function pub (topic, payload, opts) {
  if (!client || !connected) return
  try {
    client.publish(topic, payload, Object.assign({ qos: 1, retain: false }, opts))
  } catch (e) { /* 断线时忽略，靠快照补齐 */ }
}

function connectBroker () {
  return new Promise((resolve, reject) => {
    if (!window.mqtt) return reject(new Error('通讯组件没加载出来（vendor/mqtt.min.js 缺失）'))
    client = window.mqtt.connect(BROKER, {
      clientId: 'gb_' + myMqttId.slice(0, 18),
      clean: true,
      keepalive: 45,
      reconnectPeriod: 2500,
      connectTimeout: 15000,
      protocolVersion: 4
    })

    let settled = false
    const done = ok => {
      if (settled) return
      settled = true
      ok ? resolve() : reject(new Error('连不上中转服务器，检查一下网络'))
    }

    client.on('connect', () => {
      connected = true
      setConn('on', '已连接')
      subscribeAll()
      onConnected()
      done(true)
    })

    client.on('reconnect', () => { setConn('mid', '重连中…') })
    client.on('close', () => {
      connected = false
      setConn('off', '断线了')
      if (joined) setSync('offline', '离线（改动只存在本地）')
    })
    client.on('error', err => {
      console.warn('mqtt error', err)
      setConn('off', '连接异常')
      done(false)
    })

    client.on('message', (topic, payload) => { onMessage(topic, payload).catch(() => {}) })

    setTimeout(() => done(false), 16000)
  })
}

function subscribeAll () {
  const list = [topics.update, topics.snapAll, topics.awareAll, topics.verifyAll]
  list.forEach(t => client.subscribe(t, { qos: 1 }, () => {}))
}

/* 断线重连后把本地全量重新播一遍 */
function onConnected () {
  if (!joined) return
  publishSnapshot()
  broadcastAwareness()
  setSync('ok', '已同步')
}

async function onMessage (topic, payload) {
  const buf = payload instanceof Uint8Array ? payload : new Uint8Array(payload)
  let plain
  try {
    plain = await decrypt(key, buf)
  } catch (e) {
    // 只有别人的消息能证明密码对不对
    if (topic.startsWith(topics.verifyAll)) flagWrongPassword()
    return
  }

  let msg
  try { msg = unpack(plain) } catch (e) { return }

  if (msg.myId) lastSeen.set(msg.myId, { clientId: msg.clientId, ts: Date.now() })

  if (msg.type === T_UPDATE || msg.type === T_SNAP) {
    if (msg.data.length) {
      Y.applyUpdate(ydoc, msg.data, 'remote')
      setSync('ok', '已同步')
    }
  } else if (msg.type === T_AWARE) {
    if (msg.myId === myMqttId) return
    try {
      applyAwarenessUpdate(awareness, msg.data, 'remote')
      renderPeers()
    } catch (e) {}
  } else if (msg.type === T_VERIFY) {
    if (td.decode(msg.data).startsWith('gongbi-v1:' + rh)) markPasswordOk()
  }
}

/* ---------------- 发布 ---------------- */

function publishSnapshot () {
  if (!joined) return
  const state = Y.encodeStateAsUpdate(ydoc)
  sendEnc(T_SNAP, state, topics.snap, { retain: true, qos: 1 })
}

function broadcastAwareness () {
  if (!joined || !connected) return
  const upd = encodeAwarenessUpdate(awareness, [ydoc.clientID])
  sendEnc(T_AWARE, upd, topics.aware, { retain: false, qos: 0 })
}

async function sendEnc (type, data, topic, opts) {
  if (!key) return
  try {
    const packed = pack(type, ydoc.clientID, myMqttId, data)
    const enc = await encrypt(key, packed)
    pub(topic, enc, opts)
  } catch (e) {}
}

/* ---------------- 本地缓存 ---------------- */

function localKey () { return 'gongbi:doc:' + rh }

function saveLocal () {
  clearTimeout(localTimer)
  localTimer = setTimeout(() => {
    try {
      localStorage.setItem(localKey(), toBase64(Y.encodeStateAsUpdate(ydoc)))
      localStorage.setItem(localKey() + ':meta', JSON.stringify({ room, name: myName, t: Date.now() }))
    } catch (e) {}
  }, LOCAL_MS)
}

function loadLocal () {
  try {
    const s = localStorage.getItem(localKey())
    if (s) {
      Y.applyUpdate(ydoc, fromBase64(s), 'local')
      return true
    }
  } catch (e) {}
  return false
}

/* ---------------- 界面 ---------------- */

function setConn (cls, text) {
  const dot = $('conn-dot')
  if (!dot) return
  dot.className = 'dot ' + cls
  $('conn-text').textContent = text
}

function setSync (state, text) {
  const el = $('sync-hint')
  if (!el) return
  el.textContent = text
  el.className = 'sync-hint' + (state === 'ok' ? '' : ' ' + state)
}

let wrongPwFlagged = false
function flagWrongPassword () {
  if (wrongPwFlagged) return
  wrongPwFlagged = true
  toast('密码可能不对——别人发来的内容解不开。确认一下密码是不是和同事一致。', 6000)
}

function markPasswordOk () { wrongPwFlagged = false }

function colorOf (str) {
  let h = 0
  for (let i = 0; i < str.length; i++) h = (h * 31 + str.charCodeAt(i)) >>> 0
  return PALETTE[h % PALETTE.length]
}

function renderPeers () {
  const box = $('peers')
  if (!box || !awareness) return
  const states = awareness.getStates()
  const list = []
  states.forEach((st, id) => {
    const u = st.user || {}
    list.push({ id, name: u.name || '某人', color: u.color || colorOf(String(id)) })
  })
  list.sort((a, b) => (a.id === ydoc.clientID ? -1 : b.id === ydoc.clientID ? 1 : 0))
  box.innerHTML = ''
  list.slice(0, 8).forEach(p => {
    const d = document.createElement('div')
    d.className = 'peer'
    d.style.background = p.color
    d.textContent = (p.name || '?').trim().slice(0, 1)
    d.title = p.id === ydoc.clientID ? p.name + '（你）' : p.name
    box.appendChild(d)
  })
  if (list.length > 1) {
    const n = document.createElement('div')
    n.className = 'peer'
    n.style.background = '#2b3140'
    n.style.color = '#9aa3b5'
    n.textContent = list.length
    n.title = list.length + ' 人在线'
    box.appendChild(n)
  }
}

/* 掉线的人自动移除 */
function startPeerSweeper () {
  setInterval(() => {
    const now = Date.now()
    const dead = []
    lastSeen.forEach((v, mid) => {
      if (now - v.ts > PEER_TTL) {
        dead.push(v.clientId)
        lastSeen.delete(mid)
      }
    })
    if (dead.length) {
      try {
        removeAwarenessStates(awareness, dead, 'timeout')
        renderPeers()
      } catch (e) {}
    }
  }, 5000)
}

/* ---------------- 保存到本地 ---------------- */

function docBaseName () {
  const d = new Date()
  const p = n => String(n).padStart(2, '0')
  return `${room}_${d.getFullYear()}${p(d.getMonth() + 1)}${p(d.getDate())}_${p(d.getHours())}${p(d.getMinutes())}`
}

function download (name, content, mime) {
  const blob = new Blob([content], { type: mime })
  const url = URL.createObjectURL(blob)
  const a = document.createElement('a')
  a.href = url
  a.download = name
  document.body.appendChild(a)
  a.click()
  a.remove()
  setTimeout(() => URL.revokeObjectURL(url), 4000)
}

const HTML_SHELL = (title, body) => `<!DOCTYPE html>
<html lang="zh-CN"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>${title.replace(/[<>&]/g, '')}</title>
<style>
  body{max-width:760px;margin:0 auto;padding:48px 22px 90px;
       font:16px/1.85 -apple-system,BlinkMacSystemFont,"PingFang SC","Microsoft YaHei",sans-serif;
       color:#1c2128;background:#fff;-webkit-font-smoothing:antialiased}
  h1{font-size:27px;margin:20px 0 10px}h2{font-size:22px;margin:18px 0 9px}h3{font-size:18px;margin:16px 0 8px}
  blockquote{border-left:3px solid #d7dde8;margin:12px 0;padding-left:14px;color:#5c6675}
  pre{background:#f4f6fa;border-radius:8px;padding:12px 14px;overflow:auto;font-size:14px}
  code{background:#f4f6fa;border-radius:4px;padding:1px 5px;font-size:.92em}
  pre code{background:none;padding:0}
  ul,ol{padding-left:26px}li{margin:3px 0}
  a{color:#2f6fe4}
  ul li[data-list=checked],ul li[data-list=unchecked]{list-style:none;position:relative;margin-left:-22px}
  ul li[data-list=checked]::before{content:"☑ "}
  ul li[data-list=unchecked]::before{content:"☐ "}
  hr{border:0;border-top:1px solid #e6e9ef;margin:24px 0}
</style></head>
<body>${body}</body></html>`

function exportAs (fmt) {
  if (!quill) return
  const base = docBaseName()
  if (fmt === 'html') {
    download(base + '.html', HTML_SHELL(room, quill.root.innerHTML), 'text/html;charset=utf-8')
  } else if (fmt === 'txt') {
    download(base + '.txt', quill.getText().replace(/\n{3,}/g, '\n\n').trim() + '\n', 'text/plain;charset=utf-8')
  } else if (fmt === 'md') {
    const md = quill.getSemanticHTML ? quill.getSemanticHTML() : quill.root.innerHTML
    download(base + '.md', htmlToMd(md), 'text/markdown;charset=utf-8')
  }
  toast('已存到下载文件夹')
}

/* 极简 HTML → Markdown（够日常用） */
function htmlToMd (html) {
  const d = document.createElement('div')
  d.innerHTML = html
  const walk = node => {
    let out = ''
    node.childNodes.forEach(n => {
      if (n.nodeType === 3) { out += n.textContent.replace(/\s+/g, ' '); return }
      if (n.nodeType !== 1) return
      const tag = n.tagName.toLowerCase()
      const inner = walk(n)
      if (tag === 'br') out += '\n'
      else if (/^h[1-6]$/.test(tag)) out += '\n' + '#'.repeat(+tag[1]) + ' ' + inner.trim() + '\n'
      else if (tag === 'strong' || tag === 'b') out += '**' + inner + '**'
      else if (tag === 'em' || tag === 'i') out += '*' + inner + '*'
      else if (tag === 'u') out += '<u>' + inner + '</u>'
      else if (tag === 's' || tag === 'strike' || tag === 'del') out += '~~' + inner + '~~'
      else if (tag === 'code') out += '`' + inner + '`'
      else if (tag === 'pre') out += '\n```\n' + inner.replace(/\n$/, '') + '\n```\n'
      else if (tag === 'blockquote') out += '\n' + inner.trim().split('\n').map(l => '> ' + l).join('\n') + '\n'
      else if (tag === 'a') out += '[' + inner + '](' + n.getAttribute('href') + ')'
      else if (tag === 'li') {
        const parent = n.parentElement
        const ordered = parent && parent.tagName.toLowerCase() === 'ol'
        const dl = n.getAttribute('data-list')
        let mark = ordered ? '1. ' : '- '
        if (dl === 'checked') mark = '- [x] '
        if (dl === 'unchecked') mark = '- [ ] '
        out += '\n' + mark + inner.trim()
      } else if (tag === 'p' || tag === 'div') out += '\n' + inner + '\n'
      else out += inner
    })
    return out
  }
  return walk(d).replace(/\n{3,}/g, '\n\n').trim() + '\n'
}

/* ---------------- 启动 ---------------- */

async function enter (roomName, password, name, isNew) {
  const gateMsg = $('gate-msg')
  const setMsg = (t, cls) => { gateMsg.textContent = t; gateMsg.className = 'gate-msg' + (cls ? ' ' + cls : '') }

  if (!roomName || roomName.trim().length < 2) return setMsg('房间号太短了，至少 2 个字')
  if (!password || password.length < 4) return setMsg('密码至少 4 位')
  if (!name || !name.trim()) return setMsg('填个名字吧，别人好认你')

  setMsg('正在加密并连接…', 'busy')

  try {
    room = roomName.trim()
    pass = password
    myName = name.trim()

    myMqttId = localStorage.getItem('gongbi:cid')
    if (!myMqttId) {
      myMqttId = hex(crypto.getRandomValues(new Uint8Array(10)))
      localStorage.setItem('gongbi:cid', myMqttId)
    }

    key = await deriveKey(room, pass)
    rh = await roomHash(room)

    topics.update    = `${PREFIX}/${rh}/u`
    topics.snap      = `${PREFIX}/${rh}/s/${myMqttId}`
    topics.snapAll   = `${PREFIX}/${rh}/s/+`
    topics.aware     = `${PREFIX}/${rh}/a/${myMqttId}`
    topics.awareAll  = `${PREFIX}/${rh}/a/+`
    topics.verify    = `${PREFIX}/${rh}/v/${myMqttId}`
    topics.verifyAll = `${PREFIX}/${rh}/v/+`

    ydoc = new Y.Doc()
    ytext = ydoc.getText('quill')
    awareness = new Awareness(ydoc)
    awareness.setLocalStateField('user', { name: myName, color: colorOf(myMqttId) })

    const restored = loadLocal()

    setMsg('正在连接中转服务器…', 'busy')
    await connectBroker()

    setMsg('进入中…', 'busy')
    startEditor()

    joined = true

    // 告诉大家我在，并且校验密码
    sendEnc(T_VERIFY, te.encode('gongbi-v1:' + rh), topics.verify, { retain: true, qos: 1 })
    publishSnapshot()
    broadcastAwareness()

    snapTimer  = setInterval(publishSnapshot, SNAP_MS)
    awareTimer = setInterval(broadcastAwareness, AW_MS)
    startPeerSweeper()

    $('gate').classList.add('hidden')
    $('app').classList.remove('hidden')
    $('room-label').textContent = room

    setSync('ok', '已同步')
    if (isNew) {
      setTimeout(() => showShare(), 350)
    } else if (!restored) {
      toast('已进入「' + room + '」，内容会自动同步', 2600)
    }
  } catch (err) {
    console.error(err)
    setMsg(err.message || '进不去，换个网络再试试', '')
  }
}

function startEditor () {
  Quill.register('modules/cursors', QuillCursors)

  quill = new Quill('#editor', {
    theme: 'snow',
    placeholder: '开始写吧…  几个人同时打字也不会互相覆盖。',
    modules: {
      toolbar: '#toolbar',
      cursors: { transformOnTextChange: true },
      history: { userOnly: true }
    }
  })

  binding = new QuillBinding(ytext, quill, awareness)

  // 本地改动 → 立刻广播增量
  ydoc.on('update', (update, origin) => {
    if (origin === 'remote' || origin === 'local') {
      if (origin === 'local') saveLocal()
      return
    }
    if (!joined) return
    sendEnc(T_UPDATE, update, topics.update, { retain: false, qos: 1 })
    saveLocal()
    setSync('pending', '同步中…')
    setTimeout(() => { if (connected) setSync('ok', '已同步') }, 700)
  })

  // 光标/在线状态变化 → 尽快广播
  let awDeb = null
  awareness.on('update', ({ added, updated, removed }) => {
    // 注意：y-protocols 这里给的是数组，不是 Set
    const mine = added.includes(ydoc.clientID) ||
                 updated.includes(ydoc.clientID) ||
                 removed.includes(ydoc.clientID)
    if (mine && joined) {
      clearTimeout(awDeb)
      awDeb = setTimeout(broadcastAwareness, 150)
    }
    renderPeers()
  })

  renderPeers()
}

/* ---------------- 分享 / 新建 ---------------- */

function randomRoom () {
  const w = ['apple', 'river', 'tiger', 'cloud', 'stone', 'lamp', 'paper', 'sugar', 'panda', 'mint', 'tower', 'crane']
  const a = w[Math.floor(Math.random() * w.length)]
  const b = w[Math.floor(Math.random() * w.length)]
  const n = Math.floor(Math.random() * 9000 + 1000)
  return `${a}-${b}-${n}`
}

function randomPass () {
  const s = 'abcdefghjkmnpqrstuvwxyz23456789'
  let out = ''
  const r = crypto.getRandomValues(new Uint8Array(6))
  for (let i = 0; i < 6; i++) out += s[r[i] % s.length]
  return out
}

function showShare () {
  $('share-room').textContent = room
  $('share-pass').textContent = pass
  $('share-modal').classList.remove('hidden')
}

/* ---------------- 事件绑定 ---------------- */

$('btn-enter').onclick = () => {
  enter($('in-room').value, $('in-pass').value, $('in-name').value, false)
}

$('btn-new').onclick = () => {
  const r = randomRoom()
  const p = randomPass()
  $('in-room').value = r
  $('in-pass').value = p
  if (!$('in-name').value.trim()) {
    const names = ['我', '小明', '老王', '阿May', '大熊']
    $('in-name').value = names[Math.floor(Math.random() * names.length)]
  }
  $('btn-eye').textContent = '🙈'
  $('in-pass').type = 'text'
  toast('房间号和密码已生成，进入后可以再分享给同事', 3000)
  enter(r, p, $('in-name').value, true)
}

$('btn-eye').onclick = () => {
  const inp = $('in-pass')
  const show = inp.type === 'password'
  inp.type = show ? 'text' : 'password'
  $('btn-eye').textContent = show ? '🙈' : '👁'
}

$('in-pass').addEventListener('keydown', e => { if (e.key === 'Enter') $('btn-enter').click() })
$('in-room').addEventListener('keydown', e => { if (e.key === 'Enter') $('in-pass').focus() })
$('in-name').addEventListener('keydown', e => { if (e.key === 'Enter') $('btn-enter').click() })

$('btn-share').onclick = () => showShare()
$('btn-close-share').onclick = () => $('share-modal').classList.add('hidden')

$('btn-copy-share').onclick = async () => {
  const text = `一起写文档，打开这个网址：\n${location.origin + location.pathname}\n房间号：${room}\n密码：${pass}`
  try {
    await navigator.clipboard.writeText(text)
    toast('复制好了，粘给同事就行')
  } catch (e) {
    const ta = document.createElement('textarea')
    ta.value = text
    document.body.appendChild(ta)
    ta.select()
    document.execCommand('copy')
    ta.remove()
    toast('复制好了，粘给同事就行')
  }
}

$('btn-save').onclick = e => {
  e.stopPropagation()
  const m = $('save-menu')
  const r = e.currentTarget.getBoundingClientRect()
  m.style.top = (r.bottom + 8) + 'px'
  m.style.left = Math.max(10, Math.min(window.innerWidth - 270, r.right - 250)) + 'px'
  m.classList.toggle('hidden')
}

document.querySelectorAll('#save-menu button').forEach(b => {
  b.onclick = () => {
    exportAs(b.dataset.fmt)
    $('save-menu').classList.add('hidden')
  }
})

document.addEventListener('click', e => {
  if (!e.target.closest('#save-menu') && !e.target.closest('#btn-save')) {
    $('save-menu').classList.add('hidden')
  }
})

$('btn-leave').onclick = () => {
  if (!confirm('退出后，这份文档只剩你自己电脑里的缓存。\n记得先「存到本地」再走。\n\n确定退出？')) return
  publishSnapshot()
  sendEnc(T_VERIFY, te.encode('gongbi-v1:' + rh), topics.verify, { retain: true, qos: 1 })
  setTimeout(() => location.reload(), 300)
}

window.addEventListener('beforeunload', () => {
  try { saveLocal() } catch (e) {}
})

/* 预填上次用的名字 */
try {
  const last = localStorage.getItem('gongbi:lastname')
  if (last) $('in-name').value = last
  $('in-name').addEventListener('change', () => {
    localStorage.setItem('gongbi:lastname', $('in-name').value.trim())
  })
} catch (e) {}
