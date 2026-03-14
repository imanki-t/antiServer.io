const mineflayer = require('mineflayer');
const axios = require('axios');
const net = require('net');
const dns = require('dns').promises;
const express = require('express');
const path = require('path');
const os = require('os');
const http = require('http');
const { Server } = require('socket.io');
const mongoose = require('mongoose');
const diskusage = require('diskusage');
const fs = require('fs');

// ─────────────────────────────────────────────
// CONFIG
// ─────────────────────────────────────────────
let config;
try {
  config = JSON.parse(fs.readFileSync(path.join(__dirname, 'config.json'), 'utf8'));
} catch (err) {
  console.error('❌ Failed to load config.json:', err.message);
  process.exit(1);
}

const BOT_HOST        = process.env.BOT_HOST        || config.bot.host;
const BOT_PORT        = parseInt(process.env.BOT_PORT, 10) || config.bot.port;
const BOT_USERNAME    = process.env.BOT_USERNAME    || config.bot.username;
const BOT_VERSION     = config.bot.version;
const DISCORD_WEBHOOK = process.env.DISCORD_WEBHOOK || config.webhooks.discord;
const CHAT_WEBHOOK    = process.env.CHAT_WEBHOOK    || config.webhooks.chat;
const MESSAGE_WEBHOOK = process.env.MESSAGE_WEBHOOK || config.webhooks.message;
const WEB_SERVER_PORT = process.env.PORT            || config.server.port;
const MONGO_URI       = process.env.MONGO_URI       || config.database.mongoUri;

const RECONNECT_DELAY         = config.intervals.reconnect;        // base ms
const SOCKET_IO_UPDATE_INTERVAL = config.intervals.socketUpdate;
const ACTIVITY_CHECK_INTERVAL = config.intervals.activityCheck;
const ONE_HOUR                = config.timeLimits.oneHour;
const FIFTEEN_SECONDS         = config.timeLimits.fifteenSeconds;

const DEFAULT_EMBED_COLOR = config.embedColors.default;
const SUCCESS_EMBED_COLOR = config.embedColors.success;
const WARNING_EMBED_COLOR = config.embedColors.warning;
const ERROR_EMBED_COLOR   = config.embedColors.error;
const INFO_EMBED_COLOR    = config.embedColors.info;

const FACES          = config.faces;
const AUTO_TIME_FREEZE = config.features.autoTimeFreeze;
const ANTI_AFK       = config.features.antiAFK;
const AUTO_REJOIN    = config.features.autoRejoin;

// ─────────────────────────────────────────────
// EXPRESS + SOCKET.IO
// ─────────────────────────────────────────────
const app    = express();
const server = http.createServer(app);
const io     = new Server(server);

app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

// ─────────────────────────────────────────────
// MONGODB
// ─────────────────────────────────────────────
mongoose.connect(MONGO_URI)
  .then(() => console.log('✅ MongoDB connected'))
  .catch(err => console.error('❌ MongoDB connection error:', err));

const MinecraftChat = mongoose.model('MinecraftChat', new mongoose.Schema({
  username:  String,
  chat:      String,
  timestamp: { type: Date, default: Date.now },
}));

const PlayerFace = mongoose.model('PlayerFace', new mongoose.Schema({
  username:    { type: String, unique: true },
  face:        String,
  isCustom:    { type: Boolean, default: false },
  lastUpdated: { type: Date, default: Date.now },
}));

// ─────────────────────────────────────────────
// STATE
// ─────────────────────────────────────────────
let bot               = null;
let isBotOnline       = false;
let botStartTime      = null;
let movementCount     = 0;
let lastOnlineTime    = null;
let isTimeFrozen      = false;
let otherPlayersOnline = 0;
let isShuttingDown    = false;
let consecutiveFailures = 0;
let nextDotFaceIndex  = 0;
let behaviorPhase     = 'active';
let nearbyPlayers     = [];
let lastPlayerCheckTime = 0;
let mistakeCounter    = 0;
let isInSpectatorMode = false;

// ── Timer handles ──
let reconnectTimeout        = null;
let actionSchedulerTimeout  = null;
let activityIntervalHandle  = null;  // setInterval handle (was confused with setTimeout before)
let forceRejoinTimeoutHandle = null;

// ── Scheduler epoch: incremented on every disconnect/reconnect.
//    Each scheduleNextAction call captures its epoch; if it no longer
//    matches the global, that entire scheduler chain is dead. ──
let schedulerEpoch = 0;

// ── CPU tracking – must start as {idle, total}, NOT process.cpuUsage() ──
function _buildCpuSnapshot() {
  const cpus = os.cpus();
  let idle = 0, total = 0;
  for (const cpu of cpus) {
    for (const t in cpu.times) total += cpu.times[t];
    idle += cpu.times.idle;
  }
  return { idle, total };
}
let lastCpuSnapshot = _buildCpuSnapshot();

// ─────────────────────────────────────────────
// HELPERS — timers
// ─────────────────────────────────────────────
function clearAllTimers() {
  if (actionSchedulerTimeout)   { clearTimeout(actionSchedulerTimeout);  actionSchedulerTimeout  = null; }
  if (reconnectTimeout)         { clearTimeout(reconnectTimeout);         reconnectTimeout        = null; }
  if (activityIntervalHandle)   { clearInterval(activityIntervalHandle);  activityIntervalHandle  = null; }
  if (forceRejoinTimeoutHandle) { clearTimeout(forceRejoinTimeoutHandle); forceRejoinTimeoutHandle = null; }
}

function resetBotState() {
  isBotOnline       = false;
  botStartTime      = null;
  movementCount     = 0;
  isTimeFrozen      = false;
  otherPlayersOnline = 0;
  behaviorPhase     = 'active';
  nearbyPlayers     = [];
  mistakeCounter    = 0;
  isInSpectatorMode = false;
}

// ─────────────────────────────────────────────
// CPU USAGE (fixed)
// ─────────────────────────────────────────────
function getCpuUsage() {
  const now = _buildCpuSnapshot();
  const idleDiff  = now.idle  - lastCpuSnapshot.idle;
  const totalDiff = now.total - lastCpuSnapshot.total;
  lastCpuSnapshot = now;
  if (totalDiff === 0) return 0;
  return 100 - (100 * idleDiff / totalDiff);
}

// ─────────────────────────────────────────────
// SERVER REACHABILITY CHECK
// Aternos servers go to sleep. Don't waste mineflayer connections
// on a dead socket — do a quick TCP ping first (5 s timeout).
// ─────────────────────────────────────────────
async function isServerReachable(host, port, timeoutMs = 5000) {
  try {
    // Resolve hostname first so DNS errors are caught clearly
    await dns.lookup(host);
  } catch {
    console.log(`🔴 DNS lookup failed for ${host} — server is likely offline`);
    return false;
  }

  return new Promise(resolve => {
    const sock = new net.Socket();
    let done = false;

    const finish = (result) => {
      if (done) return;
      done = true;
      sock.destroy();
      resolve(result);
    };

    sock.setTimeout(timeoutMs);
    sock.once('connect', () => finish(true));
    sock.once('timeout', () => { console.log(`🔴 TCP timeout connecting to ${host}:${port}`); finish(false); });
    sock.once('error',   () => finish(false));
    sock.connect(port, host);
  });
}

// ─────────────────────────────────────────────
// DISCORD WEBHOOKS
// ─────────────────────────────────────────────
async function sendDiscordEmbed(title, description, color = DEFAULT_EMBED_COLOR, fields = []) {
  if (!DISCORD_WEBHOOK) return;
  try {
    await axios.post(DISCORD_WEBHOOK, {
      embeds: [{ title, description, color, fields, timestamp: new Date().toISOString() }],
    });
  } catch (err) { console.error('❌ Discord Webhook Error:', err.message); }
}

async function sendChatEmbed(title, description, color = SUCCESS_EMBED_COLOR, fields = []) {
  if (!CHAT_WEBHOOK) return;
  try {
    await axios.post(CHAT_WEBHOOK, {
      embeds: [{ title, description, color, fields, timestamp: new Date().toISOString() }],
    });
  } catch (err) { console.error('❌ Chat Webhook Error:', err.message); }
}

async function sendPlayerMessage(username, message) {
  if (username === BOT_USERNAME || !MESSAGE_WEBHOOK) return;
  try {
    await axios.post(MESSAGE_WEBHOOK, { content: `💬 **${username}**: ${message}` });
  } catch (err) { console.error('❌ Message Webhook Error:', err.message); }
}

// ─────────────────────────────────────────────
// PLAYER HELPERS
// ─────────────────────────────────────────────
function getOnlinePlayersExcludingBot() {
  if (!bot || !bot.players || !isBotOnline) return [];
  return Object.values(bot.players).filter(p => p.username !== BOT_USERNAME);
}

function updateSpectatorMode() {
  if (!bot || !bot.game) return;
  isInSpectatorMode = bot.game.gameMode === 'spectator' || bot.game.gameMode === 3;
}

function getNearbyPlayers(radius = 50) {
  if (!bot || !bot.entity || !bot.players) return [];
  const botPos = bot.entity.position;
  const nearby = [];
  for (const player of Object.values(bot.players)) {
    if (player.username === BOT_USERNAME || !player.entity) continue;
    const dist = botPos.distanceTo(player.entity.position);
    if (dist <= radius) nearby.push({ username: player.username, distance: dist, position: player.entity.position });
  }
  return nearby;
}

function checkNearbyPlayers() {
  if (!bot || !isBotOnline) return;
  const now = Date.now();
  if (now - lastPlayerCheckTime > 3000) {
    nearbyPlayers = getNearbyPlayers();
    lastPlayerCheckTime = now;
  }
}

function updateBehaviorPhase() {
  if (!botStartTime) return;
  const uptime = (Date.now() - botStartTime) / 60000; // minutes
  if      (uptime < 10) behaviorPhase = 'active';
  else if (uptime < 30) behaviorPhase = 'moderate';
  else                  behaviorPhase = 'idle';
}

// ─────────────────────────────────────────────
// TIME FREEZE
// ─────────────────────────────────────────────
async function freezeTime() {
  if (!bot || !isBotOnline || isTimeFrozen) return;
  try {
    bot.chat('/tick freeze');
    isTimeFrozen = true;
    console.log('⏸️  Time frozen — bot is alone');
    await sendDiscordEmbed('Time Control', 'Time frozen — bot is alone', INFO_EMBED_COLOR);
  } catch (err) { console.error('❌ freezeTime:', err.message); }
}

async function unfreezeTime() {
  if (!bot || !isBotOnline || !isTimeFrozen) return;
  try {
    bot.chat('/tick unfreeze');
    isTimeFrozen = false;
    console.log('▶️  Time unfrozen — players joined');
    await sendDiscordEmbed('Time Control', 'Time unfrozen — players joined', INFO_EMBED_COLOR);
  } catch (err) { console.error('❌ unfreezeTime:', err.message); }
}

async function ensureTimeUnfrozen() {
  if (isTimeFrozen && bot && isBotOnline) {
    try {
      bot.chat('/tick unfreeze');
      isTimeFrozen = false;
      console.log('✅ Time unfrozen before disconnect');
      await new Promise(r => setTimeout(r, 800));
    } catch (err) { console.error('❌ ensureTimeUnfrozen:', err.message); }
  }
}

function checkPlayerCount() {
  if (!bot || !AUTO_TIME_FREEZE || !isBotOnline) return;
  otherPlayersOnline = getOnlinePlayersExcludingBot().length;
  if (otherPlayersOnline === 0 && !isTimeFrozen)  setTimeout(freezeTime, 2000);
  else if (otherPlayersOnline > 0 && isTimeFrozen) unfreezeTime();
}

// ─────────────────────────────────────────────
// SKIN / FACE CACHE
// ─────────────────────────────────────────────
async function getOrCreatePlayerFace(username, uuid) {
  let record = await PlayerFace.findOne({ username });
  if (!record) {
    let skinUrl, isCustom = false;
    if (username.startsWith('.')) {
      // Cracked / offline-mode player — assign a local face
      const used = (await PlayerFace.find({ username: /^\./ }, 'face')).map(r => r.face);
      const free = FACES.filter(f => !used.includes(f));
      const selected = free.length > 0 ? FACES[nextDotFaceIndex++ % FACES.length] : FACES[Math.floor(Math.random() * FACES.length)];
      skinUrl = `./${selected}`;
      record = new PlayerFace({ username, face: selected, isCustom: false });
    } else {
      try {
        const url = `https://crafatar.com/avatars/${uuid || username}?size=32&overlay`;
        await axios.get(url, { responseType: 'arraybuffer', timeout: 5000 });
        skinUrl = url; isCustom = true;
        record = new PlayerFace({ username, face: skinUrl, isCustom: true });
      } catch {
        const selected = FACES[Math.floor(Math.random() * FACES.length)];
        skinUrl = `./${selected}`;
        record = new PlayerFace({ username, face: selected, isCustom: false });
      }
    }
    await record.save();
    return skinUrl;
  }
  return record.isCustom ? record.face : `./${record.face}`;
}

// ─────────────────────────────────────────────
// ACTIONS — weight table
// ─────────────────────────────────────────────
const ACTIONS = {
  WALK_SHORT:         { weight: 12, type: 'movement',    category: 'basic' },
  WALK_LONG:          { weight:  8, type: 'movement',    category: 'basic' },
  WANDER:             { weight:  7, type: 'movement',    category: 'basic' },
  SPRINT_TRAVEL:      { weight:  4, type: 'movement',    category: 'basic' },
  JUMP_MOVE:          { weight:  3, type: 'movement',    category: 'basic' },
  DIAGONAL_WALK:      { weight:  5, type: 'movement',    category: 'varied' },
  ZIGZAG_MOVEMENT:    { weight:  4, type: 'movement',    category: 'varied' },
  CIRCLE_WALK:        { weight:  3, type: 'movement',    category: 'varied' },
  BACKWARDS_WALK:     { weight:  3, type: 'movement',    category: 'varied' },
  STRAFE_LEFT_RIGHT:  { weight:  4, type: 'movement',    category: 'varied' },

  LOOK_AROUND:        { weight: 10, type: 'look',        category: 'basic' },
  LOOK_SLOWLY:        { weight:  7, type: 'look',        category: 'basic' },
  LOOK_QUICK:         { weight:  4, type: 'look',        category: 'basic' },
  LOOK_UP_DOWN:       { weight:  5, type: 'look',        category: 'varied' },
  LOOK_AT_GROUND:     { weight:  3, type: 'look',        category: 'varied' },
  LOOK_AT_SKY:        { weight:  3, type: 'look',        category: 'varied' },
  SCAN_HORIZON:       { weight:  4, type: 'look',        category: 'varied' },
  QUICK_HEAD_TURN:    { weight:  3, type: 'look',        category: 'varied' },
  LOOK_BEHIND:        { weight:  3, type: 'look',        category: 'varied' },

  IDLE_SHORT:         { weight:  8, type: 'idle',        category: 'basic' },
  IDLE_MEDIUM:        { weight:  6, type: 'idle',        category: 'basic' },
  IDLE_LONG:          { weight:  4, type: 'idle',        category: 'basic' },
  IDLE_WITH_MICRO_LOOK:{ weight: 6, type: 'idle',        category: 'varied' },
  COMPLETE_STILLNESS: { weight:  5, type: 'idle',        category: 'deep' },
  AFK_SIMULATION:     { weight:  3, type: 'idle',        category: 'deep' },

  HOTBAR_SWITCH:      { weight:  5, type: 'interaction', category: 'basic' },
  SWING_ARM:          { weight:  4, type: 'interaction', category: 'basic' },
  SNEAK:              { weight:  3, type: 'interaction', category: 'basic' },
  JUMP_PLACE:         { weight:  2, type: 'interaction', category: 'basic' },
  RAPID_HOTBAR_SCROLL:{ weight:  3, type: 'interaction', category: 'varied' },
  SNEAK_WALK:         { weight:  3, type: 'interaction', category: 'varied' },
  SNEAK_LOOK:         { weight:  3, type: 'interaction', category: 'varied' },
  DOUBLE_JUMP:        { weight:  2, type: 'interaction', category: 'varied' },
  TRIPLE_JUMP:        { weight:  1, type: 'interaction', category: 'varied' },
  CROUCH_SPAM:        { weight:  2, type: 'interaction', category: 'varied' },

  LOOK_AT_BLOCK:      { weight:  4, type: 'block',       category: 'interaction' },
  APPROACH_BLOCK:     { weight:  3, type: 'block',       category: 'interaction' },
  RIGHT_CLICK_AIR:    { weight:  3, type: 'block',       category: 'interaction' },
  LEFT_CLICK_AIR:     { weight:  2, type: 'block',       category: 'interaction' },
  SWING_AT_BLOCK:     { weight:  2, type: 'block',       category: 'interaction' },

  WALK_INTO_WALL:     { weight:  2, type: 'mistake',     category: 'human' },
  WRONG_DIRECTION:    { weight:  2, type: 'mistake',     category: 'human' },
  SUDDEN_STOP:        { weight:  3, type: 'mistake',     category: 'human' },
  ACCIDENTAL_JUMP:    { weight:  2, type: 'mistake',     category: 'human' },
  HESITATION:         { weight:  3, type: 'mistake',     category: 'human' },
  OVERCORRECTION:     { weight:  2, type: 'mistake',     category: 'human' },

  REACT_TO_PLAYER:    { weight:  8, type: 'social',      category: 'player-aware' },
  LOOK_AT_PLAYER:     { weight:  6, type: 'social',      category: 'player-aware' },
  FOLLOW_PLAYER:      { weight:  3, type: 'social',      category: 'player-aware' },
  AVOID_PLAYER:       { weight:  2, type: 'social',      category: 'player-aware' },
  CURIOUS_APPROACH:   { weight:  3, type: 'social',      category: 'player-aware' },

  JUMP_SPRINT_COMBO:  { weight:  3, type: 'combo',       category: 'advanced' },
  SNEAK_JUMP_COMBO:   { weight:  2, type: 'combo',       category: 'advanced' },
  STRAFE_LOOK_COMBO:  { weight:  3, type: 'combo',       category: 'advanced' },
  WALK_LOOK_COMBO:    { weight:  4, type: 'combo',       category: 'advanced' },

  SPECTATOR_FLOAT:    { weight:  2, type: 'spectator',   category: 'mode-specific' },
  SPECTATOR_PHASE:    { weight:  1, type: 'spectator',   category: 'mode-specific' },
};

function getRandomDelay(min, max) {
  const base = min + Math.random() * (max - min);
  const variance = base * 0.3 * (Math.random() - 0.5);
  const spike = Math.random() < 0.1 ? Math.random() * 1000 : 0;
  return Math.floor(base + variance + spike);
}

function selectRandomAction() {
  const adj = {};
  for (const [k, v] of Object.entries(ACTIONS)) {
    let w = v.weight;
    if (nearbyPlayers.length > 0 && v.category === 'player-aware') w *= 3;
    if (behaviorPhase === 'idle') {
      if (v.type === 'idle')     w *= 2;
      if (v.type === 'movement') w *= 0.5;
    } else if (behaviorPhase === 'active') {
      if (v.type === 'movement') w *= 1.5;
    }
    adj[k] = w;
  }

  // 5 % chance to inject a human mistake
  if (Math.random() < 0.05) {
    const mistakes = Object.keys(ACTIONS).filter(k => ACTIONS[k].category === 'human');
    if (mistakes.length) return mistakes[Math.floor(Math.random() * mistakes.length)];
  }

  const total = Object.values(adj).reduce((s, w) => s + w, 0);
  let r = Math.random() * total;
  for (const [name, w] of Object.entries(adj)) {
    r -= w;
    if (r <= 0) return name;
  }
  return 'LOOK_AROUND';
}

// ── Safe bot guard — checks both isBotOnline AND the captured epoch ──
function botAlive(capturedEpoch) {
  return bot && isBotOnline && bot.entity && schedulerEpoch === capturedEpoch;
}

// ─────────────────────────────────────────────
// ACTION IMPLEMENTATIONS
// (Each one accepts the epoch so it can bail out mid-async)
// ─────────────────────────────────────────────
async function executeWalkShort(ep) {
  if (!botAlive(ep)) return;
  const dirs = ['forward', 'back', 'left', 'right'];
  bot.setControlState(dirs[Math.floor(Math.random() * dirs.length)], true);
  if (Math.random() < 0.2) bot.setControlState('jump', true);
  await new Promise(r => setTimeout(r, getRandomDelay(300, 1200)));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeWalkLong(ep) {
  if (!botAlive(ep)) return;
  const dirs = ['forward', 'back', 'left', 'right'];
  bot.setControlState(dirs[Math.floor(Math.random() * dirs.length)], true);
  if (Math.random() < 0.3) bot.setControlState('sprint', true);
  const dur = getRandomDelay(1500, 4000);
  const ji = setInterval(() => {
    if (bot && Math.random() < 0.15) {
      bot.setControlState('jump', true);
      setTimeout(() => bot && bot.setControlState('jump', false), 300);
    }
  }, 800);
  await new Promise(r => setTimeout(r, dur));
  clearInterval(ji);
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeWander(ep) {
  if (!botAlive(ep)) return;
  const end = Date.now() + getRandomDelay(3000, 8000);
  while (Date.now() < end && botAlive(ep)) {
    const dirs = ['forward', 'back', 'left', 'right'];
    bot.clearControlStates();
    bot.setControlState(dirs[Math.floor(Math.random() * dirs.length)], true);
    if (Math.random() < 0.4) bot.setControlState('sprint', true);
    if (Math.random() < 0.3) bot.look(Math.random() * Math.PI * 2, (Math.random() - 0.5) * Math.PI / 4, true);
    await new Promise(r => setTimeout(r, getRandomDelay(500, 2000)));
    if (botAlive(ep) && Math.random() < 0.2) {
      bot.setControlState('jump', true);
      await new Promise(r => setTimeout(r, 300));
      if (bot) bot.setControlState('jump', false);
    }
  }
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeSprintTravel(ep) {
  if (!botAlive(ep)) return;
  bot.look(Math.random() * Math.PI * 2, 0, true);
  bot.setControlState('forward', true);
  bot.setControlState('sprint', true);
  const ji = setInterval(() => bot && Math.random() < 0.25 && bot.setControlState('jump', true), 1000);
  await new Promise(r => setTimeout(r, getRandomDelay(2000, 6000)));
  clearInterval(ji);
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeJumpMove(ep) {
  if (!botAlive(ep)) return;
  if (Math.random() < 0.5) {
    const dirs = ['forward', 'back', 'left', 'right'];
    bot.setControlState(dirs[Math.floor(Math.random() * dirs.length)], true);
  }
  bot.setControlState('jump', true);
  await new Promise(r => setTimeout(r, 500));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeDiagonalWalk(ep) {
  if (!botAlive(ep)) return;
  const pairs = [['forward','left'],['forward','right'],['back','left'],['back','right']];
  const p = pairs[Math.floor(Math.random() * pairs.length)];
  p.forEach(d => bot.setControlState(d, true));
  await new Promise(r => setTimeout(r, getRandomDelay(800, 2500)));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeZigzagMovement(ep) {
  if (!botAlive(ep)) return;
  const n = 3 + Math.floor(Math.random() * 3);
  for (let i = 0; i < n && botAlive(ep); i++) {
    bot.clearControlStates();
    bot.setControlState('forward', true);
    bot.setControlState(i % 2 === 0 ? 'left' : 'right', true);
    await new Promise(r => setTimeout(r, getRandomDelay(400, 800)));
  }
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeCircleWalk(ep) {
  if (!botAlive(ep)) return;
  const end = Date.now() + getRandomDelay(3000, 6000);
  bot.setControlState('forward', true);
  while (Date.now() < end && botAlive(ep)) {
    bot.look(bot.entity.yaw + (Math.PI / 180) * 5, 0, true);
    await new Promise(r => setTimeout(r, 100));
  }
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeBackwardsWalk(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('back', true);
  await new Promise(r => setTimeout(r, getRandomDelay(1000, 3000)));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeStrafeLeftRight(ep) {
  if (!botAlive(ep)) return;
  const n = 2 + Math.floor(Math.random() * 3);
  for (let i = 0; i < n && botAlive(ep); i++) {
    bot.clearControlStates();
    bot.setControlState(i % 2 === 0 ? 'left' : 'right', true);
    await new Promise(r => setTimeout(r, getRandomDelay(500, 1200)));
  }
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeLookAround(ep) {
  if (!botAlive(ep)) return;
  const n = 1 + Math.floor(Math.random() * 3);
  for (let i = 0; i < n && botAlive(ep); i++) {
    bot.look(Math.random() * Math.PI * 2, (Math.random() - 0.5) * Math.PI / 2, true);
    await new Promise(r => setTimeout(r, getRandomDelay(300, 1000)));
  }
}

async function executeLookSlowly(ep) {
  if (!botAlive(ep)) return;
  const sy = bot.entity.yaw, sp = bot.entity.pitch;
  const ty = sy + (Math.random() - 0.5) * Math.PI;
  const tp = (Math.random() - 0.5) * Math.PI / 3;
  const steps = 5 + Math.floor(Math.random() * 5);
  for (let i = 0; i <= steps && botAlive(ep); i++) {
    const prog = i / steps;
    bot.look(sy + (ty - sy) * prog, sp + (tp - sp) * prog, true);
    await new Promise(r => setTimeout(r, getRandomDelay(50, 150)));
  }
}

async function executeLookQuick(ep) {
  if (!botAlive(ep)) return;
  bot.look(Math.random() * Math.PI * 2, (Math.random() - 0.5) * Math.PI / 4, false);
}

async function executeLookUpDown(ep) {
  if (!botAlive(ep)) return;
  const y = bot.entity.yaw;
  bot.look(y, -Math.PI / 3, true);
  await new Promise(r => setTimeout(r, getRandomDelay(500, 1200)));
  if (!botAlive(ep)) return;
  bot.look(y, Math.PI / 4, true);
  await new Promise(r => setTimeout(r, getRandomDelay(500, 1200)));
  if (botAlive(ep)) bot.look(y, 0, true);
}

async function executeLookAtGround(ep) {
  if (!botAlive(ep)) return;
  bot.look(bot.entity.yaw, Math.PI / 3, true);
  await new Promise(r => setTimeout(r, getRandomDelay(1000, 3000)));
}

async function executeLookAtSky(ep) {
  if (!botAlive(ep)) return;
  bot.look(bot.entity.yaw, -Math.PI / 2.5, true);
  await new Promise(r => setTimeout(r, getRandomDelay(1000, 3000)));
}

async function executeScanHorizon(ep) {
  if (!botAlive(ep)) return;
  const base = bot.entity.yaw, sweep = Math.PI * 0.75, steps = 8;
  for (let i = 0; i <= steps && botAlive(ep); i++) {
    bot.look(base - sweep / 2 + sweep * (i / steps), 0, true);
    await new Promise(r => setTimeout(r, getRandomDelay(200, 500)));
  }
}

async function executeQuickHeadTurn(ep) {
  if (!botAlive(ep)) return;
  bot.look(bot.entity.yaw + (Math.random() - 0.5) * Math.PI, 0, false);
  await new Promise(r => setTimeout(r, 100));
}

async function executeLookBehind(ep) {
  if (!botAlive(ep)) return;
  const y = bot.entity.yaw;
  bot.look(y + Math.PI, 0, true);
  await new Promise(r => setTimeout(r, getRandomDelay(800, 2000)));
  if (botAlive(ep)) bot.look(y, 0, true);
}

async function executeIdleShort(ep) {
  if (!botAlive(ep)) return;
  bot.clearControlStates();
  await new Promise(r => setTimeout(r, getRandomDelay(500, 2000)));
}

async function executeIdleMedium(ep) {
  if (!botAlive(ep)) return;
  bot.clearControlStates();
  const dur = getRandomDelay(2000, 5000);
  const li = setInterval(() => {
    if (bot && botAlive(ep) && Math.random() < 0.3)
      bot.look(bot.entity.yaw + (Math.random() - 0.5) * Math.PI / 4, (Math.random() - 0.5) * Math.PI / 6, true);
  }, 1000);
  await new Promise(r => setTimeout(r, dur));
  clearInterval(li);
}

async function executeIdleLong(ep) {
  if (!botAlive(ep)) return;
  bot.clearControlStates();
  await new Promise(r => setTimeout(r, getRandomDelay(5000, 12000)));
}

async function executeIdleWithMicroLook(ep) {
  if (!botAlive(ep)) return;
  bot.clearControlStates();
  const end = Date.now() + getRandomDelay(3000, 8000);
  while (Date.now() < end && botAlive(ep)) {
    if (Math.random() < 0.1)
      bot.look(bot.entity.yaw + (Math.random() - 0.5) * 0.1, bot.entity.pitch + (Math.random() - 0.5) * 0.1, true);
    await new Promise(r => setTimeout(r, 500));
  }
}

async function executeCompleteStillness(ep) {
  if (!botAlive(ep)) return;
  bot.clearControlStates();
  await new Promise(r => setTimeout(r, getRandomDelay(20000, 40000)));
}

async function executeAfkSimulation(ep) {
  if (!botAlive(ep)) return;
  bot.clearControlStates();
  const dur = getRandomDelay(30000, 60000);
  console.log(`🎭 AFK simulation for ${Math.floor(dur / 1000)}s`);
  await new Promise(r => setTimeout(r, dur));
}

async function executeHotbarSwitch(ep) {
  if (!botAlive(ep)) return;
  try {
    const n = 1 + Math.floor(Math.random() * 3);
    for (let i = 0; i < n && botAlive(ep); i++) {
      bot.setQuickBarSlot(Math.floor(Math.random() * 9));
      await new Promise(r => setTimeout(r, getRandomDelay(100, 500)));
    }
  } catch { /* ignore */ }
}

async function executeSwingArm(ep) {
  if (!botAlive(ep)) return;
  const n = 1 + Math.floor(Math.random() * 3);
  for (let i = 0; i < n && botAlive(ep); i++) {
    bot.swingArm('right');
    await new Promise(r => setTimeout(r, getRandomDelay(100, 400)));
  }
  if (botAlive(ep)) movementCount++;
}

async function executeSneak(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('sneak', true);
  if (Math.random() < 0.4) {
    const dirs = ['forward', 'back', 'left', 'right'];
    bot.setControlState(dirs[Math.floor(Math.random() * dirs.length)], true);
  }
  await new Promise(r => setTimeout(r, getRandomDelay(500, 2500)));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeJumpPlace(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('jump', true);
  bot.swingArm('right');
  await new Promise(r => setTimeout(r, 500));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeRapidHotbarScroll(ep) {
  if (!botAlive(ep)) return;
  try {
    for (let i = 0; i < 9 && botAlive(ep); i++) {
      bot.setQuickBarSlot(i);
      await new Promise(r => setTimeout(r, getRandomDelay(50, 150)));
    }
  } catch { /* ignore */ }
}

async function executeSneakWalk(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('sneak', true);
  bot.setControlState('forward', true);
  await new Promise(r => setTimeout(r, getRandomDelay(2000, 5000)));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeSneakLook(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('sneak', true);
  const n = 2 + Math.floor(Math.random() * 3);
  for (let i = 0; i < n && botAlive(ep); i++) {
    bot.look(Math.random() * Math.PI * 2, (Math.random() - 0.5) * Math.PI / 3, true);
    await new Promise(r => setTimeout(r, getRandomDelay(500, 1200)));
  }
  if (bot) bot.clearControlStates();
}

async function executeDoubleJump(ep) {
  if (!botAlive(ep)) return;
  for (let i = 0; i < 2 && botAlive(ep); i++) {
    bot.setControlState('jump', true);
    await new Promise(r => setTimeout(r, 300));
    bot.setControlState('jump', false);
    await new Promise(r => setTimeout(r, 200));
  }
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeTripleJump(ep) {
  if (!botAlive(ep)) return;
  for (let i = 0; i < 3 && botAlive(ep); i++) {
    bot.setControlState('jump', true);
    await new Promise(r => setTimeout(r, 300));
    bot.setControlState('jump', false);
    await new Promise(r => setTimeout(r, 200));
  }
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeCrouchSpam(ep) {
  if (!botAlive(ep)) return;
  const n = 3 + Math.floor(Math.random() * 5);
  for (let i = 0; i < n && botAlive(ep); i++) {
    bot.setControlState('sneak', true);
    await new Promise(r => setTimeout(r, 150));
    bot.setControlState('sneak', false);
    await new Promise(r => setTimeout(r, 150));
  }
  if (bot) bot.clearControlStates();
}

async function executeLookAtBlock(ep) {
  if (!botAlive(ep)) return;
  try {
    const p = bot.entity.position;
    const t = p.offset(Math.floor(Math.random() * 10) - 5, Math.floor(Math.random() * 3) - 1, Math.floor(Math.random() * 10) - 5);
    bot.look(Math.atan2(-(t.x - p.x), t.z - p.z), Math.atan2(t.y - p.y, p.distanceTo(t)), true);
    await new Promise(r => setTimeout(r, getRandomDelay(1000, 3000)));
  } catch { /* ignore */ }
}

async function executeApproachBlock(ep) {
  if (!botAlive(ep)) return;
  try {
    const p = bot.entity.position;
    const t = p.offset(Math.floor(Math.random() * 5) - 2, 0, Math.floor(Math.random() * 5) - 2);
    bot.look(Math.atan2(-(t.x - p.x), t.z - p.z), 0, true);
    bot.setControlState('forward', true);
    await new Promise(r => setTimeout(r, getRandomDelay(1000, 2500)));
    if (bot) bot.clearControlStates();
    if (botAlive(ep)) movementCount++;
  } catch { if (bot) bot.clearControlStates(); }
}

async function executeRightClickAir(ep) {
  if (!botAlive(ep)) return;
  try { bot.activateItem(); } catch { /* ignore */ }
  await new Promise(r => setTimeout(r, 300));
}

async function executeLeftClickAir(ep) {
  if (!botAlive(ep)) return;
  bot.swingArm('right');
  await new Promise(r => setTimeout(r, 200));
  if (botAlive(ep)) movementCount++;
}

async function executeSwingAtBlock(ep) {
  if (!botAlive(ep)) return;
  const n = 2 + Math.floor(Math.random() * 4);
  for (let i = 0; i < n && botAlive(ep); i++) {
    bot.swingArm('right');
    await new Promise(r => setTimeout(r, getRandomDelay(200, 500)));
  }
  if (botAlive(ep)) movementCount++;
}

// ── Human mistakes ──
async function executeWalkIntoWall(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('forward', true);
  await new Promise(r => setTimeout(r, getRandomDelay(1000, 2500)));
  if (bot) bot.clearControlStates();
  await new Promise(r => setTimeout(r, getRandomDelay(500, 1500)));
  if (botAlive(ep)) { movementCount++; mistakeCounter++; }
}

async function executeWrongDirection(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('forward', true);
  await new Promise(r => setTimeout(r, getRandomDelay(500, 1000)));
  if (!botAlive(ep)) return;
  bot.clearControlStates();
  bot.look(bot.entity.yaw + Math.PI, 0, false);
  bot.setControlState('forward', true);
  await new Promise(r => setTimeout(r, getRandomDelay(800, 1500)));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) { movementCount++; mistakeCounter++; }
}

async function executeSuddenStop(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('forward', true);
  bot.setControlState('sprint', true);
  await new Promise(r => setTimeout(r, getRandomDelay(1000, 2000)));
  if (bot) bot.clearControlStates();
  await new Promise(r => setTimeout(r, getRandomDelay(1000, 3000)));
  if (botAlive(ep)) { movementCount++; mistakeCounter++; }
}

async function executeAccidentalJump(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('jump', true);
  await new Promise(r => setTimeout(r, 300));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) mistakeCounter++;
}

async function executeHesitation(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('forward', true);
  await new Promise(r => setTimeout(r, getRandomDelay(300, 700)));
  if (bot) bot.clearControlStates();
  await new Promise(r => setTimeout(r, getRandomDelay(500, 1200)));
  if (!botAlive(ep)) return;
  bot.setControlState('forward', true);
  await new Promise(r => setTimeout(r, getRandomDelay(500, 1000)));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) { movementCount++; mistakeCounter++; }
}

async function executeOvercorrection(ep) {
  if (!botAlive(ep)) return;
  const y = bot.entity.yaw;
  bot.look(y + Math.PI / 2, 0, true);
  await new Promise(r => setTimeout(r, 300));
  if (!botAlive(ep)) return;
  bot.look(y - Math.PI / 6, 0, true);
  await new Promise(r => setTimeout(r, 300));
  if (botAlive(ep)) { bot.look(y, 0, true); mistakeCounter++; }
}

// ── Player-aware ──
async function executeReactToPlayer(ep) {
  if (!botAlive(ep) || !nearbyPlayers.length) return;
  bot.clearControlStates();
  await new Promise(r => setTimeout(r, getRandomDelay(500, 1500)));
  if (!botAlive(ep)) return;
  const pl = nearbyPlayers[0];
  bot.look(Math.atan2(-(pl.position.x - bot.entity.position.x), pl.position.z - bot.entity.position.z), 0, true);
  await new Promise(r => setTimeout(r, getRandomDelay(1000, 3000)));
}

async function executeLookAtPlayer(ep) {
  if (!botAlive(ep) || !nearbyPlayers.length) return;
  const pl = nearbyPlayers[0];
  const bp = bot.entity.position;
  const dist = bp.distanceTo(pl.position);
  bot.look(Math.atan2(-(pl.position.x - bp.x), pl.position.z - bp.z), Math.atan2(pl.position.y - bp.y, dist), true);
  await new Promise(r => setTimeout(r, getRandomDelay(2000, 5000)));
}

async function executeFollowPlayer(ep) {
  if (!botAlive(ep) || !nearbyPlayers.length) return;
  const pl = nearbyPlayers[0];
  const end = Date.now() + getRandomDelay(3000, 8000);
  while (Date.now() < end && botAlive(ep)) {
    bot.look(Math.atan2(-(pl.position.x - bot.entity.position.x), pl.position.z - bot.entity.position.z), 0, true);
    bot.setControlState('forward', true);
    await new Promise(r => setTimeout(r, 500));
  }
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeAvoidPlayer(ep) {
  if (!botAlive(ep) || !nearbyPlayers.length) return;
  const pl = nearbyPlayers[0];
  bot.look(Math.atan2(-(pl.position.x - bot.entity.position.x), pl.position.z - bot.entity.position.z) + Math.PI, 0, true);
  bot.setControlState('forward', true);
  await new Promise(r => setTimeout(r, getRandomDelay(2000, 4000)));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeCuriousApproach(ep) {
  if (!botAlive(ep) || !nearbyPlayers.length) return;
  bot.clearControlStates();
  const pl = nearbyPlayers[0];
  bot.look(Math.atan2(-(pl.position.x - bot.entity.position.x), pl.position.z - bot.entity.position.z), 0, true);
  await new Promise(r => setTimeout(r, getRandomDelay(1000, 2000)));
  if (!botAlive(ep)) return;
  bot.setControlState('sneak', true);
  bot.setControlState('forward', true);
  await new Promise(r => setTimeout(r, getRandomDelay(2000, 4000)));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

// ── Combos ──
async function executeJumpSprintCombo(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('forward', true);
  bot.setControlState('sprint', true);
  const end = Date.now() + getRandomDelay(2000, 4000);
  while (Date.now() < end && botAlive(ep)) {
    if (Math.random() < 0.3) {
      bot.setControlState('jump', true);
      await new Promise(r => setTimeout(r, 300));
      bot.setControlState('jump', false);
    }
    await new Promise(r => setTimeout(r, 500));
  }
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeSneakJumpCombo(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('sneak', true);
  bot.setControlState('forward', true);
  await new Promise(r => setTimeout(r, getRandomDelay(1000, 2000)));
  if (botAlive(ep)) { bot.setControlState('jump', true); await new Promise(r => setTimeout(r, 300)); }
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeStrafeLookCombo(ep) {
  if (!botAlive(ep)) return;
  const end = Date.now() + getRandomDelay(2000, 4000);
  while (Date.now() < end && botAlive(ep)) {
    bot.clearControlStates();
    bot.setControlState(Math.random() < 0.5 ? 'left' : 'right', true);
    bot.look(Math.random() * Math.PI * 2, 0, true);
    await new Promise(r => setTimeout(r, getRandomDelay(500, 1200)));
  }
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeWalkLookCombo(ep) {
  if (!botAlive(ep)) return;
  bot.setControlState('forward', true);
  const end = Date.now() + getRandomDelay(3000, 6000);
  while (Date.now() < end && botAlive(ep)) {
    if (Math.random() < 0.4)
      bot.look(Math.random() * Math.PI * 2, (Math.random() - 0.5) * Math.PI / 4, true);
    await new Promise(r => setTimeout(r, getRandomDelay(800, 1500)));
  }
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

// ── Spectator ──
async function executeSpectatorFloat(ep) {
  if (!botAlive(ep) || !isInSpectatorMode) return;
  bot.look(bot.entity.yaw, -Math.PI / 4, true);
  bot.setControlState('forward', true);
  await new Promise(r => setTimeout(r, getRandomDelay(2000, 4000)));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

async function executeSpectatorPhase(ep) {
  if (!botAlive(ep) || !isInSpectatorMode) return;
  bot.look(Math.random() * Math.PI * 2, 0, true);
  bot.setControlState('forward', true);
  await new Promise(r => setTimeout(r, getRandomDelay(1500, 3000)));
  if (bot) bot.clearControlStates();
  if (botAlive(ep)) movementCount++;
}

// ─────────────────────────────────────────────
// ACTION DISPATCHER
// ─────────────────────────────────────────────
async function executeAction(name, ep) {
  if (!botAlive(ep)) return;
  try {
    const map = {
      WALK_SHORT:         executeWalkShort,
      WALK_LONG:          executeWalkLong,
      WANDER:             executeWander,
      SPRINT_TRAVEL:      executeSprintTravel,
      JUMP_MOVE:          executeJumpMove,
      DIAGONAL_WALK:      executeDiagonalWalk,
      ZIGZAG_MOVEMENT:    executeZigzagMovement,
      CIRCLE_WALK:        executeCircleWalk,
      BACKWARDS_WALK:     executeBackwardsWalk,
      STRAFE_LEFT_RIGHT:  executeStrafeLeftRight,
      LOOK_AROUND:        executeLookAround,
      LOOK_SLOWLY:        executeLookSlowly,
      LOOK_QUICK:         executeLookQuick,
      LOOK_UP_DOWN:       executeLookUpDown,
      LOOK_AT_GROUND:     executeLookAtGround,
      LOOK_AT_SKY:        executeLookAtSky,
      SCAN_HORIZON:       executeScanHorizon,
      QUICK_HEAD_TURN:    executeQuickHeadTurn,
      LOOK_BEHIND:        executeLookBehind,
      IDLE_SHORT:         executeIdleShort,
      IDLE_MEDIUM:        executeIdleMedium,
      IDLE_LONG:          executeIdleLong,
      IDLE_WITH_MICRO_LOOK: executeIdleWithMicroLook,
      COMPLETE_STILLNESS: executeCompleteStillness,
      AFK_SIMULATION:     executeAfkSimulation,
      HOTBAR_SWITCH:      executeHotbarSwitch,
      SWING_ARM:          executeSwingArm,
      SNEAK:              executeSneak,
      JUMP_PLACE:         executeJumpPlace,
      RAPID_HOTBAR_SCROLL: executeRapidHotbarScroll,
      SNEAK_WALK:         executeSneakWalk,
      SNEAK_LOOK:         executeSneakLook,
      DOUBLE_JUMP:        executeDoubleJump,
      TRIPLE_JUMP:        executeTripleJump,
      CROUCH_SPAM:        executeCrouchSpam,
      LOOK_AT_BLOCK:      executeLookAtBlock,
      APPROACH_BLOCK:     executeApproachBlock,
      RIGHT_CLICK_AIR:    executeRightClickAir,
      LEFT_CLICK_AIR:     executeLeftClickAir,
      SWING_AT_BLOCK:     executeSwingAtBlock,
      WALK_INTO_WALL:     executeWalkIntoWall,
      WRONG_DIRECTION:    executeWrongDirection,
      SUDDEN_STOP:        executeSuddenStop,
      ACCIDENTAL_JUMP:    executeAccidentalJump,
      HESITATION:         executeHesitation,
      OVERCORRECTION:     executeOvercorrection,
      REACT_TO_PLAYER:    executeReactToPlayer,
      LOOK_AT_PLAYER:     executeLookAtPlayer,
      FOLLOW_PLAYER:      executeFollowPlayer,
      AVOID_PLAYER:       executeAvoidPlayer,
      CURIOUS_APPROACH:   executeCuriousApproach,
      JUMP_SPRINT_COMBO:  executeJumpSprintCombo,
      SNEAK_JUMP_COMBO:   executeSneakJumpCombo,
      STRAFE_LOOK_COMBO:  executeStrafeLookCombo,
      WALK_LOOK_COMBO:    executeWalkLookCombo,
      SPECTATOR_FLOAT:    executeSpectatorFloat,
      SPECTATOR_PHASE:    executeSpectatorPhase,
    };
    const fn = map[name];
    if (fn) await fn(ep);
    else console.warn(`⚠️  Unknown action: ${name}`);
  } catch (err) {
    // Don't crash the scheduler on action errors
    if (bot) try { bot.clearControlStates(); } catch { /* ignore */ }
  }
}

// ─────────────────────────────────────────────
// SCHEDULER  (epoch-gated — no ghost actions)
// ─────────────────────────────────────────────
function scheduleNextAction(capturedEpoch) {
  // If epoch changed (disconnect/reconnect happened), this chain is dead
  if (schedulerEpoch !== capturedEpoch) return;
  if (!bot || !isBotOnline || isShuttingDown) return;

  checkNearbyPlayers();
  updateBehaviorPhase();
  updateSpectatorMode();

  let minD, maxD;
  switch (behaviorPhase) {
    case 'active':   minD = 500;  maxD = 4000;  break;
    case 'moderate': minD = 2000; maxD = 8000;  break;
    default:         minD = 5000; maxD = 15000; break;
  }
  if (nearbyPlayers.length > 0) { minD = Math.max(500, minD * 0.7); maxD = Math.max(2000, maxD * 0.7); }

  actionSchedulerTimeout = setTimeout(async () => {
    if (schedulerEpoch !== capturedEpoch) return;   // ← epoch check BEFORE action
    if (!bot || !isBotOnline) return;

    const action = selectRandomAction();
    if (Math.random() < 0.05)
      console.log(`🎮 [${behaviorPhase}] ${action} | nearby:${nearbyPlayers.length} | mistakes:${mistakeCounter}`);

    await executeAction(action, capturedEpoch);

    scheduleNextAction(capturedEpoch);              // continue only if epoch still valid
  }, getRandomDelay(minD, maxD));
}

function setupIntervals() {
  console.log('🎮 Starting scheduler (40+ actions, epoch-gated)…');
  const ep = schedulerEpoch;   // capture current epoch for this chain
  scheduleNextAction(ep);

  activityIntervalHandle = setInterval(() => {
    checkBotActivity();
    checkPlayerCount();
    checkNearbyPlayers();
  }, ACTIVITY_CHECK_INTERVAL);

  setTimeout(checkPlayerCount, 3000);
}

function checkBotActivity() {
  if (!botStartTime || !isBotOnline || !ANTI_AFK) return;
  if (Date.now() - botStartTime >= ONE_HOUR) {
    sendDiscordEmbed('Anti-AFK', 'Active > 1 hour — rejoining', WARNING_EMBED_COLOR);
    forceRejoinBot();
  }
}

// ─────────────────────────────────────────────
// BOT LIFECYCLE
// ─────────────────────────────────────────────
async function startBot() {
  if (isShuttingDown) return;

  clearAllTimers();
  schedulerEpoch++;   // invalidate any lingering scheduler chains

  if (bot) {
    bot.removeAllListeners();
    try { bot.quit(); } catch { /* ignore */ }
    bot = null;
  }

  resetBotState();

  // ── Pre-connection reachability check ──
  console.log(`🔍 Checking if ${BOT_HOST}:${BOT_PORT} is reachable…`);
  const reachable = await isServerReachable(BOT_HOST, BOT_PORT, 6000);
  if (!reachable) {
    consecutiveFailures++;
    const retryDelay = Math.min(RECONNECT_DELAY * Math.pow(2, Math.min(consecutiveFailures, 6)), 300000);
    console.log(`🔴 Server is offline/unreachable. Retry in ${retryDelay / 1000}s (attempt ${consecutiveFailures})`);
    reconnectTimeout = setTimeout(startBot, retryDelay);
    return;   // Don't create a mineflayer bot at all
  }

  console.log(`✅ Server reachable — connecting as ${BOT_USERNAME} (v${BOT_VERSION})…`);

  bot = mineflayer.createBot({
    host: BOT_HOST,
    port: BOT_PORT,
    username: BOT_USERNAME,
    version: BOT_VERSION,
    connectTimeout: 30000,   // was null — now 30 s
  });

  bot.once('spawn', () => {
    isBotOnline  = true;
    botStartTime = Date.now();
    lastOnlineTime = Date.now();
    consecutiveFailures = 0;
    console.log(`✅ Bot spawned on ${BOT_HOST}:${BOT_PORT}`);
    sendDiscordEmbed('Bot Connected', `${BOT_USERNAME} joined (v${BOT_VERSION})`, SUCCESS_EMBED_COLOR);

    if (bot._client?.socket) bot._client.socket.setKeepAlive(true, 30000);

    if (bot._client) {
      bot._client.on('player_info', packet => {
        for (const p of packet.data) {
          if (p.uuid === bot.uuid) {
            const gmap = { 0: 'Survival', 1: 'Creative', 2: 'Adventure', 3: 'Spectator' };
            bot.game = bot.game || {};
            bot.game.gameMode = gmap[p.gamemode] || 'Unknown';
            updateSpectatorMode();
          }
        }
      });
    }

    setTimeout(setupIntervals, 1500);
  });

  bot.on('error', err => {
    const msg = err.message || '';
    console.error('❌ Bot Error:', msg);
    // Don't log "fake" success after a connection error
    if (isBotOnline) sendDiscordEmbed('Bot Error', msg, ERROR_EMBED_COLOR);

    if (msg.includes('ETIMEDOUT') || msg.includes('ECONNRESET') ||
        msg.includes('ECONNREFUSED') || err.name === 'PartialReadError' ||
        msg.includes('Unexpected buffer end') || msg.includes('timed out')) {
      resetBotState();
      clearAllTimers();
      schedulerEpoch++;
      consecutiveFailures++;
      if (AUTO_REJOIN) scheduleReconnect();
    }
  });

  bot.on('end', async reason => {
    console.log('🔌 Bot disconnected:', reason);
    await ensureTimeUnfrozen();
    const wasOnline = isBotOnline;
    resetBotState();
    clearAllTimers();
    schedulerEpoch++;
    consecutiveFailures++;
    if (wasOnline)
      sendDiscordEmbed('Bot Disconnected', `Reason: ${reason}`, WARNING_EMBED_COLOR);
    if (AUTO_REJOIN && !isShuttingDown) scheduleReconnect();
  });

  bot.on('kicked', async reason => {
    const rs = typeof reason === 'string' ? reason : JSON.stringify(reason);
    console.log('⛔ Kicked:', rs);
    await sendDiscordEmbed('Bot Kicked', rs, ERROR_EMBED_COLOR);
    await ensureTimeUnfrozen();
    resetBotState();
    clearAllTimers();
    schedulerEpoch++;
    consecutiveFailures++;

    if (AUTO_REJOIN && !isShuttingDown) {
      const isAfk = /idle|afk|terms/i.test(rs);
      const delay = isAfk ? 30000 : Math.min(RECONNECT_DELAY * Math.pow(2, Math.min(consecutiveFailures, 6)), 300000);
      console.log(`⏳ Rejoin after kick in ${delay / 1000}s`);
      reconnectTimeout = setTimeout(startBot, delay);
    }
  });

  bot.on('chat', async (username, message) => {
    if (username === BOT_USERNAME) return;

    // Find true username + uuid from player list
    let trueUsername = username, uuid = null;
    if (bot?.players) {
      const p = Object.values(bot.players).find(p => p.username.replace(/^\./, '') === username.replace(/^\./, ''));
      if (p) { trueUsername = p.username; uuid = p.uuid; }
    }

    sendPlayerMessage(trueUsername, message);

    try {
      const skinUrl   = await getOrCreatePlayerFace(trueUsername, uuid);
      const chatMsg   = await new MinecraftChat({ username: trueUsername, chat: message }).save();
      io.emit('chatMessage', { username: trueUsername, chat: message, timestamp: chatMsg.timestamp, skinUrl });
    } catch (err) { console.error('❌ Chat save error:', err.message); }
  });

  bot.on('playerJoined', async player => {
    if (player.username === BOT_USERNAME) return;
    console.log(`👋 ${player.username} joined`);
    const skinUrl = await getOrCreatePlayerFace(player.username, player.uuid);
    player.skinUrl = skinUrl;
    if (CHAT_WEBHOOK) axios.post(CHAT_WEBHOOK, { content: `📥 **${player.username}** joined.` }).catch(() => {});
    setTimeout(checkPlayerCount, 1000);
    setTimeout(checkNearbyPlayers, 2000);
  });

  bot.on('playerLeft', player => {
    if (player.username === BOT_USERNAME) return;
    console.log(`👋 ${player.username} left`);
    if (CHAT_WEBHOOK) axios.post(CHAT_WEBHOOK, { content: `📤 **${player.username}** left.` }).catch(() => {});
    setTimeout(checkPlayerCount, 1000);
    setTimeout(checkNearbyPlayers, 2000);
  });
}

// ─────────────────────────────────────────────
// RECONNECT HELPERS
// ─────────────────────────────────────────────
function scheduleReconnect() {
  if (isShuttingDown) return;
  const delay = Math.min(RECONNECT_DELAY * Math.pow(2, Math.min(consecutiveFailures, 6)), 300000);
  console.log(`⏳ Reconnecting in ${delay / 1000}s (attempt ${consecutiveFailures})`);
  reconnectTimeout = setTimeout(startBot, delay);
}

function forceRejoinBot() {
  if (isShuttingDown) return;
  clearAllTimers();
  console.log(`⏳ Force-rejoining in ${FIFTEEN_SECONDS / 1000}s`);
  forceRejoinTimeoutHandle = setTimeout(startBot, FIFTEEN_SECONDS);  // fixed: own handle, not activityIntervalHandle
}

// ─────────────────────────────────────────────
// STATUS PAYLOAD
// ─────────────────────────────────────────────
async function getBotStatusPayload() {
  const botActive = isBotOnline && bot && bot.entity;
  let onlinePlayersCount = 0, playerDetails = [];

  if (botActive) {
    const players = getOnlinePlayersExcludingBot();
    onlinePlayersCount = players.length;
    playerDetails = await Promise.all(players.map(async p => ({
      username: p.username,
      uuid: p.uuid,
      skinUrl: await getOrCreatePlayerFace(p.username, p.uuid),
    })));
  }

  let diskInfo = { free: 0, total: 0 };
  try {
    diskInfo = await diskusage.check(os.platform() === 'win32' ? 'C:' : '/');
  } catch { /* suppress */ }

  return {
    message:            botActive ? 'Bot is running!' : 'Bot is offline',
    onlinePlayersCount: botActive ? onlinePlayersCount : 0,
    playerDetails:      botActive ? playerDetails : [],

    gameMode:           botActive && bot.game ? bot.game.gameMode : 'N/A',
    position:           botActive ? {
      x: Math.floor(bot.entity.position.x),
      y: Math.floor(bot.entity.position.y),
      z: Math.floor(bot.entity.position.z),
    } : 'N/A',

    uptime:      botActive && botStartTime ? Math.floor((Date.now() - botStartTime) / 1000) : 0,
    movements:   botActive ? movementCount : 0,
    memoryUsage: `${(process.memoryUsage().rss / 1048576).toFixed(2)} MB`,

    lastOnline:  lastOnlineTime || null,
    serverHost:  BOT_HOST,
    serverPort:  BOT_PORT,
    botName:     BOT_USERNAME,

    botHealth:   botActive && bot.health  != null ? `${Math.round(bot.health)}/20`  : 'N/A',
    botFood:     botActive && bot.food    != null ? `${Math.round(bot.food)}/20`    : 'N/A',
    botLatency:  botActive && bot.player?.ping != null ? `${bot.player.ping}ms`     : 'N/A',

    serverLoad:  os.loadavg()[0].toFixed(2),
    cpuUsage:    getCpuUsage().toFixed(2),
    diskFree:    diskInfo.total > 0 ? `${(diskInfo.free  / 1073741824).toFixed(2)} GB` : 'N/A',
    diskTotal:   diskInfo.total > 0 ? `${(diskInfo.total / 1073741824).toFixed(2)} GB` : 'N/A',

    minecraftDay:        botActive && bot.time ? bot.time.day       : 'N/A',
    minecraftTime:       botActive && bot.time ? bot.time.timeOfDay : 'N/A',
    serverDifficulty:    botActive && bot.game ? bot.game.difficulty : 'N/A',
    timeFrozen:          isTimeFrozen,
    version:             BOT_VERSION,
    behaviorPhase,
    schedulerEpoch,
  };
}

// ─────────────────────────────────────────────
// REST API
// ─────────────────────────────────────────────
app.get('/api/status', async (req, res) => {
  try { res.json(await getBotStatusPayload()); }
  catch (err) { console.error('❌ /api/status:', err.message); res.status(500).json({ error: 'Internal Server Error' }); }
});

app.get('/api/chat', async (req, res) => {
  try {
    const { username, date, search } = req.query;
    const query = {};
    if (username) query.username = username;
    if (date) {
      const s = new Date(date); s.setHours(0, 0, 0, 0);
      const e = new Date(date); e.setHours(23, 59, 59, 999);
      query.timestamp = { $gte: s, $lte: e };
    }
    if (search) query.chat = { $regex: search, $options: 'i' };

    const skip    = parseInt(req.query.skip)  || 0;
    const limit   = parseInt(req.query.limit) || 100;
    const msgs    = await MinecraftChat.find(query).sort({ timestamp: -1 }).skip(skip).limit(limit);
    const withFaces = await Promise.all(msgs.map(async m => ({
      ...m.toObject(),
      skinUrl: await getOrCreatePlayerFace(m.username, null),
    })));
    res.json(withFaces);
  } catch (err) { console.error('❌ /api/chat:', err.message); res.status(500).json({ error: 'Internal Server Error' }); }
});

app.get('/api/chat/usernames', async (req, res) => {
  try { res.json(await MinecraftChat.distinct('username')); }
  catch (err) { console.error('❌ /api/chat/usernames:', err.message); res.status(500).json({ error: 'Internal Server Error' }); }
});

app.get('/', (req, res) => res.sendFile(path.join(__dirname, 'public', 'dashboard.html')));

// ─────────────────────────────────────────────
// SOCKET.IO — status broadcast
// ─────────────────────────────────────────────
io.on('connection', socket => {
  console.log('🔌 Dashboard client connected');
});

setInterval(async () => {
  try { io.emit('botStatusUpdate', await getBotStatusPayload()); }
  catch (err) { console.error('❌ Socket.IO emit error:', err.message); }
}, SOCKET_IO_UPDATE_INTERVAL);

// ─────────────────────────────────────────────
// WEB SERVER
// ─────────────────────────────────────────────
server.listen(WEB_SERVER_PORT, () => {
  console.log(`🌐 Dashboard running on port ${WEB_SERVER_PORT}`);
  sendDiscordEmbed('Web Server', `Started on port ${WEB_SERVER_PORT}`, DEFAULT_EMBED_COLOR);
});

// ─────────────────────────────────────────────
// GRACEFUL SHUTDOWN
// ─────────────────────────────────────────────
async function gracefulShutdown(sig) {
  console.log(`\n⚠️  ${sig} received — shutting down…`);
  isShuttingDown = true;
  schedulerEpoch++;
  await ensureTimeUnfrozen();
  if (bot) {
    await sendDiscordEmbed('Bot Shutdown', 'Shutting down gracefully', WARNING_EMBED_COLOR);
    try { bot.quit(); } catch { /* ignore */ }
  }
  clearAllTimers();
  setTimeout(() => { console.log('✅ Shutdown complete'); process.exit(0); }, 2000);
}

process.on('SIGINT',  () => gracefulShutdown('SIGINT'));
process.on('SIGTERM', () => gracefulShutdown('SIGTERM'));

// ─────────────────────────────────────────────
// START
// ─────────────────────────────────────────────
startBot();
