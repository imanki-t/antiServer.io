'use strict';

const mineflayer = require('mineflayer');
const axios = require('axios');
const Vec3 = require('vec3');
const express = require('express');
const path = require('path');
const os = require('os');
const http = require('http');
const { Server } = require('socket.io');
const mongoose = require('mongoose');
const diskusage = require('diskusage');
const fs = require('fs');

// ============================================================================
// 🔧 CONFIGURATION LOADER
// ============================================================================
let config;
try {
  const configPath = path.join(__dirname, 'config.json');
  config = JSON.parse(fs.readFileSync(configPath, 'utf8'));
} catch (err) {
  console.error('❌ Failed to load config.json:', err.message);
  process.exit(1);
}

// Extract configuration with env overrides
const BOT_HOST        = process.env.BOT_HOST     || config.bot.host;
const BOT_PORT        = parseInt(process.env.BOT_PORT, 10) || config.bot.port;
const BOT_USERNAME    = process.env.BOT_USERNAME  || config.bot.username;
const BOT_VERSION     = process.env.BOT_VERSION   || config.bot.version;

const DISCORD_WEBHOOK = process.env.DISCORD_WEBHOOK || config.webhooks.discord;
const CHAT_WEBHOOK    = process.env.CHAT_WEBHOOK    || config.webhooks.chat;
const MESSAGE_WEBHOOK = process.env.MESSAGE_WEBHOOK || config.webhooks.message;

const WEB_SERVER_PORT = parseInt(process.env.PORT, 10) || config.server.port;
const MONGO_URI       = process.env.MONGO_URI || config.database.mongoUri;

// Reconnect delays: 3s → 5s → 10s (capped)
const RECONNECT_DELAYS    = config.intervals.reconnectDelays || [3000, 5000, 10000];
const SOCKET_UPDATE_MS    = config.intervals.socketUpdate    || 1000;
const ACTIVITY_CHECK_MS   = config.intervals.activityCheck   || 5000;
const KEEP_ALIVE_MS       = config.intervals.keepAlive       || 840000; // 14 min

const ONE_HOUR            = config.timeLimits.oneHour        || 3600000;
const SPAWN_TIMEOUT_MS    = config.timeLimits.spawnTimeout   || 30000;

const DEFAULT_COLOR  = config.embedColors.default;
const SUCCESS_COLOR  = config.embedColors.success;
const WARNING_COLOR  = config.embedColors.warning;
const ERROR_COLOR    = config.embedColors.error;
const INFO_COLOR     = config.embedColors.info;
const CHAT_COLOR     = config.embedColors.chat;

const FACES = config.faces;

const AUTO_TIME_FREEZE = config.features.autoTimeFreeze;
const ANTI_AFK         = config.features.antiAFK;
const AUTO_REJOIN      = config.features.autoRejoin;
const SELF_PING        = config.features.selfPing;
const SPECTATOR_ONLY   = config.features.spectatorOnly;

// ============================================================================
// 🌐 EXPRESS + SOCKET.IO SETUP
// ============================================================================
const app    = express();
const server = http.createServer(app);
const io     = new Server(server, {
  cors: { origin: '*' },
  pingTimeout: 60000,
  pingInterval: 25000,
});

app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

// ============================================================================
// 🗄️ MONGODB SETUP (optional — skip gracefully if no URI)
// ============================================================================
let dbConnected = false;
let MinecraftChat = null;
let PlayerFace = null;

async function connectDatabase() {
  if (!MONGO_URI) {
    console.log('⚠️  No MONGO_URI set — database features disabled');
    return;
  }
  try {
    await mongoose.connect(MONGO_URI, {
      serverSelectionTimeoutMS: 10000,
      socketTimeoutMS: 45000,
    });
    console.log('✅ MongoDB connected');
    dbConnected = true;

    const chatSchema = new mongoose.Schema({
      username:  String,
      chat:      String,
      timestamp: { type: Date, default: Date.now },
    });
    MinecraftChat = mongoose.model('MinecraftChat', chatSchema);

    const playerFaceSchema = new mongoose.Schema({
      username:    { type: String, unique: true },
      face:        String,
      isCustom:    { type: Boolean, default: false },
      lastUpdated: { type: Date, default: Date.now },
    });
    PlayerFace = mongoose.model('PlayerFace', playerFaceSchema);
  } catch (err) {
    console.error('❌ MongoDB connection error:', err.message);
    console.log('⚠️  Continuing without database...');
  }
}

// ============================================================================
// 📊 BOT STATE
// ============================================================================
let bot                = null;
let botReady           = false;  // true ONLY when bot is spawned and confirmed alive
let isBotOnline        = false;
let isInSpectatorMode  = false;
let isTimeFrozen       = false;
let isShuttingDown     = false;
let botStartTime       = null;
let lastOnlineTime     = null;
let movementCount      = 0;
let consecutiveFailures = 0;
let otherPlayersOnline = 0;
let mistakeCounter     = 0;
let spawnTimeoutHandle = null;

// Nearby players cache
let nearbyPlayers      = [];
let lastPlayerCheckMs  = 0;

// Behavior phase: 'active' | 'moderate' | 'idle'
let behaviorPhase      = 'active';

// Scheduler handles
let actionSchedulerHandle  = null;
let activityCheckHandle    = null;
let reconnectHandle        = null;
let heartbeatHandle        = null;

// Action guard — prevents ghost actions
let actionInProgress   = false;
let currentAction      = null;

// CPU tracking
let lastCpuSnapshot    = { idle: 0, total: 0 };

// Face index for dot-usernames
let nextDotFaceIndex   = 0;

// Current server info (for display)
let currentServerHost  = BOT_HOST;
let currentServerPort  = BOT_PORT;

// ============================================================================
// 🛡️ SAFETY GUARD — the single source of truth for "can we act?"
// ============================================================================
function canAct() {
  return (
    botReady         &&
    isBotOnline      &&
    bot              !== null &&
    bot.entity       !== null &&
    !isShuttingDown
  );
}

function canActSpectator() {
  return canAct() && isInSpectatorMode;
}

// ============================================================================
// 🔄 STATE HELPERS
// ============================================================================
function clearAllHandles() {
  if (heartbeatHandle) {
    clearInterval(heartbeatHandle);
    heartbeatHandle = null;
  }
  if (actionSchedulerHandle) {
    clearTimeout(actionSchedulerHandle);
    actionSchedulerHandle = null;
  }
  if (reconnectHandle) {
    clearTimeout(reconnectHandle);
    reconnectHandle = null;
  }
  if (activityCheckHandle) {
    clearInterval(activityCheckHandle);
    activityCheckHandle = null;
  }
  if (spawnTimeoutHandle) {
    clearTimeout(spawnTimeoutHandle);
    spawnTimeoutHandle = null;
  }
  actionInProgress = false;
  currentAction    = null;
}

function resetBotState() {
  isBotOnline        = false;
  botReady           = false;
  isInSpectatorMode  = false;
  isTimeFrozen       = false;
  botStartTime       = null;
  movementCount      = 0;
  behaviorPhase      = 'active';
  nearbyPlayers      = [];
  mistakeCounter     = 0;
  otherPlayersOnline = 0;
  actionInProgress   = false;
  currentAction      = null;
}

// ============================================================================
// 📡 DISCORD WEBHOOKS
// ============================================================================
async function sendDiscordEmbed(title, description, color = DEFAULT_COLOR, fields = []) {
  if (!DISCORD_WEBHOOK) return;
  try {
    await axios.post(DISCORD_WEBHOOK, {
      embeds: [{ title, description, color, fields, timestamp: new Date().toISOString() }],
    }, { timeout: 8000 });
  } catch (err) {
    console.error('❌ Discord Webhook Error:', err.message);
  }
}

async function sendChatEmbed(title, description, color = SUCCESS_COLOR, fields = []) {
  if (!CHAT_WEBHOOK) return;
  try {
    await axios.post(CHAT_WEBHOOK, {
      embeds: [{ title, description, color, fields, timestamp: new Date().toISOString() }],
    }, { timeout: 8000 });
  } catch (err) {
    console.error('❌ Chat Webhook Error:', err.message);
  }
}

async function sendPlayerMessage(username, message) {
  if (username === BOT_USERNAME || !MESSAGE_WEBHOOK) return;
  try {
    await axios.post(MESSAGE_WEBHOOK, {
      content: `💬 **${username}**: ${message}`,
    }, { timeout: 8000 });
  } catch (err) {
    console.error('❌ Message Webhook Error:', err.message);
  }
}

// ============================================================================
// 👥 PLAYER HELPERS
// ============================================================================
function getOnlinePlayersExcludingBot() {
  if (!bot || !bot.players || !canAct()) return [];
  return Object.values(bot.players).filter(p => p.username !== BOT_USERNAME);
}

function updateSpectatorMode() {
  if (!bot || !bot.game) return;
  const gm = bot.game.gameMode;
  isInSpectatorMode = (gm === 'spectator' || gm === 3);
  if (isInSpectatorMode) {
    console.log('👻 Confirmed in SPECTATOR mode — movement engine armed');
  }
}

function getNearbyPlayers(radius = 64) {
  if (!canAct() || !bot.players) return [];
  const botPos = bot.entity.position;
  const nearby = [];
  Object.values(bot.players).forEach(player => {
    if (player.username === BOT_USERNAME) return;
    if (!player.entity) return;
    const dist = botPos.distanceTo(player.entity.position);
    if (dist <= radius) {
      nearby.push({ username: player.username, distance: dist, position: player.entity.position });
    }
  });
  return nearby;
}

function refreshNearbyPlayers() {
  if (!canAct()) return;
  const now = Date.now();
  if (now - lastPlayerCheckMs > 3000) {
    nearbyPlayers = getNearbyPlayers();
    lastPlayerCheckMs = now;
  }
}

function updateBehaviorPhase() {
  if (!botStartTime) return;
  const minutes = (Date.now() - botStartTime) / 60000;
  if (minutes < 10)       behaviorPhase = 'active';
  else if (minutes < 30)  behaviorPhase = 'moderate';
  else                    behaviorPhase = 'idle';
}

// ============================================================================
// ⏰ TIME FREEZE / UNFREEZE
// ============================================================================
async function freezeTime() {
  if (!canAct() || isTimeFrozen) return;
  try {
    bot.chat('/tick freeze');
    isTimeFrozen = true;
    console.log('⏸️  Time frozen — bot is alone');
    await sendDiscordEmbed('Time Control', 'Time frozen — bot is the only player', INFO_COLOR);
  } catch (err) {
    console.error('❌ Error freezing time:', err.message);
  }
}

async function unfreezeTime() {
  if (!canAct() || !isTimeFrozen) return;
  try {
    bot.chat('/tick unfreeze');
    isTimeFrozen = false;
    console.log('▶️  Time unfrozen — other players joined');
    await sendDiscordEmbed('Time Control', 'Time unfrozen — players online', INFO_COLOR);
  } catch (err) {
    console.error('❌ Error unfreezing time:', err.message);
  }
}

async function ensureTimeUnfrozen() {
  if (isTimeFrozen && bot && isBotOnline) {
    try {
      bot.chat('/tick unfreeze');
      isTimeFrozen = false;
      console.log('✅ Time unfrozen before disconnect');
      await new Promise(r => setTimeout(r, 800));
    } catch (_) {}
  }
}

function checkPlayerCount() {
  if (!bot || !AUTO_TIME_FREEZE || !canAct()) return;
  const players = getOnlinePlayersExcludingBot();
  otherPlayersOnline = players.length;
  if (otherPlayersOnline === 0 && !isTimeFrozen) {
    setTimeout(() => freezeTime(), 2000);
  } else if (otherPlayersOnline > 0 && isTimeFrozen) {
    unfreezeTime();
  }
}

// ============================================================================
// 🎮 SPECTATOR MOVEMENT ENGINE
// All movements are strictly spectator-mode only.
// Uses bot.look() and bot.setControlState() — these are mineflayer's actual
// high-level movement API that send real protocol packets to the server.
// ============================================================================

// --- Utility: sleep ---
function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

// --- Utility: humanized random delay ---
function humanDelay(min, max) {
  const base     = min + Math.random() * (max - min);
  const jitter   = base * 0.25 * (Math.random() - 0.5);
  const spike    = Math.random() < 0.08 ? Math.random() * 800 : 0;
  return Math.max(100, Math.floor(base + jitter + spike));
}

// --- Utility: smooth interpolated look (simulates real mouse movement) ---
async function smoothLook(targetYaw, targetPitch, durationMs) {
  if (!canAct()) return;
  const startYaw   = bot.entity.yaw;
  const startPitch = bot.entity.pitch;
  const steps      = Math.max(4, Math.floor(durationMs / 50));
  for (let i = 1; i <= steps; i++) {
    if (!canAct()) break;
    const t     = i / steps;
    // ease-in-out cubic
    const ease  = t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
    const yaw   = startYaw   + (targetYaw   - startYaw)   * ease;
    const pitch = startPitch + (targetPitch - startPitch)  * ease;
    bot.look(yaw, pitch, false);
    await sleep(Math.floor(durationMs / steps));
  }
}

// --- Utility: micro-drift (tiny random look wobble like a real player) ---
async function microDrift(durationMs) {
  const endTime = Date.now() + durationMs;
  while (Date.now() < endTime && canAct()) {
    if (Math.random() < 0.12) {
      const yaw   = bot.entity.yaw   + (Math.random() - 0.5) * 0.08;
      const pitch = bot.entity.pitch + (Math.random() - 0.5) * 0.04;
      bot.look(yaw, pitch, false);
    }
    await sleep(200 + Math.random() * 300);
  }
}

// ============================================================================
// SPECTATOR ACTIONS — every single one checks canActSpectator()
// ============================================================================

// 1. Smooth look around (random direction)
async function doLookAround() {
  if (!canActSpectator()) return;
  const turns = 1 + Math.floor(Math.random() * 3);
  for (let i = 0; i < turns; i++) {
    if (!canActSpectator()) break;
    const yaw   = Math.random() * Math.PI * 2;
    const pitch = (Math.random() - 0.5) * (Math.PI / 2.2);
    await smoothLook(yaw, pitch, humanDelay(400, 1200));
    await sleep(humanDelay(200, 600));
  }
}

// 2. Slow pan (like a player carefully scanning)
async function doSlowPan() {
  if (!canActSpectator()) return;
  const startYaw   = bot.entity.yaw;
  const startPitch = bot.entity.pitch;
  const sweepAngle = (Math.random() - 0.5) * Math.PI * 1.2;
  const targetPitch = startPitch + (Math.random() - 0.5) * 0.3;
  await smoothLook(startYaw + sweepAngle, targetPitch, humanDelay(1500, 3500));
  await sleep(humanDelay(300, 800));
}

// 3. Quick snap look
async function doQuickLook() {
  if (!canActSpectator()) return;
  const yaw   = Math.random() * Math.PI * 2;
  const pitch = (Math.random() - 0.5) * 0.8;
  bot.look(yaw, pitch, false);
  await sleep(humanDelay(80, 200));
}

// 4. Look up / look at sky
async function doLookAtSky() {
  if (!canActSpectator()) return;
  const yaw = bot.entity.yaw + (Math.random() - 0.5) * 0.4;
  await smoothLook(yaw, -(0.9 + Math.random() * 0.6), humanDelay(500, 1200));
  await sleep(humanDelay(1000, 3000));
  if (!canActSpectator()) return;
  await smoothLook(bot.entity.yaw, 0, humanDelay(400, 900));
}

// 5. Look at ground
async function doLookAtGround() {
  if (!canActSpectator()) return;
  const yaw = bot.entity.yaw + (Math.random() - 0.5) * 0.3;
  await smoothLook(yaw, 0.9 + Math.random() * 0.5, humanDelay(400, 1000));
  await sleep(humanDelay(800, 2500));
}

// 6. Scan horizon (wide sweep left to right)
async function doScanHorizon() {
  if (!canActSpectator()) return;
  const startYaw  = bot.entity.yaw;
  const sweepSize = Math.PI * (0.6 + Math.random() * 0.8);
  const steps     = 10 + Math.floor(Math.random() * 8);
  for (let i = 0; i <= steps; i++) {
    if (!canActSpectator()) break;
    const t   = i / steps;
    const yaw = startYaw - sweepSize / 2 + sweepSize * t;
    bot.look(yaw, (Math.random() - 0.5) * 0.15, false);
    await sleep(humanDelay(80, 200));
  }
}

// 7. Look behind
async function doLookBehind() {
  if (!canActSpectator()) return;
  const startYaw = bot.entity.yaw;
  await smoothLook(startYaw + Math.PI, 0, humanDelay(300, 600));
  await sleep(humanDelay(600, 2000));
  if (!canActSpectator()) return;
  await smoothLook(startYaw, 0, humanDelay(300, 600));
}

// 8. Fly forward (spectator noclip)
async function doFlyForward() {
  if (!canActSpectator()) return;
  const yaw = Math.random() * Math.PI * 2;
  await smoothLook(yaw, (Math.random() - 0.5) * 0.4, humanDelay(200, 500));
  if (!canActSpectator()) return;

  bot.setControlState('forward', true);
  const duration = humanDelay(800, 3500);
  const endTime  = Date.now() + duration;

  while (Date.now() < endTime && canActSpectator()) {
    // Occasionally adjust look mid-flight (like a real player steering)
    if (Math.random() < 0.15) {
      const curYaw   = bot.entity.yaw;
      const curPitch = bot.entity.pitch;
      bot.look(curYaw + (Math.random() - 0.5) * 0.12, curPitch + (Math.random() - 0.5) * 0.08, false);
    }
    await sleep(100);
  }

  bot.clearControlStates();
  movementCount++;
}

// 9. Fly backward
async function doFlyBackward() {
  if (!canActSpectator()) return;
  bot.setControlState('back', true);
  await sleep(humanDelay(500, 2000));
  if (bot) bot.clearControlStates();
  movementCount++;
}

// 10. Sprint fly (fast forward)
async function doSprintFly() {
  if (!canActSpectator()) return;
  const yaw = Math.random() * Math.PI * 2;
  await smoothLook(yaw, (Math.random() - 0.5) * 0.3, humanDelay(200, 400));
  if (!canActSpectator()) return;

  bot.setControlState('sprint', true);
  bot.setControlState('forward', true);
  const duration = humanDelay(1500, 5000);
  const endTime  = Date.now() + duration;

  while (Date.now() < endTime && canActSpectator()) {
    if (Math.random() < 0.1) {
      bot.look(bot.entity.yaw + (Math.random() - 0.5) * 0.15, bot.entity.pitch + (Math.random() - 0.5) * 0.1, false);
    }
    await sleep(100);
  }

  bot.clearControlStates();
  movementCount++;
}

// 11. Fly up (spectator: look up + forward = ascend)
async function doFlyUp() {
  if (!canActSpectator()) return;
  const pitch = -(0.6 + Math.random() * 0.9); // look up
  await smoothLook(bot.entity.yaw, pitch, humanDelay(300, 700));
  if (!canActSpectator()) return;

  bot.setControlState('forward', true);
  await sleep(humanDelay(600, 2500));
  bot.clearControlStates();

  // Level out
  if (canActSpectator()) {
    await smoothLook(bot.entity.yaw, 0, humanDelay(300, 600));
  }
  movementCount++;
}

// 12. Fly down (spectator: look down + forward = descend)
async function doFlyDown() {
  if (!canActSpectator()) return;
  const pitch = 0.6 + Math.random() * 0.9; // look down
  await smoothLook(bot.entity.yaw, pitch, humanDelay(300, 700));
  if (!canActSpectator()) return;

  bot.setControlState('forward', true);
  await sleep(humanDelay(600, 2000));
  bot.clearControlStates();

  if (canActSpectator()) {
    await smoothLook(bot.entity.yaw, 0, humanDelay(300, 600));
  }
  movementCount++;
}

// 13. Float up using jump key (spectator)
async function doFloatUp() {
  if (!canActSpectator()) return;
  bot.setControlState('jump', true);
  await sleep(humanDelay(500, 2000));
  bot.clearControlStates();
  movementCount++;
}

// 14. Float down using sneak key (spectator)
async function doFloatDown() {
  if (!canActSpectator()) return;
  bot.setControlState('sneak', true);
  await sleep(humanDelay(500, 1800));
  bot.clearControlStates();
  movementCount++;
}

// 15. Strafe left / right
async function doStrafe() {
  if (!canActSpectator()) return;
  const side = Math.random() < 0.5 ? 'left' : 'right';
  bot.setControlState(side, true);
  await sleep(humanDelay(400, 2000));
  bot.clearControlStates();
  movementCount++;
}

// 16. Zigzag flight (alternating strafes while moving forward)
async function doZigzagFly() {
  if (!canActSpectator()) return;
  const yaw = Math.random() * Math.PI * 2;
  await smoothLook(yaw, (Math.random() - 0.5) * 0.2, humanDelay(200, 400));
  if (!canActSpectator()) return;

  const legs = 3 + Math.floor(Math.random() * 3);
  for (let i = 0; i < legs; i++) {
    if (!canActSpectator()) break;
    bot.clearControlStates();
    bot.setControlState('forward', true);
    bot.setControlState(i % 2 === 0 ? 'left' : 'right', true);
    await sleep(humanDelay(400, 900));
  }
  bot.clearControlStates();
  movementCount++;
}

// 17. Diagonal fly
async function doDiagonalFly() {
  if (!canActSpectator()) return;
  const combos = [['forward','left'],['forward','right'],['back','left'],['back','right']];
  const combo  = combos[Math.floor(Math.random() * combos.length)];
  combo.forEach(d => bot.setControlState(d, true));
  await sleep(humanDelay(700, 2500));
  bot.clearControlStates();
  movementCount++;
}

// 18. Circle fly (forward + slowly rotate yaw)
async function doCircleFly() {
  if (!canActSpectator()) return;
  const duration = humanDelay(3000, 7000);
  const endTime  = Date.now() + duration;
  bot.setControlState('forward', true);
  while (Date.now() < endTime && canActSpectator()) {
    const yaw = bot.entity.yaw + (Math.PI / 180) * (4 + Math.random() * 3);
    bot.look(yaw, bot.entity.pitch, false);
    await sleep(80);
  }
  bot.clearControlStates();
  movementCount++;
}

// 19. Short idle (complete stillness)
async function doIdleShort() {
  if (!canActSpectator()) return;
  bot.clearControlStates();
  await sleep(humanDelay(500, 2500));
}

// 20. Medium idle (stillness with micro eye drift)
async function doIdleMedium() {
  if (!canActSpectator()) return;
  bot.clearControlStates();
  await microDrift(humanDelay(2000, 6000));
}

// 21. Long idle (true AFK simulation)
async function doIdleLong() {
  if (!canActSpectator()) return;
  bot.clearControlStates();
  const dur = humanDelay(8000, 20000);
  console.log(`💤 Long idle for ${Math.floor(dur / 1000)}s`);
  await microDrift(dur);
}

// 22. Swing arm
async function doSwingArm() {
  if (!canActSpectator()) return;
  const swings = 1 + Math.floor(Math.random() * 3);
  for (let i = 0; i < swings; i++) {
    if (!canActSpectator()) break;
    bot.swingArm('right');
    await sleep(humanDelay(100, 400));
  }
  movementCount++;
}

// 23. Hotbar switch
async function doHotbarSwitch() {
  if (!canActSpectator()) return;
  try {
    const current = bot.quickBarSlot || 0;
    const switches = 1 + Math.floor(Math.random() * 3);
    for (let i = 0; i < switches; i++) {
      if (!canActSpectator()) break;
      let slot = Math.floor(Math.random() * 9);
      if (slot === current) slot = (slot + 1) % 9;
      bot.setQuickBarSlot(slot);
      await sleep(humanDelay(80, 450));
    }
  } catch (_) {}
}

// 24. Rapid hotbar scroll
async function doHotbarScroll() {
  if (!canActSpectator()) return;
  try {
    for (let i = 0; i < 9 && canActSpectator(); i++) {
      bot.setQuickBarSlot(i);
      await sleep(humanDelay(40, 120));
    }
  } catch (_) {}
}

// 25. Phase through blocks (fly straight, spectator noclip)
async function doPhaseThrough() {
  if (!canActSpectator()) return;
  const yaw = Math.random() * Math.PI * 2;
  bot.look(yaw, (Math.random() - 0.5) * 0.3, false);
  bot.setControlState('forward', true);
  await sleep(humanDelay(1000, 3500));
  bot.clearControlStates();
  movementCount++;
  console.log('👻 Spectator: phased through blocks');
}

// 26. Orbit a spot (circle around current position)
async function doOrbitFly() {
  if (!canActSpectator()) return;
  const startYaw = bot.entity.yaw;
  const speed    = Math.PI / 180 * (3 + Math.random() * 4);
  const duration = humanDelay(4000, 9000);
  const endTime  = Date.now() + duration;

  bot.setControlState('forward', true);
  bot.setControlState('left', true);

  while (Date.now() < endTime && canActSpectator()) {
    const yaw = bot.entity.yaw + speed;
    bot.look(yaw, bot.entity.pitch, false);
    await sleep(80);
  }
  bot.clearControlStates();
  movementCount++;
}

// 27. Look at player (if nearby)
async function doLookAtPlayer() {
  if (!canActSpectator() || nearbyPlayers.length === 0) return;
  const player  = nearbyPlayers[Math.floor(Math.random() * nearbyPlayers.length)];
  const botPos  = bot.entity.position;
  const pPos    = player.position;
  const yaw     = Math.atan2(-(pPos.x - botPos.x), pPos.z - botPos.z);
  const dist    = botPos.distanceTo(pPos);
  const pitch   = -Math.atan2(pPos.y - botPos.y, dist);
  await smoothLook(yaw, pitch, humanDelay(400, 1000));
  await sleep(humanDelay(1500, 5000));
}

// 28. Fly toward a player briefly
async function doFlyTowardPlayer() {
  if (!canActSpectator() || nearbyPlayers.length === 0) return;
  const player  = nearbyPlayers[0];
  const botPos  = bot.entity.position;
  const pPos    = player.position;
  const yaw     = Math.atan2(-(pPos.x - botPos.x), pPos.z - botPos.z);
  await smoothLook(yaw, 0, humanDelay(300, 700));
  if (!canActSpectator()) return;
  bot.setControlState('forward', true);
  await sleep(humanDelay(1500, 4000));
  bot.clearControlStates();
  movementCount++;
}

// 29. Fly away from player
async function doFlyAwayFromPlayer() {
  if (!canActSpectator() || nearbyPlayers.length === 0) return;
  const player = nearbyPlayers[0];
  const botPos = bot.entity.position;
  const pPos   = player.position;
  // Opposite direction
  const yaw    = Math.atan2(-(pPos.x - botPos.x), pPos.z - botPos.z) + Math.PI;
  await smoothLook(yaw, 0, humanDelay(300, 700));
  if (!canActSpectator()) return;
  bot.setControlState('forward', true);
  await sleep(humanDelay(1000, 3000));
  bot.clearControlStates();
  movementCount++;
}

// 30. Human mistake: wrong direction correction
async function doWrongDirection() {
  if (!canActSpectator()) return;
  console.log('🤦 Mistake: wrong direction');
  bot.setControlState('forward', true);
  await sleep(humanDelay(400, 800));
  bot.clearControlStates();
  await sleep(humanDelay(300, 600));
  // Correct
  if (!canActSpectator()) return;
  const newYaw = bot.entity.yaw + Math.PI + (Math.random() - 0.5) * 0.4;
  await smoothLook(newYaw, 0, humanDelay(200, 400));
  bot.setControlState('forward', true);
  await sleep(humanDelay(600, 1200));
  bot.clearControlStates();
  movementCount++;
  mistakeCounter++;
}

// 31. Human mistake: sudden stop
async function doSuddenStop() {
  if (!canActSpectator()) return;
  console.log('🤦 Mistake: sudden stop');
  bot.setControlState('forward', true);
  bot.setControlState('sprint', true);
  await sleep(humanDelay(800, 2000));
  bot.clearControlStates();
  await sleep(humanDelay(1000, 3500));
  movementCount++;
  mistakeCounter++;
}

// 32. Human mistake: hesitation
async function doHesitation() {
  if (!canActSpectator()) return;
  console.log('🤦 Mistake: hesitation');
  bot.setControlState('forward', true);
  await sleep(humanDelay(200, 500));
  bot.clearControlStates();
  await sleep(humanDelay(400, 1000));
  if (!canActSpectator()) return;
  bot.setControlState('forward', true);
  await sleep(humanDelay(400, 900));
  bot.clearControlStates();
  movementCount++;
  mistakeCounter++;
}

// 33. Human mistake: overcorrect look
async function doOvercorrectLook() {
  if (!canActSpectator()) return;
  console.log('🤦 Mistake: overcorrect');
  const startYaw = bot.entity.yaw;
  await smoothLook(startYaw + Math.PI / 2.5, 0, humanDelay(150, 300));
  await sleep(100);
  if (!canActSpectator()) return;
  await smoothLook(startYaw - Math.PI / 8, 0, humanDelay(150, 300));
  await sleep(100);
  if (!canActSpectator()) return;
  await smoothLook(startYaw + (Math.random() - 0.5) * 0.3, 0, humanDelay(200, 400));
  mistakeCounter++;
}

// 34. Fly in a figure-8 pattern
async function doFigureEightFly() {
  if (!canActSpectator()) return;
  const startYaw = bot.entity.yaw;
  bot.setControlState('forward', true);
  for (let i = 0; i < 120 && canActSpectator(); i++) {
    // sin wave on yaw to create figure-8 pattern
    const yaw = startYaw + Math.sin(i * Math.PI / 30) * (Math.PI / 3);
    bot.look(yaw, 0, false);
    await sleep(80);
  }
  bot.clearControlStates();
  movementCount++;
}

// 35. Look at coordinate (random block simulation)
async function doLookAtCoord() {
  if (!canActSpectator()) return;
  const botPos = bot.entity.position;
  const tx = botPos.x + (Math.random() - 0.5) * 20;
  const ty = botPos.y + (Math.random() - 0.5) * 10;
  const tz = botPos.z + (Math.random() - 0.5) * 20;
  const dx = tx - botPos.x;
  const dz = tz - botPos.z;
  const dy = ty - botPos.y;
  const dist = Math.sqrt(dx * dx + dz * dz);
  const yaw  = Math.atan2(-dx, dz);
  const pitch = -Math.atan2(dy, dist);
  await smoothLook(yaw, pitch, humanDelay(400, 1200));
  await sleep(humanDelay(1000, 4000));
}

// 36. Approach a coordinate then look around (exploration simulation)
async function doExplore() {
  if (!canActSpectator()) return;
  const yaw = Math.random() * Math.PI * 2;
  await smoothLook(yaw, (Math.random() - 0.5) * 0.3, humanDelay(300, 600));
  if (!canActSpectator()) return;
  bot.setControlState('forward', true);
  await sleep(humanDelay(2000, 5000));
  bot.clearControlStates();
  if (!canActSpectator()) return;
  await doScanHorizon();
  movementCount++;
}

// 37. Activate item (right click in air)
async function doActivateItem() {
  if (!canActSpectator()) return;
  try {
    bot.activateItem();
    await sleep(humanDelay(200, 500));
  } catch (_) {}
}

// 38. Deactivate item
async function doDeactivateItem() {
  if (!canActSpectator()) return;
  try {
    bot.deactivateItem();
    await sleep(humanDelay(100, 300));
  } catch (_) {}
}

// 39. Up + down oscillation (hovering simulation)
async function doHover() {
  if (!canActSpectator()) return;
  const cycles = 2 + Math.floor(Math.random() * 3);
  for (let i = 0; i < cycles; i++) {
    if (!canActSpectator()) break;
    bot.setControlState('jump', true);
    await sleep(humanDelay(300, 700));
    bot.clearControlStates();
    await sleep(humanDelay(200, 400));
    bot.setControlState('sneak', true);
    await sleep(humanDelay(300, 700));
    bot.clearControlStates();
    await sleep(humanDelay(200, 400));
  }
  movementCount++;
}

// 40. Full stop (clear everything, micro drift)
async function doFullStop() {
  if (!canActSpectator()) return;
  bot.clearControlStates();
  await microDrift(humanDelay(500, 1500));
}

// 41. Look toward spawn (0,0)
async function doLookTowardSpawn() {
  if (!canActSpectator()) return;
  const pos = bot.entity.position;
  const yaw = Math.atan2(-pos.x, pos.z);
  await smoothLook(yaw, 0, humanDelay(600, 1500));
  await sleep(humanDelay(1000, 3000));
}

// 42. Stutter fly (start/stop multiple times)
async function doStutterFly() {
  if (!canActSpectator()) return;
  const stops = 3 + Math.floor(Math.random() * 3);
  const yaw   = Math.random() * Math.PI * 2;
  await smoothLook(yaw, 0, humanDelay(200, 400));
  for (let i = 0; i < stops; i++) {
    if (!canActSpectator()) break;
    bot.setControlState('forward', true);
    await sleep(humanDelay(300, 800));
    bot.clearControlStates();
    await sleep(humanDelay(200, 600));
  }
  movementCount++;
}

// ============================================================================
// 🎯 ACTION TABLE
// ============================================================================
const ACTIONS = [
  // --- Looking (no guard issue if spectator not confirmed yet, but we still check) ---
  { name: 'LOOK_AROUND',         fn: doLookAround,          weight: 14, phase: 'all'      },
  { name: 'SLOW_PAN',            fn: doSlowPan,             weight: 10, phase: 'all'      },
  { name: 'QUICK_LOOK',          fn: doQuickLook,           weight:  6, phase: 'all'      },
  { name: 'LOOK_AT_SKY',         fn: doLookAtSky,           weight:  5, phase: 'all'      },
  { name: 'LOOK_AT_GROUND',      fn: doLookAtGround,        weight:  4, phase: 'all'      },
  { name: 'SCAN_HORIZON',        fn: doScanHorizon,         weight:  6, phase: 'all'      },
  { name: 'LOOK_BEHIND',         fn: doLookBehind,          weight:  4, phase: 'all'      },
  { name: 'LOOK_AT_COORD',       fn: doLookAtCoord,         weight:  5, phase: 'all'      },
  { name: 'LOOK_TOWARD_SPAWN',   fn: doLookTowardSpawn,     weight:  2, phase: 'all'      },

  // --- Flight ---
  { name: 'FLY_FORWARD',         fn: doFlyForward,          weight: 14, phase: 'active'   },
  { name: 'FLY_BACKWARD',        fn: doFlyBackward,         weight:  4, phase: 'all'      },
  { name: 'SPRINT_FLY',          fn: doSprintFly,           weight:  8, phase: 'active'   },
  { name: 'FLY_UP',              fn: doFlyUp,               weight:  6, phase: 'all'      },
  { name: 'FLY_DOWN',            fn: doFlyDown,             weight:  5, phase: 'all'      },
  { name: 'FLOAT_UP',            fn: doFloatUp,             weight:  4, phase: 'all'      },
  { name: 'FLOAT_DOWN',          fn: doFloatDown,           weight:  4, phase: 'all'      },
  { name: 'STRAFE',              fn: doStrafe,              weight:  5, phase: 'all'      },
  { name: 'ZIGZAG_FLY',          fn: doZigzagFly,           weight:  5, phase: 'active'   },
  { name: 'DIAGONAL_FLY',        fn: doDiagonalFly,         weight:  4, phase: 'all'      },
  { name: 'CIRCLE_FLY',          fn: doCircleFly,           weight:  3, phase: 'moderate' },
  { name: 'ORBIT_FLY',           fn: doOrbitFly,            weight:  2, phase: 'moderate' },
  { name: 'FIGURE_EIGHT',        fn: doFigureEightFly,      weight:  2, phase: 'moderate' },
  { name: 'PHASE_THROUGH',       fn: doPhaseThrough,        weight:  3, phase: 'active'   },
  { name: 'EXPLORE',             fn: doExplore,             weight:  4, phase: 'active'   },
  { name: 'STUTTER_FLY',         fn: doStutterFly,          weight:  3, phase: 'all'      },
  { name: 'HOVER',               fn: doHover,               weight:  3, phase: 'all'      },

  // --- Idle ---
  { name: 'IDLE_SHORT',          fn: doIdleShort,           weight: 10, phase: 'all'      },
  { name: 'IDLE_MEDIUM',         fn: doIdleMedium,          weight:  7, phase: 'all'      },
  { name: 'IDLE_LONG',           fn: doIdleLong,            weight:  4, phase: 'idle'     },
  { name: 'FULL_STOP',           fn: doFullStop,            weight:  5, phase: 'all'      },

  // --- Interactive ---
  { name: 'SWING_ARM',           fn: doSwingArm,            weight:  5, phase: 'all'      },
  { name: 'HOTBAR_SWITCH',       fn: doHotbarSwitch,        weight:  4, phase: 'all'      },
  { name: 'HOTBAR_SCROLL',       fn: doHotbarScroll,        weight:  2, phase: 'all'      },
  { name: 'ACTIVATE_ITEM',       fn: doActivateItem,        weight:  3, phase: 'all'      },
  { name: 'DEACTIVATE_ITEM',     fn: doDeactivateItem,      weight:  2, phase: 'all'      },

  // --- Player-aware (only run when nearbyPlayers > 0) ---
  { name: 'LOOK_AT_PLAYER',      fn: doLookAtPlayer,        weight:  9, phase: 'all',     needsPlayer: true },
  { name: 'FLY_TOWARD_PLAYER',   fn: doFlyTowardPlayer,     weight:  4, phase: 'active',  needsPlayer: true },
  { name: 'FLY_AWAY_PLAYER',     fn: doFlyAwayFromPlayer,   weight:  3, phase: 'all',     needsPlayer: true },

  // --- Human mistakes ---
  { name: 'WRONG_DIRECTION',     fn: doWrongDirection,      weight:  2, phase: 'all'      },
  { name: 'SUDDEN_STOP',         fn: doSuddenStop,          weight:  2, phase: 'all'      },
  { name: 'HESITATION',          fn: doHesitation,          weight:  3, phase: 'all'      },
  { name: 'OVERCORRECT_LOOK',    fn: doOvercorrectLook,     weight:  2, phase: 'all'      },
];

function buildWeightedPool() {
  const pool = [];
  for (const action of ACTIONS) {
    // Phase filter
    if (action.phase !== 'all' && action.phase !== behaviorPhase) {
      // Allow actions of other phases with reduced weight
      const reduced = Math.max(1, Math.floor(action.weight * 0.25));
      for (let i = 0; i < reduced; i++) pool.push(action);
      continue;
    }
    // Player-required filter
    if (action.needsPlayer && nearbyPlayers.length === 0) continue;

    // Boost player-aware actions if players are nearby
    let w = action.weight;
    if (action.needsPlayer && nearbyPlayers.length > 0) w *= 3;

    // Boost idle in idle phase
    if (behaviorPhase === 'idle' && action.name.includes('IDLE')) w *= 2;

    // 5% chance to inject mistake
    if (action.name.includes('DIRECTION') || action.name.includes('STOP') ||
        action.name.includes('HESITATION') || action.name.includes('OVERCORRECT')) {
      if (Math.random() < 0.05) w *= 4;
    }

    for (let i = 0; i < w; i++) pool.push(action);
  }
  return pool;
}

function pickAction() {
  const pool = buildWeightedPool();
  if (pool.length === 0) return ACTIONS[0];
  return pool[Math.floor(Math.random() * pool.length)];
}

// ============================================================================
// 💓 ANTI-TIMEOUT HEARTBEAT
// Aternos kicks bots that send zero packets for ~30s.
// This fires every 4 seconds and sends a guaranteed tiny movement packet
// (a look update) so the server always sees activity, regardless of what
// the action scheduler is doing.
// ============================================================================
function startHeartbeat() {
  if (heartbeatHandle) clearInterval(heartbeatHandle);

  heartbeatHandle = setInterval(() => {
    if (!canActSpectator()) return;

    try {
      // Tiny micro-look — imperceptible to a human watcher but counts as a
      // movement packet to the server, resetting its idle timer.
      const yaw   = bot.entity.yaw   + (Math.random() - 0.5) * 0.03;
      const pitch = bot.entity.pitch + (Math.random() - 0.5) * 0.015;
      bot.look(yaw, pitch, false);
    } catch (_) {}
  }, 4000); // every 4 seconds — well within Aternos 30s timeout window
}


async function executeAction(action) {
  // Double-check guard before every action
  if (!canActSpectator() || actionInProgress) return;

  actionInProgress = true;
  currentAction    = action.name;

  try {
    await action.fn();
  } catch (err) {
    console.error(`❌ Action ${action.name} error:`, err.message);
    if (bot && botReady) {
      try { bot.clearControlStates(); } catch (_) {}
    }
  } finally {
    actionInProgress = false;
    currentAction    = null;
  }
}

function scheduleNextAction() {
  if (!canActSpectator() || isShuttingDown) return;

  refreshNearbyPlayers();
  updateBehaviorPhase();

  let minMs, maxMs;
  switch (behaviorPhase) {
    case 'active':   minMs =  500; maxMs =  4000; break;
    case 'moderate': minMs = 2000; maxMs =  9000; break;
    case 'idle':     minMs = 3000; maxMs = 12000; break;
    default:         minMs = 1000; maxMs =  6000;
  }

  // More responsive when players are nearby
  if (nearbyPlayers.length > 0) {
    minMs = Math.max(300, minMs * 0.6);
    maxMs = Math.max(2000, maxMs * 0.6);
  }

  const delay = humanDelay(minMs, maxMs);

  actionSchedulerHandle = setTimeout(async () => {
    if (!canActSpectator()) return;

    const action = pickAction();

    // Log occasionally (5%)
    if (Math.random() < 0.05) {
      console.log(`🎮 [${behaviorPhase}] ${action.name} | nearby: ${nearbyPlayers.length} | moves: ${movementCount} | mistakes: ${mistakeCounter}`);
    }

    await executeAction(action);

    // Schedule next only if still valid
    if (canActSpectator()) {
      scheduleNextAction();
    }
  }, delay);
}

// ============================================================================
// 🏃 ACTIVITY CHECK
// ============================================================================
function checkBotActivity() {
  if (!botStartTime || !isBotOnline || !ANTI_AFK) return;
  const uptime = Date.now() - botStartTime;
  if (uptime >= ONE_HOUR) {
    console.log('⏰ 1-hour uptime reached — rejoining to avoid AFK detection');
    sendDiscordEmbed('AFK Prevention', 'Bot active 1+ hour — rejoining server', WARNING_COLOR);
    forceRejoin();
  }
}

function setupActivityCheck() {
  if (activityCheckHandle) clearInterval(activityCheckHandle);
  activityCheckHandle = setInterval(() => {
    checkBotActivity();
    checkPlayerCount();
    refreshNearbyPlayers();
  }, ACTIVITY_CHECK_MS);
}

// ============================================================================
// 🔁 RECONNECT LOGIC (3s → 5s → 10s max)
// ============================================================================
function getReconnectDelay() {
  const idx = Math.min(consecutiveFailures, RECONNECT_DELAYS.length - 1);
  return RECONNECT_DELAYS[idx];
}

function scheduleReconnect() {
  if (isShuttingDown) {
    console.log('🛑 Shutting down — skipping reconnect');
    return;
  }
  clearAllHandles();
  const delay = getReconnectDelay();
  console.log(`⏳ Reconnecting in ${delay / 1000}s (failure #${consecutiveFailures + 1})...`);
  reconnectHandle = setTimeout(() => startBot(), delay);
}

function forceRejoin() {
  if (isShuttingDown) return;
  clearAllHandles();
  console.log(`⏳ Force-rejoining in 5s...`);
  reconnectHandle = setTimeout(() => startBot(), 5000);
}

// ============================================================================
// 🗃️ PLAYER FACE MANAGEMENT
// ============================================================================
async function getOrCreatePlayerFace(username, uuid) {
  if (!dbConnected || !PlayerFace) {
    // Fallback: return crafatar URL if not a dot-username
    if (username && !username.startsWith('.') && uuid) {
      return `https://crafatar.com/avatars/${uuid}?size=32&overlay`;
    }
    return `./${FACES[Math.floor(Math.random() * FACES.length)]}`;
  }

  try {
    let record = await PlayerFace.findOne({ username });
    if (record) {
      return record.isCustom ? record.face : `./${record.face}`;
    }

    let skinUrl;
    if (username.startsWith('.')) {
      const used = await PlayerFace.find({ username: /^\./ }, 'face');
      const available = FACES.filter(f => !used.some(u => u.face === f));
      const face = available.length > 0 ? FACES[nextDotFaceIndex++ % FACES.length] : FACES[Math.floor(Math.random() * FACES.length)];
      record  = new PlayerFace({ username, face, isCustom: false });
      skinUrl = `./${face}`;
    } else {
      try {
        const faceUrl = uuid
          ? `https://crafatar.com/avatars/${uuid}?size=32&overlay`
          : `https://crafatar.com/avatars/${username}?size=32&overlay`;
        const res = await axios.get(faceUrl, { responseType: 'arraybuffer', timeout: 5000 });
        if (res.status === 200) {
          skinUrl = faceUrl;
          record  = new PlayerFace({ username, face: skinUrl, isCustom: true });
        } else throw new Error('not found');
      } catch (_) {
        const face = FACES[Math.floor(Math.random() * FACES.length)];
        skinUrl = `./${face}`;
        record  = new PlayerFace({ username, face, isCustom: false });
      }
    }

    await record.save();
    return skinUrl;
  } catch (err) {
    console.error('❌ getOrCreatePlayerFace error:', err.message);
    return `./${FACES[0]}`;
  }
}

// ============================================================================
// 📊 STATUS PAYLOAD
// ============================================================================
function getCpuUsage() {
  const cpus = os.cpus();
  let totalIdle = 0, totalTick = 0;
  for (const cpu of cpus) {
    for (const t in cpu.times) totalTick += cpu.times[t];
    totalIdle += cpu.times.idle;
  }
  const idleDiff  = totalIdle - lastCpuSnapshot.idle;
  const totalDiff = totalTick - lastCpuSnapshot.total;
  lastCpuSnapshot = { idle: totalIdle, total: totalTick };
  if (totalDiff === 0) return 0;
  return 100 - (100 * idleDiff / totalDiff);
}

async function getBotStatusPayload() {
  const active = canAct();

  let onlineCount   = 0;
  let playerDetails = [];

  if (active) {
    const others = getOnlinePlayersExcludingBot();
    onlineCount   = others.length;
    playerDetails = await Promise.all(others.map(async p => {
      const skinUrl = await getOrCreatePlayerFace(p.username, p.uuid);
      return { username: p.username, uuid: p.uuid, skinUrl };
    }));
  }

  let diskInfo = { free: 0, total: 0 };
  try {
    diskInfo = await diskusage.check(os.platform() === 'win32' ? 'C:' : '/');
  } catch (_) {}

  return {
    message:           active ? 'Bot is running!' : 'Bot is offline',
    onlinePlayersCount: active ? onlineCount : 0,
    playerDetails:     active ? playerDetails : [],
    gameMode:          active && bot.game ? bot.game.gameMode : 'N/A',
    isSpectator:       isInSpectatorMode,
    position:          active && bot.entity ? {
      x: Math.floor(bot.entity.position.x),
      y: Math.floor(bot.entity.position.y),
      z: Math.floor(bot.entity.position.z),
    } : 'N/A',
    uptime:            active && botStartTime ? Math.floor((Date.now() - botStartTime) / 1000) : 0,
    movements:         active ? movementCount : 0,
    currentAction:     active ? currentAction : null,
    behaviorPhase:     behaviorPhase,
    memoryUsage:       `${(process.memoryUsage().rss / 1024 / 1024).toFixed(2)} MB`,
    lastOnline:        lastOnlineTime || null,
    serverHost:        currentServerHost,
    serverPort:        currentServerPort,
    botName:           BOT_USERNAME,
    botHealth:         active && bot.health !== undefined ? `${Math.round(bot.health)}/20` : 'N/A',
    botFood:           active && bot.food   !== undefined ? `${Math.round(bot.food)}/20`   : 'N/A',
    botLatency:        active && bot.player && bot.player.ping !== undefined ? `${bot.player.ping}ms` : 'N/A',
    serverLoad:        os.loadavg()[0].toFixed(2),
    cpuUsage:          getCpuUsage().toFixed(2),
    diskFree:          diskInfo.total > 0 ? `${(diskInfo.free  / 1073741824).toFixed(2)} GB` : 'N/A',
    diskTotal:         diskInfo.total > 0 ? `${(diskInfo.total / 1073741824).toFixed(2)} GB` : 'N/A',
    minecraftDay:      active && bot.time ? bot.time.day       : 'N/A',
    minecraftTime:     active && bot.time ? bot.time.timeOfDay : 'N/A',
    serverDifficulty:  active && bot.game  ? bot.game.difficulty : 'N/A',
    timeFrozen:        isTimeFrozen,
    version:           BOT_VERSION,
    nearbyPlayers:     nearbyPlayers.length,
    consecutiveFailures,
    dbConnected,
  };
}

// ============================================================================
// 🤖 BOT STARTUP
// ============================================================================
function startBot() {
  if (isShuttingDown) {
    console.log('🛑 Shutting down — not starting bot');
    return;
  }

  clearAllHandles();

  // Destroy old bot if exists
  if (bot) {
    try {
      bot.removeAllListeners();
      bot.quit('Restarting');
    } catch (_) {}
    bot = null;
  }

  resetBotState();
  currentServerHost = BOT_HOST;
  currentServerPort = BOT_PORT;

  console.log(`\n🚀 Connecting to ${BOT_HOST}:${BOT_PORT} as ${BOT_USERNAME} (${BOT_VERSION})...`);

  const botOptions = {
    host:           BOT_HOST,
    port:           BOT_PORT,
    username:       BOT_USERNAME,
    version:        BOT_VERSION,
    keepAlive:      true,
    checkTimeoutInterval: 30000,
    chatLengthLimit: 256,
    auth:           'offline',
  };

  try {
    bot = mineflayer.createBot(botOptions);
  } catch (err) {
    console.error('❌ Failed to create bot:', err.message);
    consecutiveFailures++;
    scheduleReconnect();
    return;
  }

  // ---- SPAWN TIMEOUT — if bot never fires 'spawn' within SPAWN_TIMEOUT_MS ----
  spawnTimeoutHandle = setTimeout(() => {
    if (!isBotOnline) {
      console.log(`⏰ Spawn timeout after ${SPAWN_TIMEOUT_MS / 1000}s — retrying...`);
      consecutiveFailures++;
      try { bot.quit('Spawn timeout'); } catch (_) {}
      scheduleReconnect();
    }
  }, SPAWN_TIMEOUT_MS);

  // ---- SPAWN ----
  bot.once('spawn', async () => {
    clearTimeout(spawnTimeoutHandle);
    spawnTimeoutHandle = null;

    console.log(`✅ Spawned on ${BOT_HOST}:${BOT_PORT}`);

    isBotOnline        = true;
    botStartTime       = Date.now();
    lastOnlineTime     = Date.now();
    consecutiveFailures = 0;

    // Keep TCP alive
    if (bot._client && bot._client.socket) {
      bot._client.socket.setKeepAlive(true, 30000);
      bot._client.socket.setTimeout(0); // no idle timeout
    }

    // Wait for game mode packet (give server time to set it)
    await sleep(1500);

    // Detect game mode from bot.game
    updateSpectatorMode();

    // Also listen for game mode changes via player_info packet
    if (bot._client) {
      bot._client.on('player_info', (packet) => {
        if (!packet || !packet.data) return;
        packet.data.forEach(entry => {
          if (entry.uuid === bot.uuid) {
            const gmMap = { 0: 'survival', 1: 'creative', 2: 'adventure', 3: 'spectator' };
            const gm    = gmMap[entry.gamemode];
            if (gm) {
              bot.game = bot.game || {};
              bot.game.gameMode = gm;
              const wasSpectator = isInSpectatorMode;
              updateSpectatorMode();
              if (!wasSpectator && isInSpectatorMode) {
                console.log('🎮 Game mode switched to SPECTATOR — starting movement engine');
                startHeartbeat();
                if (!actionSchedulerHandle) scheduleNextAction();
              } else if (wasSpectator && !isInSpectatorMode) {
                console.log('⚠️  No longer in spectator — movement engine paused');
                if (bot) bot.clearControlStates();
                if (actionSchedulerHandle) {
                  clearTimeout(actionSchedulerHandle);
                  actionSchedulerHandle = null;
                }
              }
            }
          }
        });
      });

      // Also listen for game_state_change (for game mode updates)
      bot._client.on('game_state_change', (packet) => {
        if (packet.reason === 3) { // change game mode
          const gmMap = { 0: 'survival', 1: 'creative', 2: 'adventure', 3: 'spectator' };
          const gm    = gmMap[packet.gameMode];
          if (gm) {
            bot.game = bot.game || {};
            bot.game.gameMode = gm;
            updateSpectatorMode();
          }
        }
      });
    }

    // Mark as truly ready
    botReady = true;

    if (!isInSpectatorMode) {
      console.log('⚠️  Bot spawned but NOT in spectator mode — waiting for mode to be set');
      console.log('   (Bot will only perform movements once confirmed in spectator mode)');
    }

    sendDiscordEmbed(
      'Bot Connected',
      `**${BOT_USERNAME}** joined ${BOT_HOST} (v${BOT_VERSION})\nMode: ${bot.game?.gameMode || 'unknown'}`,
      SUCCESS_COLOR,
    );

    setupActivityCheck();

    // Start movement engine only if already in spectator
    if (isInSpectatorMode) {
      console.log('🎮 Already in spectator mode — starting movement engine');
      await sleep(500);
      startHeartbeat();
      scheduleNextAction();
    }

    // Send stats after 10s
    setTimeout(() => {
      if (canAct()) sendBotStats();
    }, 10000);

    setTimeout(() => {
      if (canAct()) checkPlayerCount();
    }, 3000);
  });

  // ---- ERROR ----
  bot.on('error', (err) => {
    // Stop ghost actions immediately
    botReady   = false;
    isBotOnline = false;

    const msg = err.message || String(err);
    console.error('❌ Bot error:', msg);

    const isNetworkError =
      msg.includes('ECONNRESET')   ||
      msg.includes('ECONNREFUSED') ||
      msg.includes('ETIMEDOUT')    ||
      msg.includes('timed out')    ||
      msg.includes('ENOTFOUND')    ||
      msg.includes('PartialReadError') ||
      msg.includes('Unexpected buffer end');

    if (isNetworkError) {
      sendDiscordEmbed('Network Error', `${msg}`, WARNING_COLOR);
      clearAllHandles();
      consecutiveFailures++;
      if (AUTO_REJOIN) scheduleReconnect();
    } else {
      sendDiscordEmbed('Bot Error', msg, ERROR_COLOR);
    }
  });

  // ---- END ----
  bot.on('end', async (reason) => {
    botReady   = false;
    isBotOnline = false;

    const r = reason || 'unknown';
    console.log(`🔌 Bot disconnected: ${r}`);

    await ensureTimeUnfrozen();
    clearAllHandles();
    consecutiveFailures++;

    sendDiscordEmbed('Bot Disconnected', `Reason: ${r}`, WARNING_COLOR);

    if (AUTO_REJOIN && !isShuttingDown) scheduleReconnect();
  });

  // ---- KICKED ----
  bot.on('kicked', async (reason) => {
    botReady   = false;
    isBotOnline = false;

    const reasonStr = typeof reason === 'object'
      ? JSON.stringify(reason)
      : String(reason);
    console.log(`⛔ Bot kicked: ${reasonStr}`);

    await ensureTimeUnfrozen();
    clearAllHandles();

    sendDiscordEmbed('Bot Kicked', `Reason: ${reasonStr}`, ERROR_COLOR);

    const isAfkKick =
      reasonStr.toLowerCase().includes('idle') ||
      reasonStr.toLowerCase().includes('afk')  ||
      reasonStr.toLowerCase().includes('terms');

    consecutiveFailures++;

    if (AUTO_REJOIN && !isShuttingDown) {
      if (isAfkKick) {
        console.log('🔄 AFK kick detected — waiting 30s before rejoin...');
        reconnectHandle = setTimeout(() => startBot(), 30000);
      } else {
        scheduleReconnect();
      }
    }
  });

  // ---- CHAT ----
  bot.on('chat', async (username, message) => {
    if (username === BOT_USERNAME) return;

    let trueUsername = username;
    let uuid         = null;

    if (bot && bot.players) {
      const player = Object.values(bot.players).find(
        p => p.username.replace(/^\./, '') === username.replace(/^\./, ''),
      );
      if (player) { trueUsername = player.username; uuid = player.uuid; }
    }

    sendPlayerMessage(trueUsername, message);

    if (dbConnected && MinecraftChat) {
      try {
        const skinUrl = await getOrCreatePlayerFace(trueUsername, uuid);
        const doc     = new MinecraftChat({ username: trueUsername, chat: message });
        await doc.save();
        io.emit('chatMessage', {
          username:  trueUsername,
          chat:      message,
          timestamp: doc.timestamp,
          skinUrl,
        });
      } catch (err) {
        console.error('❌ Chat save error:', err.message);
      }
    }
  });

  // ---- PLAYER JOINED ----
  bot.on('playerJoined', async (player) => {
    if (player.username === BOT_USERNAME) return;
    console.log(`👋 ${player.username} joined`);
    const skinUrl = await getOrCreatePlayerFace(player.username, player.uuid);
    player.skinUrl = skinUrl;

    if (CHAT_WEBHOOK) {
      axios.post(CHAT_WEBHOOK, { content: `📥 **${player.username}** joined.` }).catch(() => {});
    }

    io.emit('playerJoined', { username: player.username, skinUrl });
    setTimeout(checkPlayerCount, 1000);
    setTimeout(refreshNearbyPlayers, 2000);
  });

  // ---- PLAYER LEFT ----
  bot.on('playerLeft', (player) => {
    if (player.username === BOT_USERNAME) return;
    console.log(`👋 ${player.username} left`);

    if (CHAT_WEBHOOK) {
      axios.post(CHAT_WEBHOOK, { content: `📤 **${player.username}** left.` }).catch(() => {});
    }

    io.emit('playerLeft', { username: player.username });
    setTimeout(checkPlayerCount, 1000);
    setTimeout(refreshNearbyPlayers, 2000);
  });

  // ---- HEALTH (monitor only) ----
  bot.on('health', () => {
    // In spectator mode health isn't relevant, but we can log anomalies
    if (bot && bot.health !== undefined && bot.health <= 0 && !isInSpectatorMode) {
      console.log('💀 Bot health hit 0 (non-spectator?) — rejoining');
      consecutiveFailures++;
      scheduleReconnect();
    }
  });
}

// ============================================================================
// 📋 BOT STATS
// ============================================================================
function sendBotStats() {
  if (!canAct()) return;
  try {
    const uptime  = botStartTime ? Math.floor((Date.now() - botStartTime) / 1000) : 0;
    const h = Math.floor(uptime / 3600);
    const m = Math.floor((uptime % 3600) / 60);
    const s = uptime % 60;
    const pos = bot.entity
      ? `X:${Math.floor(bot.entity.position.x)} Y:${Math.floor(bot.entity.position.y)} Z:${Math.floor(bot.entity.position.z)}`
      : 'N/A';

    sendDiscordEmbed('Bot Status', `Report for **${BOT_USERNAME}**`, INFO_COLOR, [
      { name: 'Uptime',         value: `${h}h ${m}m ${s}s`,               inline: true },
      { name: 'Position',       value: pos,                                 inline: true },
      { name: 'Mode',           value: bot.game?.gameMode || 'N/A',         inline: true },
      { name: 'Memory',         value: `${(process.memoryUsage().rss / 1048576).toFixed(1)} MB`, inline: true },
      { name: 'Moves',          value: `${movementCount}`,                  inline: true },
      { name: 'Phase',          value: behaviorPhase,                       inline: true },
      { name: 'Spectator',      value: isInSpectatorMode ? '✅ Yes' : '❌ No', inline: true },
      { name: 'Time',           value: isTimeFrozen ? '⏸️ Frozen' : '▶️ Running', inline: true },
      { name: 'Players Online', value: `${getOnlinePlayersExcludingBot().length}`, inline: true },
    ]);
  } catch (err) {
    console.error('❌ sendBotStats error:', err.message);
  }
}

// ============================================================================
// 🌐 EXPRESS API ROUTES
// ============================================================================
app.get('/', (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'dashboard.html'));
});

app.get('/api/status', async (req, res) => {
  try {
    const payload = await getBotStatusPayload();
    res.json(payload);
  } catch (err) {
    console.error('❌ /api/status error:', err.message);
    res.status(500).json({ error: 'Internal Server Error' });
  }
});

app.get('/api/chat', async (req, res) => {
  if (!dbConnected || !MinecraftChat) {
    return res.json([]);
  }
  try {
    const { username, date, search } = req.query;
    const query = {};
    if (username) query.username = username;
    if (date) {
      const d0 = new Date(date); d0.setHours(0, 0, 0, 0);
      const d1 = new Date(date); d1.setHours(23, 59, 59, 999);
      query.timestamp = { $gte: d0, $lte: d1 };
    }
    if (search) query.chat = { $regex: search, $options: 'i' };

    const skip  = parseInt(req.query.skip,  10) || 0;
    const limit = parseInt(req.query.limit, 10) || 100;

    const messages = await MinecraftChat.find(query).sort({ timestamp: -1 }).skip(skip).limit(limit);
    const withFaces = await Promise.all(messages.map(async msg => {
      const skinUrl = await getOrCreatePlayerFace(msg.username, null);
      return { ...msg.toObject(), skinUrl };
    }));
    res.json(withFaces);
  } catch (err) {
    console.error('❌ /api/chat error:', err.message);
    res.status(500).json({ error: 'Internal Server Error' });
  }
});

app.get('/api/chat/usernames', async (req, res) => {
  if (!dbConnected || !MinecraftChat) return res.json([]);
  try {
    const usernames = await MinecraftChat.distinct('username');
    res.json(usernames);
  } catch (err) {
    console.error('❌ /api/chat/usernames error:', err.message);
    res.status(500).json({ error: 'Internal Server Error' });
  }
});

// Manual reconnect endpoint
app.post('/api/reconnect', (req, res) => {
  console.log('🔄 Manual reconnect triggered via API');
  res.json({ message: 'Reconnect initiated' });
  setTimeout(() => {
    consecutiveFailures = 0;
    startBot();
  }, 1000);
});

// Health check (for Render.com uptime)
app.get('/health', (req, res) => {
  res.json({
    status: 'ok',
    botOnline: isBotOnline,
    botReady,
    isSpectator: isInSpectatorMode,
    uptime: process.uptime(),
  });
});

// ============================================================================
// 🔌 SOCKET.IO
// ============================================================================
io.on('connection', (socket) => {
  console.log(`🔌 Dashboard client connected [${socket.id}]`);

  // Send current status immediately on connect
  getBotStatusPayload().then(payload => {
    socket.emit('botStatusUpdate', payload);
  }).catch(() => {});

  socket.on('disconnect', () => {
    console.log(`🔌 Dashboard client disconnected [${socket.id}]`);
  });
});

// Periodic status broadcast
setInterval(async () => {
  try {
    const payload = await getBotStatusPayload();
    io.emit('botStatusUpdate', payload);
  } catch (err) {
    console.error('❌ Socket.IO broadcast error:', err.message);
  }
}, SOCKET_UPDATE_MS);

// ============================================================================
// 🔁 RENDER.COM KEEP-ALIVE (self-ping to prevent spin-down on free tier)
// ============================================================================
function startSelfPing() {
  if (!SELF_PING) return;
  const selfUrl = process.env.RENDER_EXTERNAL_URL
    ? `${process.env.RENDER_EXTERNAL_URL}/health`
    : `http://localhost:${WEB_SERVER_PORT}/health`;

  setInterval(async () => {
    try {
      await axios.get(selfUrl, { timeout: 10000 });
      console.log(`🏓 Self-ping OK → ${selfUrl}`);
    } catch (err) {
      console.error(`❌ Self-ping failed: ${err.message}`);
    }
  }, KEEP_ALIVE_MS);
}

// ============================================================================
// 🛑 GRACEFUL SHUTDOWN
// ============================================================================
async function gracefulShutdown(signal) {
  console.log(`\n⚠️  ${signal} received — shutting down gracefully...`);
  isShuttingDown = true;
  botReady       = false;

  await ensureTimeUnfrozen();

  if (bot) {
    try {
      await sendDiscordEmbed('Bot Shutdown', `${BOT_USERNAME} shutting down (${signal})`, WARNING_COLOR);
      bot.quit('Shutdown');
    } catch (_) {}
  }

  clearAllHandles();

  setTimeout(() => {
    console.log('✅ Shutdown complete');
    process.exit(0);
  }, 2500);
}

process.on('SIGINT',  () => gracefulShutdown('SIGINT'));
process.on('SIGTERM', () => gracefulShutdown('SIGTERM'));

process.on('uncaughtException', (err) => {
  console.error('💥 Uncaught Exception:', err.message, err.stack);
  // Don't crash — just log and continue
});

process.on('unhandledRejection', (reason) => {
  console.error('💥 Unhandled Rejection:', reason);
});

// ============================================================================
// 🚀 BOOT SEQUENCE
// ============================================================================
async function boot() {
  console.log('='.repeat(60));
  console.log('  🍃 Leaf Dashboard — Minecraft AFK Bot');
  console.log(`  Host:    ${BOT_HOST}:${BOT_PORT}`);
  console.log(`  Bot:     ${BOT_USERNAME} (MC ${BOT_VERSION})`);
  console.log(`  Version: mineflayer 4.35.0`);
  console.log(`  Mode:    Spectator-only movement engine`);
  console.log('='.repeat(60));

  // Start web server first so Render health check passes
  await new Promise(resolve => {
    server.listen(WEB_SERVER_PORT, '0.0.0.0', () => {
      console.log(`🌐 Web server listening on port ${WEB_SERVER_PORT}`);
      resolve();
    });
  });

  // Connect database (non-blocking)
  connectDatabase().catch(() => {});

  // Self-ping for Render free tier
  startSelfPing();

  // Announce web server start
  sendDiscordEmbed(
    'Server Started',
    `Web monitoring on port ${WEB_SERVER_PORT}\nBot will connect to ${BOT_HOST}:${BOT_PORT}`,
    DEFAULT_COLOR,
  );

  // Small delay then start bot
  await sleep(2000);
  startBot();
}

boot();
