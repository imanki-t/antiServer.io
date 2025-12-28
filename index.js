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

// Load configuration
let config;
try {
  const configPath = path.join(__dirname, 'config.json');
  config = JSON.parse(fs.readFileSync(configPath, 'utf8'));
} catch (err) {
  console.error('❌ Failed to load config.json:', err.message);
  console.error('Please create a config.json file. See config.example.json for reference.');
  process.exit(1);
}

// Extract configuration
const BOT_HOST = process.env.BOT_HOST || config.bot.host;
const BOT_PORT = parseInt(process.env.BOT_PORT, 10) || config.bot.port;
const BOT_USERNAME = process.env.BOT_USERNAME || config.bot.username;
const BOT_VERSION = config.bot.version;
const DISCORD_WEBHOOK = process.env.DISCORD_WEBHOOK || config.webhooks.discord;
const CHAT_WEBHOOK = process.env.CHAT_WEBHOOK || config.webhooks.chat;
const MESSAGE_WEBHOOK = process.env.MESSAGE_WEBHOOK || config.webhooks.message;
const WEB_SERVER_PORT = process.env.PORT || config.server.port;
const MONGO_URI = process.env.MONGO_URI || config.database.mongoUri;

const RECONNECT_DELAY = config.intervals.reconnect;
const SOCKET_IO_UPDATE_INTERVAL = config.intervals.socketUpdate;
const ACTIVITY_CHECK_INTERVAL = config.intervals.activityCheck;

const ONE_HOUR = config.timeLimits.oneHour;
const FIFTEEN_SECONDS = config.timeLimits.fifteenSeconds;

const DEFAULT_EMBED_COLOR = config.embedColors.default;
const SUCCESS_EMBED_COLOR = config.embedColors.success;
const WARNING_EMBED_COLOR = config.embedColors.warning;
const ERROR_EMBED_COLOR = config.embedColors.error;
const INFO_EMBED_COLOR = config.embedColors.info;
const CHAT_EMBED_COLOR = config.embedColors.chat;

const FACES = config.faces;

const AUTO_TIME_FREEZE = config.features.autoTimeFreeze;
const ANTI_AFK = config.features.antiAFK;
const AUTO_REJOIN = config.features.autoRejoin;

const botOptions = {
  host: BOT_HOST,
  port: BOT_PORT,
  username: BOT_USERNAME,
  version: BOT_VERSION,
  connectTimeout: null,
};

let bot = null;
let reconnectTimeout = null;
let actionSchedulerTimeout = null;
let activityCheckTimeout = null;
let botStartTime = null;
let movementCount = 0;
let isBotOnline = false;
let lastOnlineTime = null;
let currentServerHost = BOT_HOST;
let currentServerPort = BOT_PORT;
let lastCpuUsage = process.cpuUsage();
let nextDotFaceIndex = 0;
let isTimeFrozen = false;
let otherPlayersOnline = 0;
let isShuttingDown = false;
let consecutiveFailures = 0;
let currentAction = null;
let actionInProgress = false;

// New tracking variables for advanced behavior
let behaviorPhase = 'active'; // active, moderate, idle
let nearbyPlayers = [];
let lastPlayerCheckTime = 0;
let mistakeCounter = 0;
let isInSpectatorMode = false;

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

mongoose.connect(MONGO_URI)
  .then(() => console.log('✅ MongoDB connected'))
  .catch(err => console.error('❌ MongoDB connection error:', err));

const chatSchema = new mongoose.Schema({
  username: String,
  chat: String,
  timestamp: { type: Date, default: Date.now }
});
const MinecraftChat = mongoose.model('MinecraftChat', chatSchema);

const playerFaceSchema = new mongoose.Schema({
  username: { type: String, unique: true },
  face: String,
  isCustom: { type: Boolean, default: false },
  lastUpdated: { type: Date, default: Date.now }
});
const PlayerFace = mongoose.model('PlayerFace', playerFaceSchema);

function clearAllIntervals() {
  if (actionSchedulerTimeout) {
    clearTimeout(actionSchedulerTimeout);
    actionSchedulerTimeout = null;
  }
  if (reconnectTimeout) {
    clearTimeout(reconnectTimeout);
    reconnectTimeout = null;
  }
  if (activityCheckTimeout) {
    clearInterval(activityCheckTimeout);
    activityCheckTimeout = null;
  }
  actionInProgress = false;
  currentAction = null;
}

function resetBotState() {
  isBotOnline = false;
  botStartTime = null;
  movementCount = 0;
  isTimeFrozen = false;
  otherPlayersOnline = 0;
  behaviorPhase = 'active';
  nearbyPlayers = [];
  mistakeCounter = 0;
  isInSpectatorMode = false;
}

async function sendDiscordEmbed(title, description, color = DEFAULT_EMBED_COLOR, fields = []) {
  if (!DISCORD_WEBHOOK) return;
  try {
    await axios.post(DISCORD_WEBHOOK, {
      embeds: [{ title, description, color, fields, timestamp: new Date().toISOString() }],
    });
  } catch (err) {
    console.error('❌ Discord Webhook Error:', err.message);
  }
}

async function sendChatEmbed(title, description, color = SUCCESS_EMBED_COLOR, fields = []) {
  if (!CHAT_WEBHOOK) return;
  try {
    await axios.post(CHAT_WEBHOOK, {
      embeds: [{ title, description, color, fields, timestamp: new Date().toISOString() }],
    });
  } catch (err) {
    console.error('❌ Chat Webhook Error:', err.message);
  }
}

async function sendPlayerMessage(username, message) {
  if (username === botOptions.username || !MESSAGE_WEBHOOK) return;
  try {
    await axios.post(MESSAGE_WEBHOOK, {
      content: `💬 **${username}**: ${message}`
    });
  } catch (err) {
    console.error('❌ Message Webhook Error:', err.message);
  }
}

function getOnlinePlayersExcludingBot() {
  if (!bot || !bot.players || !isBotOnline) {
    return [];
  }
  return Object.values(bot.players).filter(p => p.username !== botOptions.username);
}

// Check for spectator mode
function updateSpectatorMode() {
  if (!bot || !bot.game) return;
  isInSpectatorMode = bot.game.gameMode === 'spectator' || bot.game.gameMode === 3;
}

// Get nearby players within render distance
function getNearbyPlayers(radius = 50) {
  if (!bot || !bot.entity || !bot.players) return [];
  
  const botPos = bot.entity.position;
  const nearby = [];
  
  Object.values(bot.players).forEach(player => {
    if (player.username === botOptions.username) return;
    if (!player.entity) return;
    
    const distance = botPos.distanceTo(player.entity.position);
    if (distance <= radius) {
      nearby.push({
        username: player.username,
        distance: distance,
        position: player.entity.position
      });
    }
  });
  
  return nearby;
}

// Update nearby players periodically
function checkNearbyPlayers() {
  if (!bot || !isBotOnline) return;
  
  const now = Date.now();
  if (now - lastPlayerCheckTime > 3000) {
    nearbyPlayers = getNearbyPlayers();
    lastPlayerCheckTime = now;
  }
}

// Determine behavior phase based on uptime
function updateBehaviorPhase() {
  if (!botStartTime) return;
  
  const uptime = (Date.now() - botStartTime) / 1000 / 60; // minutes
  
  if (uptime < 10) {
    behaviorPhase = 'active';
  } else if (uptime < 30) {
    behaviorPhase = 'moderate';
  } else {
    behaviorPhase = 'idle';
  }
}

async function freezeTime() {
  if (!bot || !isBotOnline || isTimeFrozen) return;
  try {
    bot.chat('/tick freeze');
    isTimeFrozen = true;
    console.log('⏸️  Time frozen - Bot is alone on the server');
    await sendDiscordEmbed('Time Control', 'Time frozen - Bot is the only player online', INFO_EMBED_COLOR);
  } catch (err) {
    console.error('❌ Error freezing time:', err.message);
  }
}

async function unfreezeTime() {
  if (!bot || !isBotOnline || !isTimeFrozen) return;
  try {
    bot.chat('/tick unfreeze');
    isTimeFrozen = false;
    console.log('▶️  Time unfrozen - Other players joined');
    await sendDiscordEmbed('Time Control', 'Time unfrozen - Other players online', INFO_EMBED_COLOR);
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
      await new Promise(resolve => setTimeout(resolve, 1000));
    } catch (err) {
      console.error('❌ Error ensuring time unfrozen:', err.message);
    }
  }
}

function checkPlayerCount() {
  if (!bot || !AUTO_TIME_FREEZE || !isBotOnline) return;

  const players = getOnlinePlayersExcludingBot();
  otherPlayersOnline = players.length;

  if (otherPlayersOnline === 0 && !isTimeFrozen) {
    setTimeout(() => freezeTime(), 2000);
  } else if (otherPlayersOnline > 0 && isTimeFrozen) {
    unfreezeTime();
  }
}

function sendPlayerList() {
  if (!bot || !bot.players || !isBotOnline) return;
}

function sendBotStats() {
  if (!bot || !isBotOnline) return;
  try {
    const uptime = botStartTime ? Math.floor((Date.now() - botStartTime) / 1000) : 0;
    const hours = Math.floor(uptime / 3600);
    const minutes = Math.floor((uptime % 3600) / 60);
    const seconds = uptime % 60;
    const uptimeStr = `${hours}h ${minutes}m ${seconds}s`;
    
    const position = bot.entity ? bot.entity.position : { x: 0, y: 0, z: 0 };
    const posStr = `X: ${Math.floor(position.x)}, Y: ${Math.floor(position.y)}, Z: ${Math.floor(position.z)}`;
    
    const memoryUsage = process.memoryUsage();
    const memoryStr = `${Math.round(memoryUsage.rss / 1024 / 1024 * 100) / 100} MB`;
    const gameModeDisplay = bot?.game?.gameMode || 'N/A';
    const onlinePlayersCount = getOnlinePlayersExcludingBot().length;

    sendDiscordEmbed('Bot Status Report', `Status report for ${botOptions.username}`, INFO_EMBED_COLOR, [
      { name: 'Uptime', value: uptimeStr, inline: true },
      { name: 'Position', value: posStr, inline: true },
      { name: 'Game Mode', value: gameModeDisplay, inline: true },
      { name: 'Memory Usage', value: memoryStr, inline: true },
      { name: 'Movement Count', value: `${movementCount} moves`, inline: true },
      { name: 'Players Online', value: `${onlinePlayersCount} (excluding bot)`, inline: true },
      { name: 'Time Status', value: isTimeFrozen ? '⏸️ Frozen' : '▶️ Running', inline: true },
      { name: 'Behavior Phase', value: behaviorPhase, inline: true }
    ]);
  } catch (err) {
    console.error('❌ Error sending bot stats:', err.message);
  }
}

// ============================================================================
// 🎮 ENHANCED ACTION-BASED SCHEDULER - 40+ ACTIONS WITH ADVANCED BEHAVIOR
// ============================================================================

const ACTIONS = {
  // ========== MOVEMENT ACTIONS (Spectator-friendly) ==========
  WALK_SHORT: { weight: 12, type: 'movement', category: 'basic' },
  WALK_LONG: { weight: 8, type: 'movement', category: 'basic' },
  WANDER: { weight: 7, type: 'movement', category: 'basic' },
  SPRINT_TRAVEL: { weight: 4, type: 'movement', category: 'basic' },
  JUMP_MOVE: { weight: 3, type: 'movement', category: 'basic' },
  
  // New movement variations
  DIAGONAL_WALK: { weight: 5, type: 'movement', category: 'varied' },
  ZIGZAG_MOVEMENT: { weight: 4, type: 'movement', category: 'varied' },
  CIRCLE_WALK: { weight: 3, type: 'movement', category: 'varied' },
  BACKWARDS_WALK: { weight: 3, type: 'movement', category: 'varied' },
  STRAFE_LEFT_RIGHT: { weight: 4, type: 'movement', category: 'varied' },
  
  // ========== LOOKING ACTIONS ==========
  LOOK_AROUND: { weight: 10, type: 'look', category: 'basic' },
  LOOK_SLOWLY: { weight: 7, type: 'look', category: 'basic' },
  LOOK_QUICK: { weight: 4, type: 'look', category: 'basic' },
  
  // New looking variations
  LOOK_UP_DOWN: { weight: 5, type: 'look', category: 'varied' },
  LOOK_AT_GROUND: { weight: 3, type: 'look', category: 'varied' },
  LOOK_AT_SKY: { weight: 3, type: 'look', category: 'varied' },
  SCAN_HORIZON: { weight: 4, type: 'look', category: 'varied' },
  QUICK_HEAD_TURN: { weight: 3, type: 'look', category: 'varied' },
  LOOK_BEHIND: { weight: 3, type: 'look', category: 'varied' },
  
  // ========== IDLE ACTIONS ==========
  IDLE_SHORT: { weight: 8, type: 'idle', category: 'basic' },
  IDLE_MEDIUM: { weight: 6, type: 'idle', category: 'basic' },
  IDLE_LONG: { weight: 4, type: 'idle', category: 'basic' },
  
  // New idle variations
  IDLE_WITH_MICRO_LOOK: { weight: 6, type: 'idle', category: 'varied' },
  COMPLETE_STILLNESS: { weight: 5, type: 'idle', category: 'deep' },
  AFK_SIMULATION: { weight: 3, type: 'idle', category: 'deep' },
  
  // ========== INTERACTIVE ACTIONS ==========
  HOTBAR_SWITCH: { weight: 5, type: 'interaction', category: 'basic' },
  SWING_ARM: { weight: 4, type: 'interaction', category: 'basic' },
  SNEAK: { weight: 3, type: 'interaction', category: 'basic' },
  JUMP_PLACE: { weight: 2, type: 'interaction', category: 'basic' },
  
  // New interaction variations
  RAPID_HOTBAR_SCROLL: { weight: 3, type: 'interaction', category: 'varied' },
  SNEAK_WALK: { weight: 3, type: 'interaction', category: 'varied' },
  SNEAK_LOOK: { weight: 3, type: 'interaction', category: 'varied' },
  DOUBLE_JUMP: { weight: 2, type: 'interaction', category: 'varied' },
  TRIPLE_JUMP: { weight: 1, type: 'interaction', category: 'varied' },
  CROUCH_SPAM: { weight: 2, type: 'interaction', category: 'varied' },
  
  // ========== BLOCK INTERACTION ACTIONS ==========
  LOOK_AT_BLOCK: { weight: 4, type: 'block', category: 'interaction' },
  APPROACH_BLOCK: { weight: 3, type: 'block', category: 'interaction' },
  RIGHT_CLICK_AIR: { weight: 3, type: 'block', category: 'interaction' },
  LEFT_CLICK_AIR: { weight: 2, type: 'block', category: 'interaction' },
  SWING_AT_BLOCK: { weight: 2, type: 'block', category: 'interaction' },
  
  // ========== HUMAN MISTAKE ACTIONS ==========
  WALK_INTO_WALL: { weight: 2, type: 'mistake', category: 'human' },
  WRONG_DIRECTION: { weight: 2, type: 'mistake', category: 'human' },
  SUDDEN_STOP: { weight: 3, type: 'mistake', category: 'human' },
  ACCIDENTAL_JUMP: { weight: 2, type: 'mistake', category: 'human' },
  HESITATION: { weight: 3, type: 'mistake', category: 'human' },
  OVERCORRECTION: { weight: 2, type: 'mistake', category: 'human' },
  
  // ========== PLAYER-AWARE ACTIONS ==========
  REACT_TO_PLAYER: { weight: 8, type: 'social', category: 'player-aware' },
  LOOK_AT_PLAYER: { weight: 6, type: 'social', category: 'player-aware' },
  FOLLOW_PLAYER: { weight: 3, type: 'social', category: 'player-aware' },
  AVOID_PLAYER: { weight: 2, type: 'social', category: 'player-aware' },
  CURIOUS_APPROACH: { weight: 3, type: 'social', category: 'player-aware' },
  
  // ========== ADVANCED COMBINATIONS ==========
  JUMP_SPRINT_COMBO: { weight: 3, type: 'combo', category: 'advanced' },
  SNEAK_JUMP_COMBO: { weight: 2, type: 'combo', category: 'advanced' },
  STRAFE_LOOK_COMBO: { weight: 3, type: 'combo', category: 'advanced' },
  WALK_LOOK_COMBO: { weight: 4, type: 'combo', category: 'advanced' },
  
  // ========== SPECTATOR-SPECIFIC ACTIONS ==========
  SPECTATOR_FLOAT: { weight: 2, type: 'spectator', category: 'mode-specific' },
  SPECTATOR_PHASE: { weight: 1, type: 'spectator', category: 'mode-specific' },
};

const TOTAL_WEIGHT = Object.values(ACTIONS).reduce((sum, action) => sum + action.weight, 0);

function getRandomDelay(min, max) {
  const baseDelay = min + Math.random() * (max - min);
  const variance = baseDelay * 0.3 * (Math.random() - 0.5);
  const spike = Math.random() < 0.1 ? Math.random() * 1000 : 0;
  return Math.floor(baseDelay + variance + spike);
}

function selectRandomAction() {
  // Adjust weights based on context
  let adjustedActions = { ...ACTIONS };
  
  // If players nearby, increase social actions
  if (nearbyPlayers.length > 0) {
    Object.keys(adjustedActions).forEach(key => {
      if (adjustedActions[key].category === 'player-aware') {
        adjustedActions[key] = { ...adjustedActions[key], weight: adjustedActions[key].weight * 3 };
      }
    });
  }
  
  // Adjust based on behavior phase
  if (behaviorPhase === 'idle') {
    Object.keys(adjustedActions).forEach(key => {
      if (adjustedActions[key].type === 'idle') {
        adjustedActions[key] = { ...adjustedActions[key], weight: adjustedActions[key].weight * 2 };
      }
      if (adjustedActions[key].type === 'movement') {
        adjustedActions[key] = { ...adjustedActions[key], weight: adjustedActions[key].weight * 0.5 };
      }
    });
  } else if (behaviorPhase === 'active') {
    Object.keys(adjustedActions).forEach(key => {
      if (adjustedActions[key].type === 'movement') {
        adjustedActions[key] = { ...adjustedActions[key], weight: adjustedActions[key].weight * 1.5 };
      }
    });
  }
  
  // Occasionally inject mistakes (5% chance)
  if (Math.random() < 0.05) {
    const mistakes = Object.keys(adjustedActions).filter(k => adjustedActions[k].category === 'human');
    if (mistakes.length > 0) {
      return mistakes[Math.floor(Math.random() * mistakes.length)];
    }
  }
  
  // Calculate total adjusted weight
  const totalAdjustedWeight = Object.values(adjustedActions).reduce((sum, action) => sum + action.weight, 0);
  
  let random = Math.random() * totalAdjustedWeight;
  
  for (const [actionName, actionData] of Object.entries(adjustedActions)) {
    random -= actionData.weight;
    if (random <= 0) {
      return actionName;
    }
  }
  
  return 'LOOK_AROUND';
}

// ========== ACTION IMPLEMENTATIONS ==========

// Basic Movement Actions
async function executeWalkShort() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const directions = ['forward', 'back', 'left', 'right'];
  const direction = directions[Math.floor(Math.random() * directions.length)];
  
  bot.setControlState(direction, true);
  
  if (Math.random() < 0.2) {
    bot.setControlState('jump', true);
  }
  
  const duration = getRandomDelay(300, 1200);
  
  await new Promise(resolve => setTimeout(resolve, duration));
  
  if (bot) {
    bot.clearControlStates();
  }
  
  movementCount++;
}

async function executeWalkLong() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const directions = ['forward', 'back', 'left', 'right'];
  const direction = directions[Math.floor(Math.random() * directions.length)];
  
  bot.setControlState(direction, true);
  
  if (Math.random() < 0.3) {
    bot.setControlState('sprint', true);
  }
  
  const duration = getRandomDelay(1500, 4000);
  
  const jumpInterval = setInterval(() => {
    if (bot && Math.random() < 0.15) {
      bot.setControlState('jump', true);
      setTimeout(() => {
        if (bot) bot.setControlState('jump', false);
      }, 300);
    }
  }, 800);
  
  await new Promise(resolve => setTimeout(resolve, duration));
  
  clearInterval(jumpInterval);
  
  if (bot) {
    bot.clearControlStates();
  }
  
  movementCount++;
}

async function executeWander() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const totalDuration = getRandomDelay(3000, 8000);
  const startTime = Date.now();
  
  while (Date.now() - startTime < totalDuration && bot && isBotOnline) {
    const directions = ['forward', 'back', 'left', 'right'];
    const direction = directions[Math.floor(Math.random() * directions.length)];
    
    bot.clearControlStates();
    bot.setControlState(direction, true);
    
    if (Math.random() < 0.4) {
      bot.setControlState('sprint', true);
    }
    
    if (Math.random() < 0.3) {
      const yaw = Math.random() * Math.PI * 2;
      const pitch = (Math.random() - 0.5) * Math.PI / 4;
      bot.look(yaw, pitch, true);
    }
    
    const segmentDuration = getRandomDelay(500, 2000);
    await new Promise(resolve => setTimeout(resolve, segmentDuration));
    
    if (Math.random() < 0.2) {
      bot.setControlState('jump', true);
      await new Promise(resolve => setTimeout(resolve, 300));
      if (bot) bot.setControlState('jump', false);
    }
  }
  
  if (bot) {
    bot.clearControlStates();
  }
  
  movementCount++;
}

async function executeSprintTravel() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const yaw = Math.random() * Math.PI * 2;
  bot.look(yaw, 0, true);
  
  bot.setControlState('forward', true);
  bot.setControlState('sprint', true);
  
  const duration = getRandomDelay(2000, 6000);
  
  const jumpInterval = setInterval(() => {
    if (bot && Math.random() < 0.25) {
      bot.setControlState('jump', true);
    }
  }, 1000);
  
  await new Promise(resolve => setTimeout(resolve, duration));
  
  clearInterval(jumpInterval);
  
  if (bot) {
    bot.clearControlStates();
  }
  
  movementCount++;
}

async function executeJumpMove() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  if (Math.random() < 0.5) {
    const directions = ['forward', 'back', 'left', 'right'];
    const direction = directions[Math.floor(Math.random() * directions.length)];
    bot.setControlState(direction, true);
  }
  
  bot.setControlState('jump', true);
  
  await new Promise(resolve => setTimeout(resolve, 500));
  
  if (bot) {
    bot.clearControlStates();
  }
  
  movementCount++;
}

// New Movement Variations
async function executeDiagonalWalk() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const combos = [
    ['forward', 'left'],
    ['forward', 'right'],
    ['back', 'left'],
    ['back', 'right']
  ];
  
  const combo = combos[Math.floor(Math.random() * combos.length)];
  
  combo.forEach(dir => bot.setControlState(dir, true));
  
  const duration = getRandomDelay(800, 2500);
  await new Promise(resolve => setTimeout(resolve, duration));
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeZigzagMovement() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const iterations = 3 + Math.floor(Math.random() * 3);
  
  for (let i = 0; i < iterations && bot && isBotOnline; i++) {
    bot.clearControlStates();
    
    bot.setControlState('forward', true);
    bot.setControlState(i % 2 === 0 ? 'left' : 'right', true);
    
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(400, 800)));
  }
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeCircleWalk() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const duration = getRandomDelay(3000, 6000);
  const startTime = Date.now();
  
  bot.setControlState('forward', true);
  
  while (Date.now() - startTime < duration && bot && isBotOnline) {
    const currentYaw = bot.entity.yaw;
    const newYaw = currentYaw + (Math.PI / 180) * 5; // 5 degrees per step
    bot.look(newYaw, 0, true);
    
    await new Promise(resolve => setTimeout(resolve, 100));
  }
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeBackwardsWalk() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.setControlState('back', true);
  
  const duration = getRandomDelay(1000, 3000);
  await new Promise(resolve => setTimeout(resolve, duration));
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeStrafeLeftRight() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const iterations = 2 + Math.floor(Math.random() * 3);
  
  for (let i = 0; i < iterations && bot && isBotOnline; i++) {
    bot.clearControlStates();
    bot.setControlState(i % 2 === 0 ? 'left' : 'right', true);
    
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(500, 1200)));
  }
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

// Looking Actions
async function executeLookAround() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const numLooks = 1 + Math.floor(Math.random() * 3);
  
  for (let i = 0; i < numLooks; i++) {
    if (!bot || !isBotOnline) break;
    
    const yaw = Math.random() * Math.PI * 2;
    const pitch = (Math.random() - 0.5) * Math.PI / 2;
    bot.look(yaw, pitch, true);
    
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(300, 1000)));
  }
}

async function executeLookSlowly() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const currentYaw = bot.entity.yaw;
  const currentPitch = bot.entity.pitch;
  
  const targetYaw = currentYaw + (Math.random() - 0.5) * Math.PI;
  const targetPitch = (Math.random() - 0.5) * Math.PI / 3;
  
  const steps = 5 + Math.floor(Math.random() * 5);
  for (let i = 0; i <= steps; i++) {
    if (!bot || !isBotOnline) break;
    
    const progress = i / steps;
    const yaw = currentYaw + (targetYaw - currentYaw) * progress;
    const pitch = currentPitch + (targetPitch - currentPitch) * progress;
    
    bot.look(yaw, pitch, true);
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(50, 150)));
  }
}

async function executeLookQuick() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const yaw = Math.random() * Math.PI * 2;
  const pitch = (Math.random() - 0.5) * Math.PI / 4;
  
  bot.look(yaw, pitch, false);
}

// New Looking Variations
async function executeLookUpDown() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const currentYaw = bot.entity.yaw;
  
  // Look up
  bot.look(currentYaw, -Math.PI / 3, true);
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(500, 1200)));
  
  // Look down
  if (bot && isBotOnline) {
    bot.look(currentYaw, Math.PI / 4, true);
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(500, 1200)));
  }
  
  // Return to normal
  if (bot && isBotOnline) {
    bot.look(currentYaw, 0, true);
  }
}

async function executeLookAtGround() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const currentYaw = bot.entity.yaw;
  bot.look(currentYaw, Math.PI / 3, true);
  
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(1000, 3000)));
}

async function executeLookAtSky() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const currentYaw = bot.entity.yaw;
  bot.look(currentYaw, -Math.PI / 2.5, true);
  
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(1000, 3000)));
}

async function executeScanHorizon() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const currentYaw = bot.entity.yaw;
  const sweepRange = Math.PI * 0.75;
  const steps = 8;
  
  for (let i = 0; i <= steps && bot && isBotOnline; i++) {
    const progress = i / steps;
    const yaw = currentYaw - sweepRange / 2 + sweepRange * progress;
    bot.look(yaw, 0, true);
    
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(200, 500)));
  }
}

async function executeQuickHeadTurn() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const currentYaw = bot.entity.yaw;
  const turnAmount = (Math.random() - 0.5) * Math.PI;
  
  bot.look(currentYaw + turnAmount, 0, false);
  await new Promise(resolve => setTimeout(resolve, 100));
}

async function executeLookBehind() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const currentYaw = bot.entity.yaw;
  bot.look(currentYaw + Math.PI, 0, true);
  
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(800, 2000)));
  
  if (bot && isBotOnline) {
    bot.look(currentYaw, 0, true);
  }
}

// Idle Actions
async function executeIdleShort() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.clearControlStates();
  const duration = getRandomDelay(500, 2000);
  await new Promise(resolve => setTimeout(resolve, duration));
}

async function executeIdleMedium() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.clearControlStates();
  const duration = getRandomDelay(2000, 5000);
  
  const lookInterval = setInterval(() => {
    if (bot && Math.random() < 0.3) {
      const yaw = bot.entity.yaw + (Math.random() - 0.5) * Math.PI / 4;
      const pitch = (Math.random() - 0.5) * Math.PI / 6;
      bot.look(yaw, pitch, true);
    }
  }, 1000);
  
  await new Promise(resolve => setTimeout(resolve, duration));
  clearInterval(lookInterval);
}

async function executeIdleLong() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.clearControlStates();
  const duration = getRandomDelay(5000, 12000);
  await new Promise(resolve => setTimeout(resolve, duration));
}

// New Idle Variations
async function executeIdleWithMicroLook() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.clearControlStates();
  const duration = getRandomDelay(3000, 8000);
  const startTime = Date.now();
  
  while (Date.now() - startTime < duration && bot && isBotOnline) {
    if (Math.random() < 0.1) {
      const currentYaw = bot.entity.yaw;
      const currentPitch = bot.entity.pitch;
      const microYaw = currentYaw + (Math.random() - 0.5) * 0.1;
      const microPitch = currentPitch + (Math.random() - 0.5) * 0.1;
      bot.look(microYaw, microPitch, true);
    }
    
    await new Promise(resolve => setTimeout(resolve, 500));
  }
}

async function executeCompleteStillness() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.clearControlStates();
  const duration = getRandomDelay(20000, 40000); // 20-40 seconds
  await new Promise(resolve => setTimeout(resolve, duration));
}

async function executeAfkSimulation() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.clearControlStates();
  const duration = getRandomDelay(30000, 60000); // 30-60 seconds
  
  console.log('🎭 Simulating AFK behavior for', Math.floor(duration / 1000), 'seconds');
  
  await new Promise(resolve => setTimeout(resolve, duration));
}

// Interactive Actions
async function executeHotbarSwitch() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  try {
    const currentSlot = bot.quickBarSlot;
    const numSwitches = 1 + Math.floor(Math.random() * 3);
    
    for (let i = 0; i < numSwitches; i++) {
      if (!bot || !isBotOnline) break;
      
      let newSlot = Math.floor(Math.random() * 9);
      if (newSlot === currentSlot) {
        newSlot = (newSlot + 1) % 9;
      }
      
      bot.setQuickBarSlot(newSlot);
      await new Promise(resolve => setTimeout(resolve, getRandomDelay(100, 500)));
    }
  } catch (err) {
    // Ignore hotbar errors
  }
}

async function executeSwingArm() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const numSwings = 1 + Math.floor(Math.random() * 3);
  
  for (let i = 0; i < numSwings; i++) {
    if (!bot || !isBotOnline) break;
    
    bot.swingArm('right');
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(100, 400)));
  }
  
  movementCount++;
}

async function executeSneak() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.setControlState('sneak', true);
  
  const duration = getRandomDelay(500, 2500);
  
  if (Math.random() < 0.4) {
    const directions = ['forward', 'back', 'left', 'right'];
    const direction = directions[Math.floor(Math.random() * directions.length)];
    bot.setControlState(direction, true);
  }
  
  await new Promise(resolve => setTimeout(resolve, duration));
  
  if (bot) {
    bot.clearControlStates();
  }
  
  movementCount++;
}

async function executeJumpPlace() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.setControlState('jump', true);
  bot.swingArm('right');
  
  await new Promise(resolve => setTimeout(resolve, 500));
  
  if (bot) {
    bot.clearControlStates();
  }
  
  movementCount++;
}

// New Interactive Variations
async function executeRapidHotbarScroll() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  try {
    for (let i = 0; i < 9 && bot && isBotOnline; i++) {
      bot.setQuickBarSlot(i);
      await new Promise(resolve => setTimeout(resolve, getRandomDelay(50, 150)));
    }
  } catch (err) {
    // Ignore
  }
}

async function executeSneakWalk() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.setControlState('sneak', true);
  bot.setControlState('forward', true);
  
  const duration = getRandomDelay(2000, 5000);
  await new Promise(resolve => setTimeout(resolve, duration));
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeSneakLook() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.setControlState('sneak', true);
  
  const numLooks = 2 + Math.floor(Math.random() * 3);
  for (let i = 0; i < numLooks && bot && isBotOnline; i++) {
    const yaw = Math.random() * Math.PI * 2;
    const pitch = (Math.random() - 0.5) * Math.PI / 3;
    bot.look(yaw, pitch, true);
    
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(500, 1200)));
  }
  
  if (bot) bot.clearControlStates();
}

async function executeDoubleJump() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.setControlState('jump', true);
  await new Promise(resolve => setTimeout(resolve, 300));
  
  if (bot) bot.setControlState('jump', false);
  await new Promise(resolve => setTimeout(resolve, 200));
  
  if (bot) bot.setControlState('jump', true);
  await new Promise(resolve => setTimeout(resolve, 300));
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeTripleJump() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  for (let i = 0; i < 3 && bot && isBotOnline; i++) {
    bot.setControlState('jump', true);
    await new Promise(resolve => setTimeout(resolve, 300));
    bot.setControlState('jump', false);
    await new Promise(resolve => setTimeout(resolve, 200));
  }
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeCrouchSpam() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const iterations = 3 + Math.floor(Math.random() * 5);
  
  for (let i = 0; i < iterations && bot && isBotOnline; i++) {
    bot.setControlState('sneak', true);
    await new Promise(resolve => setTimeout(resolve, 150));
    bot.setControlState('sneak', false);
    await new Promise(resolve => setTimeout(resolve, 150));
  }
  
  if (bot) bot.clearControlStates();
}

// Block Interaction Actions
async function executeLookAtBlock() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  try {
    const botPos = bot.entity.position;
    const blockPos = botPos.offset(
      Math.floor(Math.random() * 10) - 5,
      Math.floor(Math.random() * 3) - 1,
      Math.floor(Math.random() * 10) - 5
    );
    
    const yaw = Math.atan2(-blockPos.x + botPos.x, blockPos.z - botPos.z);
    const distance = botPos.distanceTo(blockPos);
    const pitch = Math.atan2(blockPos.y - botPos.y, distance);
    
    bot.look(yaw, pitch, true);
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(1000, 3000)));
  } catch (err) {
    // Ignore
  }
}

async function executeApproachBlock() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  try {
    const botPos = bot.entity.position;
    const targetPos = botPos.offset(
      Math.floor(Math.random() * 5) - 2,
      0,
      Math.floor(Math.random() * 5) - 2
    );
    
    const yaw = Math.atan2(-targetPos.x + botPos.x, targetPos.z - botPos.z);
    bot.look(yaw, 0, true);
    
    bot.setControlState('forward', true);
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(1000, 2500)));
    
    if (bot) bot.clearControlStates();
    movementCount++;
  } catch (err) {
    if (bot) bot.clearControlStates();
  }
}

async function executeRightClickAir() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  try {
    bot.activateItem();
    await new Promise(resolve => setTimeout(resolve, 300));
  } catch (err) {
    // Ignore
  }
}

async function executeLeftClickAir() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.swingArm('right');
  await new Promise(resolve => setTimeout(resolve, 200));
  movementCount++;
}

async function executeSwingAtBlock() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const numSwings = 2 + Math.floor(Math.random() * 4);
  
  for (let i = 0; i < numSwings && bot && isBotOnline; i++) {
    bot.swingArm('right');
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(200, 500)));
  }
  
  movementCount++;
}

// Human Mistake Actions
async function executeWalkIntoWall() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  console.log('🤦 Making human mistake: walking into wall');
  
  bot.setControlState('forward', true);
  const duration = getRandomDelay(1000, 2500);
  await new Promise(resolve => setTimeout(resolve, duration));
  
  if (bot) bot.clearControlStates();
  
  // Pause as if confused
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(500, 1500)));
  
  movementCount++;
  mistakeCounter++;
}

async function executeWrongDirection() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  console.log('🤦 Making human mistake: wrong direction');
  
  // Start moving in one direction
  bot.setControlState('forward', true);
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(500, 1000)));
  
  // Suddenly realize and change direction
  if (bot) {
    bot.clearControlStates();
    const yaw = bot.entity.yaw + Math.PI;
    bot.look(yaw, 0, false);
    bot.setControlState('forward', true);
    
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(800, 1500)));
  }
  
  if (bot) bot.clearControlStates();
  movementCount++;
  mistakeCounter++;
}

async function executeSuddenStop() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  console.log('🤦 Making human mistake: sudden stop');
  
  bot.setControlState('forward', true);
  bot.setControlState('sprint', true);
  
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(1000, 2000)));
  
  // Sudden stop
  if (bot) bot.clearControlStates();
  
  // Pause
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(1000, 3000)));
  
  movementCount++;
  mistakeCounter++;
}

async function executeAccidentalJump() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  console.log('🤦 Making human mistake: accidental jump');
  
  // Random jump at inappropriate time
  bot.setControlState('jump', true);
  await new Promise(resolve => setTimeout(resolve, 300));
  
  if (bot) bot.clearControlStates();
  
  mistakeCounter++;
}

async function executeHesitation() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  console.log('🤦 Making human mistake: hesitation');
  
  // Start moving
  bot.setControlState('forward', true);
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(300, 700)));
  
  // Stop
  if (bot) bot.clearControlStates();
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(500, 1200)));
  
  // Continue
  if (bot) bot.setControlState('forward', true);
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(500, 1000)));
  
  if (bot) bot.clearControlStates();
  
  movementCount++;
  mistakeCounter++;
}

async function executeOvercorrection() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  console.log('🤦 Making human mistake: overcorrection');
  
  const currentYaw = bot.entity.yaw;
  
  // Turn too far
  bot.look(currentYaw + Math.PI / 2, 0, true);
  await new Promise(resolve => setTimeout(resolve, 300));
  
  // Correct back
  if (bot) bot.look(currentYaw - Math.PI / 6, 0, true);
  await new Promise(resolve => setTimeout(resolve, 300));
  
  // Final adjustment
  if (bot) bot.look(currentYaw, 0, true);
  
  mistakeCounter++;
}

// Player-Aware Actions
async function executeReactToPlayer() {
  if (!bot || !bot.entity || !isBotOnline || nearbyPlayers.length === 0) return;
  
  console.log('👀 Reacting to nearby player');
  
  // Stop current movement
  bot.clearControlStates();
  
  // Pause briefly
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(500, 1500)));
  
  // Look at player
  const player = nearbyPlayers[0];
  const botPos = bot.entity.position;
  const playerPos = player.position;
  
  const yaw = Math.atan2(-playerPos.x + botPos.x, playerPos.z - botPos.z);
  bot.look(yaw, 0, true);
  
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(1000, 3000)));
}

async function executeLookAtPlayer() {
  if (!bot || !bot.entity || !isBotOnline || nearbyPlayers.length === 0) return;
  
  const player = nearbyPlayers[0];
  const botPos = bot.entity.position;
  const playerPos = player.position;
  
  const yaw = Math.atan2(-playerPos.x + botPos.x, playerPos.z - botPos.z);
  const distance = botPos.distanceTo(playerPos);
  const pitch = Math.atan2(playerPos.y - botPos.y, distance);
  
  bot.look(yaw, pitch, true);
  
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(2000, 5000)));
}

async function executeFollowPlayer() {
  if (!bot || !bot.entity || !isBotOnline || nearbyPlayers.length === 0) return;
  
  console.log('🚶 Following nearby player briefly');
  
  const player = nearbyPlayers[0];
  const duration = getRandomDelay(3000, 8000);
  const startTime = Date.now();
  
  while (Date.now() - startTime < duration && bot && isBotOnline) {
    const botPos = bot.entity.position;
    const playerPos = player.position;
    
    const yaw = Math.atan2(-playerPos.x + botPos.x, playerPos.z - botPos.z);
    bot.look(yaw, 0, true);
    
    bot.setControlState('forward', true);
    
    await new Promise(resolve => setTimeout(resolve, 500));
  }
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeAvoidPlayer() {
  if (!bot || !bot.entity || !isBotOnline || nearbyPlayers.length === 0) return;
  
  console.log('🏃 Avoiding nearby player');
  
  const player = nearbyPlayers[0];
  const botPos = bot.entity.position;
  const playerPos = player.position;
  
  // Look away from player
  const yaw = Math.atan2(-playerPos.x + botPos.x, playerPos.z - botPos.z) + Math.PI;
  bot.look(yaw, 0, true);
  
  bot.setControlState('forward', true);
  
  const duration = getRandomDelay(2000, 4000);
  await new Promise(resolve => setTimeout(resolve, duration));
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeCuriousApproach() {
  if (!bot || !bot.entity || !isBotOnline || nearbyPlayers.length === 0) return;
  
  console.log('🤔 Curiously approaching player');
  
  const player = nearbyPlayers[0];
  
  // Stop and look
  bot.clearControlStates();
  
  const botPos = bot.entity.position;
  const playerPos = player.position;
  const yaw = Math.atan2(-playerPos.x + botPos.x, playerPos.z - botPos.z);
  bot.look(yaw, 0, true);
  
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(1000, 2000)));
  
  // Approach slowly with sneak
  if (bot && isBotOnline) {
    bot.setControlState('sneak', true);
    bot.setControlState('forward', true);
    
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(2000, 4000)));
    
    if (bot) bot.clearControlStates();
  }
  
  movementCount++;
}

// Advanced Combo Actions
async function executeJumpSprintCombo() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.setControlState('forward', true);
  bot.setControlState('sprint', true);
  
  const duration = getRandomDelay(2000, 4000);
  const startTime = Date.now();
  
  while (Date.now() - startTime < duration && bot && isBotOnline) {
    if (Math.random() < 0.3) {
      bot.setControlState('jump', true);
      await new Promise(resolve => setTimeout(resolve, 300));
      bot.setControlState('jump', false);
    }
    
    await new Promise(resolve => setTimeout(resolve, 500));
  }
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeSneakJumpCombo() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.setControlState('sneak', true);
  bot.setControlState('forward', true);
  
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(1000, 2000)));
  
  if (bot && isBotOnline) {
    bot.setControlState('jump', true);
    await new Promise(resolve => setTimeout(resolve, 300));
  }
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeStrafeL ookCombo() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const duration = getRandomDelay(2000, 4000);
  const startTime = Date.now();
  
  while (Date.now() - startTime < duration && bot && isBotOnline) {
    bot.clearControlStates();
    bot.setControlState(Math.random() < 0.5 ? 'left' : 'right', true);
    
    const yaw = Math.random() * Math.PI * 2;
    bot.look(yaw, 0, true);
    
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(500, 1200)));
  }
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeWalkLookCombo() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const duration = getRandomDelay(3000, 6000);
  const startTime = Date.now();
  
  bot.setControlState('forward', true);
  
  while (Date.now() - startTime < duration && bot && isBotOnline) {
    if (Math.random() < 0.4) {
      const yaw = Math.random() * Math.PI * 2;
      const pitch = (Math.random() - 0.5) * Math.PI / 4;
      bot.look(yaw, pitch, true);
    }
    
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(800, 1500)));
  }
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

// Spectator-Specific Actions
async function executeSpectatorFloat() {
  if (!bot || !bot.entity || !isBotOnline || !isInSpectatorMode) return;
  
  console.log('👻 Spectator mode: floating');
  
  // In spectator mode, looking up/down affects vertical movement
  bot.look(bot.entity.yaw, -Math.PI / 4, true);
  bot.setControlState('forward', true);
  
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(2000, 4000)));
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

async function executeSpectatorPhase() {
  if (!bot || !bot.entity || !isBotOnline || !isInSpectatorMode) return;
  
  console.log('👻 Spectator mode: phasing through blocks');
  
  // Look at a random direction and move through
  const yaw = Math.random() * Math.PI * 2;
  bot.look(yaw, 0, true);
  
  bot.setControlState('forward', true);
  
  await new Promise(resolve => setTimeout(resolve, getRandomDelay(1500, 3000)));
  
  if (bot) bot.clearControlStates();
  movementCount++;
}

// Main action executor
async function executeAction(actionName) {
  if (!bot || !isBotOnline || actionInProgress) return;
  
  actionInProgress = true;
  currentAction = actionName;
  
  try {
    switch (actionName) {
      // Basic movements
      case 'WALK_SHORT': await executeWalkShort(); break;
      case 'WALK_LONG': await executeWalkLong(); break;
      case 'WANDER': await executeWander(); break;
      case 'SPRINT_TRAVEL': await executeSprintTravel(); break;
      case 'JUMP_MOVE': await executeJumpMove(); break;
      
      // New movement variations
      case 'DIAGONAL_WALK': await executeDiagonalWalk(); break;
      case 'ZIGZAG_MOVEMENT': await executeZigzagMovement(); break;
      case 'CIRCLE_WALK': await executeCircleWalk(); break;
      case 'BACKWARDS_WALK': await executeBackwardsWalk(); break;
      case 'STRAFE_LEFT_RIGHT': await executeStrafeLeftRight(); break;
      
      // Looking actions
      case 'LOOK_AROUND': await executeLookAround(); break;
      case 'LOOK_SLOWLY': await executeLookSlowly(); break;
      case 'LOOK_QUICK': await executeLookQuick(); break;
      case 'LOOK_UP_DOWN': await executeLookUpDown(); break;
      case 'LOOK_AT_GROUND': await executeLookAtGround(); break;
      case 'LOOK_AT_SKY': await executeLookAtSky(); break;
      case 'SCAN_HORIZON': await executeScanHorizon(); break;
      case 'QUICK_HEAD_TURN': await executeQuickHeadTurn(); break;
      case 'LOOK_BEHIND': await executeLookBehind(); break;
      
      // Idle actions
      case 'IDLE_SHORT': await executeIdleShort(); break;
      case 'IDLE_MEDIUM': await executeIdleMedium(); break;
      case 'IDLE_LONG': await executeIdleLong(); break;
      case 'IDLE_WITH_MICRO_LOOK': await executeIdleWithMicroLook(); break;
      case 'COMPLETE_STILLNESS': await executeCompleteStillness(); break;
      case 'AFK_SIMULATION': await executeAfkSimulation(); break;
      
      // Interactive actions
      case 'HOTBAR_SWITCH': await executeHotbarSwitch(); break;
      case 'SWING_ARM': await executeSwingArm(); break;
      case 'SNEAK': await executeSneak(); break;
      case 'JUMP_PLACE': await executeJumpPlace(); break;
      case 'RAPID_HOTBAR_SCROLL': await executeRapidHotbarScroll(); break;
      case 'SNEAK_WALK': await executeSneakWalk(); break;
      case 'SNEAK_LOOK': await executeSneakLook(); break;
      case 'DOUBLE_JUMP': await executeDoubleJump(); break;
      case 'TRIPLE_JUMP': await executeTripleJump(); break;
      case 'CROUCH_SPAM': await executeCrouchSpam(); break;
      
      // Block interactions
      case 'LOOK_AT_BLOCK': await executeLookAtBlock(); break;
      case 'APPROACH_BLOCK': await executeApproachBlock(); break;
      case 'RIGHT_CLICK_AIR': await executeRightClickAir(); break;
      case 'LEFT_CLICK_AIR': await executeLeftClickAir(); break;
      case 'SWING_AT_BLOCK': await executeSwingAtBlock(); break;
      
      // Human mistakes
      case 'WALK_INTO_WALL': await executeWalkIntoWall(); break;
      case 'WRONG_DIRECTION': await executeWrongDirection(); break;
      case 'SUDDEN_STOP': await executeSuddenStop(); break;
      case 'ACCIDENTAL_JUMP': await executeAccidentalJump(); break;
      case 'HESITATION': await executeHesitation(); break;
      case 'OVERCORRECTION': await executeOvercorrection(); break;
      
      // Player-aware
      case 'REACT_TO_PLAYER': await executeReactToPlayer(); break;
      case 'LOOK_AT_PLAYER': await executeLookAtPlayer(); break;
      case 'FOLLOW_PLAYER': await executeFollowPlayer(); break;
      case 'AVOID_PLAYER': await executeAvoidPlayer(); break;
      case 'CURIOUS_APPROACH': await executeCuriousApproach(); break;
      
      // Combos
      case 'JUMP_SPRINT_COMBO': await executeJumpSprintCombo(); break;
      case 'SNEAK_JUMP_COMBO': await executeSneakJumpCombo(); break;
      case 'STRAFE_LOOK_COMBO': await executeStrafeL ookCombo(); break;
      case 'WALK_LOOK_COMBO': await executeWalkLookCombo(); break;
      
      // Spectator-specific
      case 'SPECTATOR_FLOAT': await executeSpectatorFloat(); break;
      case 'SPECTATOR_PHASE': await executeSpectatorPhase(); break;
      
      default:
        console.log(`⚠️  Unknown action: ${actionName}`);
    }
  } catch (err) {
    console.error(`❌ Error executing action ${actionName}:`, err.message);
  } finally {
    actionInProgress = false;
    currentAction = null;
  }
}

function scheduleNextAction() {
  if (!bot || !isBotOnline || isShuttingDown) return;
  
  // Update context
  checkNearbyPlayers();
  updateBehaviorPhase();
  updateSpectatorMode();
  
  // Dynamic delay based on behavior phase
  let minDelay, maxDelay;
  
  switch (behaviorPhase) {
    case 'active':
      minDelay = 500;
      maxDelay = 4000;
      break;
    case 'moderate':
      minDelay = 2000;
      maxDelay = 8000;
      break;
    case 'idle':
      minDelay = 5000;
      maxDelay = 15000;
      break;
    default:
      minDelay = 1000;
      maxDelay = 6000;
  }
  
  // If players nearby, be more active
  if (nearbyPlayers.length > 0) {
    minDelay = Math.max(500, minDelay * 0.7);
    maxDelay = Math.max(2000, maxDelay * 0.7);
  }
  
  const delay = getRandomDelay(minDelay, maxDelay);
  
  actionSchedulerTimeout = setTimeout(async () => {
    if (!bot || !isBotOnline) return;
    
    const action = selectRandomAction();
    
    if (Math.random() < 0.05) {
      console.log(`🎮 [${behaviorPhase}] ${action} | Players nearby: ${nearbyPlayers.length} | Mistakes: ${mistakeCounter}`);
    }
    
    await executeAction(action);
    
    scheduleNextAction();
  }, delay);
}

function setupIntervals() {
  console.log('🎮 Starting enhanced action-based scheduler with 40+ movements...');
  scheduleNextAction();
  
  activityCheckTimeout = setInterval(() => {
    checkBotActivity();
    checkPlayerCount();
    checkNearbyPlayers();
  }, ACTIVITY_CHECK_INTERVAL);
  
  setTimeout(sendPlayerList, 5000);
  setTimeout(sendBotStats, 10000);
  setTimeout(checkPlayerCount, 3000);
}

function checkBotActivity() {
  if (!botStartTime || !isBotOnline || !ANTI_AFK) return;

  const uptime = Date.now() - botStartTime;
  if (uptime >= ONE_HOUR) {
    sendDiscordEmbed('Bot Activity', 'Bot active for over 1 hour. Rejoining to prevent AFK detection.', WARNING_EMBED_COLOR);
    forceRejoinBot();
    return;
  }
}

async function getOrCreatePlayerFace(username, uuid) {
  let playerFace = await PlayerFace.findOne({ username: username });
  let skinUrl;

  if (!playerFace) {
    if (username.startsWith('.')) {
      const assignedFaces = await PlayerFace.find({ username: { $regex: '^\\.' } }, 'face');
      const availableFaces = FACES.filter(face => !assignedFaces.some(pf => pf.face === face));

      let selectedFace;
      if (availableFaces.length > 0 && nextDotFaceIndex < FACES.length) {
        selectedFace = FACES[nextDotFaceIndex];
        nextDotFaceIndex = (nextDotFaceIndex + 1) % FACES.length;
      } else {
        selectedFace = FACES[Math.floor(Math.random() * FACES.length)];
      }
      playerFace = new PlayerFace({ username: username, face: selectedFace, isCustom: false });
      skinUrl = `./${selectedFace}`;
    } else {
      try {
        const faceUrl = uuid ? `https://crafatar.com/avatars/${uuid}?size=32&overlay` : `https://crafatar.com/avatars/${username}?size=32&overlay`;
        const crafatarResponse = await axios.get(faceUrl, { responseType: 'arraybuffer' });
        
        if (crafatarResponse.status === 200) {
          skinUrl = faceUrl;
          playerFace = new PlayerFace({ username: username, face: skinUrl, isCustom: true });
        } else {
          throw new Error("Face not found");
        }
      } catch (crafatarError) {
        const selectedFace = FACES[Math.floor(Math.random() * FACES.length)];
        skinUrl = `./${selectedFace}`;
        playerFace = new PlayerFace({ username: username, face: selectedFace, isCustom: false });
      }
    }
    await playerFace.save();
  } else {
    skinUrl = playerFace.isCustom ? playerFace.face : `./${playerFace.face}`;
  }
  return skinUrl;
}

function startBot() {
  if (isShuttingDown) {
    console.log('⚠️  Bot is shutting down, not starting new connection');
    return;
  }

  clearAllIntervals();
  if (bot) {
    bot.removeAllListeners();
    bot = null;
  }

  resetBotState();

  console.log(`🚀 Starting bot with version ${BOT_VERSION}...`);
  bot = mineflayer.createBot(botOptions);

  bot.once('spawn', () => {
    sendDiscordEmbed('Bot Connected', `${botOptions.username} has joined the server (v${BOT_VERSION})`, SUCCESS_EMBED_COLOR);
    isBotOnline = true;
    botStartTime = Date.now();
    lastOnlineTime = Date.now();
    consecutiveFailures = 0;
    console.log(`✅ Bot spawned successfully on ${BOT_HOST}:${BOT_PORT}`);

    if (bot._client && bot._client.socket) {
      bot._client.socket.setKeepAlive(true, 30000);
    }
    
    if (bot._client) {
      bot._client.on('player_info', (packet) => {
        packet.data.forEach((player) => {
          if (player.uuid === bot.uuid) {
            const gamemodeMap = { 0: 'Survival', 1: 'Creative', 2: 'Adventure', 3: 'Spectator' };
            const currentGamemode = gamemodeMap[player.gamemode] || 'Unknown';
            bot.game = bot.game || {};
            bot.game.gameMode = currentGamemode;
            updateSpectatorMode();
          }
        });
      });
    }

    setTimeout(() => {
      setupIntervals();
    }, 1000);
  });

  bot.on('error', (err) => {
    console.error('❌ Bot Error:', err.message);
    sendDiscordEmbed('Bot Error', `Error: ${err.message}`, ERROR_EMBED_COLOR);

    if (err.message.includes("timed out") ||
        err.message.includes("ECONNRESET") ||
        err.message.includes("ECONNREFUSED") ||
        err.name === 'PartialReadError' ||
        err.message.includes("Unexpected buffer end")) {
      
      resetBotState();
      clearAllIntervals();
      consecutiveFailures++;
      
      if (AUTO_REJOIN) {
        reconnectBot();
      }
    }
  });

  bot.on('end', async (reason) => {
    console.log('🔌 Bot disconnected:', reason);
    
    await ensureTimeUnfrozen();
    resetBotState();
    clearAllIntervals();
    consecutiveFailures++;
    
    if (AUTO_REJOIN && !isShuttingDown) {
      reconnectBot();
    }
  });

  bot.on('kicked', async (reason) => {
    console.log('⛔ Bot was kicked:', reason);
    const reasonStr = typeof reason === 'string' ? reason : JSON.stringify(reason);
    await sendDiscordEmbed('Bot Kicked', `Reason: ${reasonStr}`, ERROR_EMBED_COLOR);
    
    await ensureTimeUnfrozen();
    resetBotState();
    clearAllIntervals();
    
    const isAfkKick = reasonStr.toLowerCase().includes('idle') || 
                     reasonStr.toLowerCase().includes('afk') || 
                     reasonStr.toLowerCase().includes('terms of service');
    
    if (isAfkKick) {
      console.log('⚠️  Detected AFK kick from Aternos. Will attempt to rejoin.');
      consecutiveFailures++;
      if (AUTO_REJOIN && !isShuttingDown) {
        console.log(`⏳ Reconnecting after AFK kick in 30 seconds...`);
        reconnectTimeout = setTimeout(() => {
          startBot();
        }, 30000);
      }
    } else {
      consecutiveFailures++;
      if (AUTO_REJOIN && !isShuttingDown) {
        reconnectBot();
      }
    }
  });

  bot.on('chat', async (username, message) => {
    if (username !== botOptions.username) {
      let trueUsername = username;
      let uuid = null;
      
      if (bot && bot.players) {
        const player = Object.values(bot.players).find(p =>
          p.username.replace(/^\./, '') === username.replace(/^\./, '')
        );
        if (player) {
            trueUsername = player.username;
            uuid = player.uuid;
        }
      }

      sendPlayerMessage(trueUsername, message);

      try {
        const skinUrl = await getOrCreatePlayerFace(trueUsername, uuid);
        const chatMessage = new MinecraftChat({ username: trueUsername, chat: message });
        await chatMessage.save();
        io.emit('chatMessage', {
          username: trueUsername,
          chat: message,
          timestamp: chatMessage.timestamp,
          skinUrl,
        });
      } catch (err) {
        console.error('❌ Error saving chat message to MongoDB:', err.message);
      }
    }
  });

  bot.on('playerJoined', async (player) => {
    if (player.username !== botOptions.username) {
      console.log(`👋 ${player.username} joined the game`);
      const skinUrl = await getOrCreatePlayerFace(player.username, player.uuid);
      player.skinUrl = skinUrl;

      if (CHAT_WEBHOOK) {
        await axios.post(CHAT_WEBHOOK, {
          content: `📥 **${player.username}** joined the game.`
        }).catch(err => console.error('❌ Join Webhook Error:', err.message));
      }

      sendPlayerList();
      setTimeout(checkPlayerCount, 1000);
      setTimeout(checkNearbyPlayers, 2000);
    }
  });

  bot.on('playerLeft', (player) => {
    if (player.username !== botOptions.username) {
      console.log(`👋 ${player.username} left the game`);
      
      if (CHAT_WEBHOOK) {
        axios.post(CHAT_WEBHOOK, {
          content: `📤 **${player.username}** left the game.`
        }).catch(err => console.error('❌ Leave Webhook Error:', err.message));
      }

      sendPlayerList();
      setTimeout(checkPlayerCount, 1000);
      setTimeout(checkNearbyPlayers, 2000);
    }
  });

  bot.on('health', () => {
    // Health monitoring
  });
}

function reconnectBot() {
  if (isShuttingDown) {
    console.log('⚠️  Bot is shutting down, not reconnecting');
    return;
  }
  
  clearAllIntervals();
  
  const baseDelay = RECONNECT_DELAY;
  const maxDelay = 300000;
  const delay = Math.min(baseDelay * Math.pow(2, Math.min(consecutiveFailures, 5)), maxDelay);
  
  console.log(`⏳ Reconnecting in ${delay / 1000} seconds... (Attempt ${consecutiveFailures + 1})`);
  reconnectTimeout = setTimeout(() => {
    startBot();
  }, delay);
}

function forceRejoinBot() {
  if (isShuttingDown) return;
  
  clearAllIntervals();
  console.log(`⏳ Rejoining in ${FIFTEEN_SECONDS / 1000} seconds...`);
  activityCheckTimeout = setTimeout(() => {
    startBot();
  }, FIFTEEN_SECONDS);
}

function getCpuUsage() {
  const cpus = os.cpus();
  let totalIdle = 0, totalTick = 0;

  for (let i = 0; i < cpus.length; i++) {
    const cpu = cpus[i];
    for (const type in cpu.times) {
      totalTick += cpu.times[type];
    }
    totalIdle += cpu.times.idle;
  }

  const idleDifference = totalIdle - lastCpuUsage.idle;
  const totalDifference = totalTick - lastCpuUsage.total;

  lastCpuUsage = { idle: totalIdle, total: totalTick };
  if (totalDifference === 0) return 0;
  return 100 - (100 * idleDifference / totalDifference);
}

async function getBotStatusPayload() {
    const botActive = isBotOnline && bot && bot.entity;
    
    let onlinePlayersCount = 0;
    let playerDetails = [];
    
    if (botActive) {
        const playersExcludingBot = getOnlinePlayersExcludingBot();
        onlinePlayersCount = playersExcludingBot.length;
        playerDetails = await Promise.all(playersExcludingBot.map(async p => {
            const skinUrl = await getOrCreatePlayerFace(p.username, p.uuid);
            return { username: p.username, uuid: p.uuid, skinUrl: skinUrl };
        }));
    }

    let diskInfo = { free: 0, total: 0 };
    try {
        const pathToCheck = os.platform() === 'win32' ? 'C:' : '/';
        diskInfo = await diskusage.check(pathToCheck);
    } catch (err) {
        // Suppress disk errors
    }

    return {
        message: botActive ? "Bot is running!" : "Bot is offline",
        onlinePlayersCount: botActive ? onlinePlayersCount : 0,
        playerDetails: botActive ? playerDetails : [],
        
        gameMode: botActive && bot.game ? bot.game.gameMode : 'N/A',
        position: botActive ? {
            x: Math.floor(bot.entity.position.x),
            y: Math.floor(bot.entity.position.y),
            z: Math.floor(bot.entity.position.z)
        } : 'N/A',
        
        uptime: (botActive && botStartTime) ? Math.floor((Date.now() - botStartTime) / 1000) : 0,
        movements: botActive ? movementCount : 0,
        memoryUsage: `${Math.round(process.memoryUsage().rss / 1024 / 1024 * 100) / 100} MB`,
        
        lastOnline: lastOnlineTime || null,
        serverHost: currentServerHost,
        serverPort: currentServerPort,
        botName: BOT_USERNAME,
        
        botHealth: botActive && bot.health !== undefined ? `${Math.round(bot.health)}/20` : 'N/A',
        botFood: botActive && bot.food !== undefined ? `${Math.round(bot.food)}/20` : 'N/A',
        botLatency: botActive && bot.player && bot.player.ping !== undefined ? `${bot.player.ping}ms` : 'N/A',
        
        serverLoad: os.loadavg()[0].toFixed(2),
        cpuUsage: getCpuUsage().toFixed(2),
        diskFree: diskInfo.total > 0 ? `${(diskInfo.free / (1024 ** 3)).toFixed(2)} GB` : 'N/A',
        diskTotal: diskInfo.total > 0 ? `${(diskInfo.total / (1024 ** 3)).toFixed(2)} GB` : 'N/A',
        
        minecraftDay: botActive && bot.time ? bot.time.day : 'N/A',
        minecraftTime: botActive && bot.time ? bot.time.timeOfDay : 'N/A',
        serverDifficulty: botActive && bot.game ? bot.game.difficulty : 'N/A',
        timeFrozen: isTimeFrozen,
        version: BOT_VERSION,
    };
}

app.get('/api/status', async (req, res) => {
  try {
    const status = await getBotStatusPayload();
    res.json(status);
  } catch (err) {
    console.error('❌ Error in /api/status:', err.message);
    res.status(500).json({ error: "Internal Server Error" });
  }
});

app.get('/api/chat', async (req, res) => {
  try {
    const { username, date, search } = req.query;
    let query = {};
    if (username) {
      query.username = username;
    }
    if (date) {
      const startOfDay = new Date(date);
      startOfDay.setHours(0, 0, 0, 0);
      const endOfDay = new Date(date);
      endOfDay.setHours(23, 59, 59, 999);
      query.timestamp = { $gte: startOfDay, $lte: endOfDay };
    }
    if (search) {
      query.chat = { $regex: search, $options: 'i' };
    }
    const skip = parseInt(req.query.skip) || 0;
    const limit = parseInt(req.query.limit) || 100;
    const messages = await MinecraftChat.find(query)
      .sort({ timestamp: -1 })
      .skip(skip)
      .limit(limit);

    const messagesWithFaces = await Promise.all(messages.map(async (msg) => {
      const skinUrl = await getOrCreatePlayerFace(msg.username, null);
      return { ...msg.toObject(), skinUrl };
    }));

    res.json(messagesWithFaces);
  } catch (err) {
    console.error('❌ Error fetching chat history:', err.message);
    res.status(500).json({ error: 'Internal Server Error' });
  }
});

app.get('/api/chat/usernames', async (req, res) => {
  try {
    const usernames = await MinecraftChat.distinct('username');
    res.json(usernames);
  } catch (err) {
    console.error('❌ Error fetching distinct usernames:', err.message);
    res.status(500).json({ error: 'Internal Server Error' });
  }
});

io.on('connection', (socket) => {
  console.log('🔌 Client connected to Socket.IO');
});

setInterval(async () => {
  try {
    const botStatus = await getBotStatusPayload();
    io.emit('botStatusUpdate', botStatus);
  } catch (err) {
    console.error('❌ Error emitting status update via Socket.IO:', err.message);
  }
}, SOCKET_IO_UPDATE_INTERVAL);

app.get('/', (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'dashboard.html'));
});

server.listen(WEB_SERVER_PORT, () => {
  console.log(`🌐 Web monitoring server started on port ${WEB_SERVER_PORT}`);
  sendDiscordEmbed('Web Server', `Web monitoring server started on port ${WEB_SERVER_PORT}`, DEFAULT_EMBED_COLOR);
});

process.on('SIGINT', async () => {
  console.log('\n⚠️  Received SIGINT, shutting down gracefully...');
  isShuttingDown = true;
  
  await ensureTimeUnfrozen();
  
  if (bot) {
    await sendDiscordEmbed('Bot Shutdown', 'Bot is shutting down gracefully', WARNING_EMBED_COLOR);
    bot.quit();
  }
  
  clearAllIntervals();
  
  setTimeout(() => {
    console.log('✅ Shutdown complete');
    process.exit(0);
  }, 2000);
});

process.on('SIGTERM', async () => {
  console.log('\n⚠️  Received SIGTERM, shutting down gracefully...');
  isShuttingDown = true;
  
  await ensureTimeUnfrozen();
  
  if (bot) {
    await sendDiscordEmbed('Bot Shutdown', 'Bot is shutting down gracefully', WARNING_EMBED_COLOR);
    bot.quit();
  }
  
  clearAllIntervals();
  
  setTimeout(() => {
    console.log('✅ Shutdown complete');
    process.exit(0);
  }, 2000);
});

startBot();
