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
let actionInProgress = false; // Track connection failures

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

// Reset state strictly to avoid fake data
function resetBotState() {
  isBotOnline = false;
  botStartTime = null;
  movementCount = 0;
  isTimeFrozen = false;
  otherPlayersOnline = 0;
  // Note: We do NOT reset lastOnlineTime so the dashboard knows when it was last seen
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
      embeds: [{ 
        author: { name: username }, 
        description: message, 
        color: CHAT_EMBED_COLOR,
        timestamp: new Date().toISOString() 
      }],
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

// Time freeze/unfreeze functions
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
  // Logic kept for potential Discord updates, but simplified
}

function sendBotStats() {
  if (!bot || !isBotOnline) return;
  try {
    const uptime = botStartTime ? Math.floor((Date.now() - botStartTime) / 1000) : 0;
    const hours = Math.floor(uptime / 3600);
    const minutes = Math.floor((uptime % 3600) / 60);
    const seconds = uptime % 60;
    const uptimeStr = `${hours}h ${minutes}m ${seconds}s`;
    
    // Safety check for entity
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
      { name: 'Server Load', value: `${os.loadavg()[0].toFixed(2)}`, inline: true }
    ]);
  } catch (err) {
    console.error('❌ Error sending bot stats:', err.message);
  }
}

// ============================================================================
// 🎮 ACTION-BASED SCHEDULER - Truly Random, Human-Like Behavior
// ============================================================================

// Define all possible actions with weights (higher = more frequent)
const ACTIONS = {
  // Movement actions (40% total)
  WALK_SHORT: { weight: 15, type: 'movement' },
  WALK_LONG: { weight: 10, type: 'movement' },
  WANDER: { weight: 8, type: 'movement' },
  SPRINT_TRAVEL: { weight: 5, type: 'movement' },
  JUMP_MOVE: { weight: 2, type: 'movement' },
  
  // Looking actions (25% total)
  LOOK_AROUND: { weight: 12, type: 'look' },
  LOOK_SLOWLY: { weight: 8, type: 'look' },
  LOOK_QUICK: { weight: 5, type: 'look' },
  
  // Idle actions (20% total)
  IDLE_SHORT: { weight: 10, type: 'idle' },
  IDLE_MEDIUM: { weight: 7, type: 'idle' },
  IDLE_LONG: { weight: 3, type: 'idle' },
  
  // Interactive actions (15% total)
  HOTBAR_SWITCH: { weight: 6, type: 'interaction' },
  SWING_ARM: { weight: 5, type: 'interaction' },
  SNEAK: { weight: 2, type: 'interaction' },
  JUMP_PLACE: { weight: 2, type: 'interaction' },
};

// Calculate total weight for random selection
const TOTAL_WEIGHT = Object.values(ACTIONS).reduce((sum, action) => sum + action.weight, 0);

/**
 * Get a truly random delay that's completely unpredictable
 * Uses multiple layers of randomness
 */
function getRandomDelay(min, max) {
  const baseDelay = min + Math.random() * (max - min);
  // Add random variance (±30%)
  const variance = baseDelay * 0.3 * (Math.random() - 0.5);
  // Add small random spikes occasionally
  const spike = Math.random() < 0.1 ? Math.random() * 1000 : 0;
  return Math.floor(baseDelay + variance + spike);
}

/**
 * Select a random action based on weights
 */
function selectRandomAction() {
  let random = Math.random() * TOTAL_WEIGHT;
  
  for (const [actionName, actionData] of Object.entries(ACTIONS)) {
    random -= actionData.weight;
    if (random <= 0) {
      return actionName;
    }
  }
  
  // Fallback (should never reach here)
  return 'LOOK_AROUND';
}

/**
 * Execute WALK_SHORT: Brief walk in a random direction
 */
async function executeWalkShort() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const directions = ['forward', 'back', 'left', 'right'];
  const direction = directions[Math.floor(Math.random() * directions.length)];
  
  bot.setControlState(direction, true);
  
  // 20% chance to jump while walking
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

/**
 * Execute WALK_LONG: Extended walk in one direction
 */
async function executeWalkLong() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const directions = ['forward', 'back', 'left', 'right'];
  const direction = directions[Math.floor(Math.random() * directions.length)];
  
  bot.setControlState(direction, true);
  
  // 30% chance to sprint
  if (Math.random() < 0.3) {
    bot.setControlState('sprint', true);
  }
  
  const duration = getRandomDelay(1500, 4000);
  
  // Occasionally jump during long walks
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

/**
 * Execute WANDER: Realistic wandering with direction changes
 */
async function executeWander() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const totalDuration = getRandomDelay(3000, 8000);
  const startTime = Date.now();
  
  while (Date.now() - startTime < totalDuration && bot && isBotOnline) {
    const directions = ['forward', 'back', 'left', 'right'];
    const direction = directions[Math.floor(Math.random() * directions.length)];
    
    bot.clearControlStates();
    bot.setControlState(direction, true);
    
    // Random sprint bursts
    if (Math.random() < 0.4) {
      bot.setControlState('sprint', true);
    }
    
    // Look in movement direction occasionally
    if (Math.random() < 0.3) {
      const yaw = Math.random() * Math.PI * 2;
      const pitch = (Math.random() - 0.5) * Math.PI / 4;
      bot.look(yaw, pitch, true);
    }
    
    // Each direction segment lasts different time
    const segmentDuration = getRandomDelay(500, 2000);
    await new Promise(resolve => setTimeout(resolve, segmentDuration));
    
    // Random jump
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

/**
 * Execute SPRINT_TRAVEL: Long sprint in one direction (like traveling)
 */
async function executeSprintTravel() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const yaw = Math.random() * Math.PI * 2;
  bot.look(yaw, 0, true);
  
  bot.setControlState('forward', true);
  bot.setControlState('sprint', true);
  
  const duration = getRandomDelay(2000, 6000);
  
  // Jump occasionally while sprinting
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

/**
 * Execute JUMP_MOVE: Jump in place or while moving
 */
async function executeJumpMove() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  // 50% chance to move while jumping
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

/**
 * Execute LOOK_AROUND: Natural looking behavior
 */
async function executeLookAround() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const numLooks = 1 + Math.floor(Math.random() * 3); // 1-3 looks
  
  for (let i = 0; i < numLooks; i++) {
    if (!bot || !isBotOnline) break;
    
    const yaw = Math.random() * Math.PI * 2;
    const pitch = (Math.random() - 0.5) * Math.PI / 2;
    bot.look(yaw, pitch, true);
    
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(300, 1000)));
  }
}

/**
 * Execute LOOK_SLOWLY: Slow, deliberate looking (like reading signs)
 */
async function executeLookSlowly() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const currentYaw = bot.entity.yaw;
  const currentPitch = bot.entity.pitch;
  
  const targetYaw = currentYaw + (Math.random() - 0.5) * Math.PI;
  const targetPitch = (Math.random() - 0.5) * Math.PI / 3;
  
  // Slow interpolated look
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

/**
 * Execute LOOK_QUICK: Quick glances
 */
async function executeLookQuick() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const yaw = Math.random() * Math.PI * 2;
  const pitch = (Math.random() - 0.5) * Math.PI / 4;
  
  bot.look(yaw, pitch, false); // false = instant look
}

/**
 * Execute IDLE_SHORT: Brief pause (like checking inventory)
 */
async function executeIdleShort() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.clearControlStates();
  const duration = getRandomDelay(500, 2000);
  await new Promise(resolve => setTimeout(resolve, duration));
}

/**
 * Execute IDLE_MEDIUM: Medium pause (like organizing inventory)
 */
async function executeIdleMedium() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.clearControlStates();
  const duration = getRandomDelay(2000, 5000);
  
  // Occasionally look around while idle
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

/**
 * Execute IDLE_LONG: Long pause (like AFK/typing in chat)
 */
async function executeIdleLong() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.clearControlStates();
  const duration = getRandomDelay(5000, 12000);
  await new Promise(resolve => setTimeout(resolve, duration));
}

/**
 * Execute HOTBAR_SWITCH: Switch hotbar slots (simulate item selection)
 */
async function executeHotbarSwitch() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  try {
    const currentSlot = bot.quickBarSlot;
    const numSwitches = 1 + Math.floor(Math.random() * 3); // 1-3 switches
    
    for (let i = 0; i < numSwitches; i++) {
      if (!bot || !isBotOnline) break;
      
      let newSlot = Math.floor(Math.random() * 9);
      // Don't switch to same slot
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

/**
 * Execute SWING_ARM: Swing arm (like breaking block or attacking)
 */
async function executeSwingArm() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  const numSwings = 1 + Math.floor(Math.random() * 3); // 1-3 swings
  
  for (let i = 0; i < numSwings; i++) {
    if (!bot || !isBotOnline) break;
    
    const hand = Math.random() < 0.5 ? 'right' : 'left';
    bot.swingArm(hand);
    
    await new Promise(resolve => setTimeout(resolve, getRandomDelay(100, 400)));
  }
  
  movementCount++;
}

/**
 * Execute SNEAK: Brief sneaking
 */
async function executeSneak() {
  if (!bot || !bot.entity || !isBotOnline) return;
  
  bot.setControlState('sneak', true);
  
  const duration = getRandomDelay(500, 2500);
  
  // Maybe move while sneaking
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

/**
 * Execute JUMP_PLACE: Jump as if placing block beneath
 */
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

/**
 * Main action executor - routes to specific action functions
 */
async function executeAction(actionName) {
  if (!bot || !isBotOnline || actionInProgress) return;
  
  actionInProgress = true;
  currentAction = actionName;
  
  try {
    switch (actionName) {
      case 'WALK_SHORT':
        await executeWalkShort();
        break;
      case 'WALK_LONG':
        await executeWalkLong();
        break;
      case 'WANDER':
        await executeWander();
        break;
      case 'SPRINT_TRAVEL':
        await executeSprintTravel();
        break;
      case 'JUMP_MOVE':
        await executeJumpMove();
        break;
      case 'LOOK_AROUND':
        await executeLookAround();
        break;
      case 'LOOK_SLOWLY':
        await executeLookSlowly();
        break;
      case 'LOOK_QUICK':
        await executeLookQuick();
        break;
      case 'IDLE_SHORT':
        await executeIdleShort();
        break;
      case 'IDLE_MEDIUM':
        await executeIdleMedium();
        break;
      case 'IDLE_LONG':
        await executeIdleLong();
        break;
      case 'HOTBAR_SWITCH':
        await executeHotbarSwitch();
        break;
      case 'SWING_ARM':
        await executeSwingArm();
        break;
      case 'SNEAK':
        await executeSneak();
        break;
      case 'JUMP_PLACE':
        await executeJumpPlace();
        break;
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

/**
 * Action Scheduler - schedules next action with random delay
 */
function scheduleNextAction() {
  if (!bot || !isBotOnline || isShuttingDown) return;
  
  // Completely random delay between actions (0.5s to 8s)
  // This makes behavior unpredictable even to you
  const delay = getRandomDelay(500, 8000);
  
  actionSchedulerTimeout = setTimeout(async () => {
    if (!bot || !isBotOnline) return;
    
    const action = selectRandomAction();
    
    // Log occasionally for debugging (10% of the time)
    if (Math.random() < 0.1) {
      console.log(`🎮 Executing: ${action} (next in ~${Math.floor(delay/1000)}s)`);
    }
    
    await executeAction(action);
    
    // Schedule next action
    scheduleNextAction();
  }, delay);
}

// ============================================================================
// End of Action-Based Scheduler
// ============================================================================

function setupIntervals() {
  // Start the action-based scheduler
  console.log('🎮 Starting action-based scheduler...');
  scheduleNextAction();
  
  // Keep the activity check interval
  activityCheckTimeout = setInterval(() => {
    checkBotActivity();
    checkPlayerCount();
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

  // Reset state on start attempt
  resetBotState();

  console.log(`🚀 Starting bot with version ${BOT_VERSION}...`);
  bot = mineflayer.createBot(botOptions);

  bot.once('spawn', () => {
    sendDiscordEmbed('Bot Connected', `${botOptions.username} has joined the server (v${BOT_VERSION})`, SUCCESS_EMBED_COLOR);
    isBotOnline = true;
    botStartTime = Date.now();
    lastOnlineTime = Date.now();
    consecutiveFailures = 0; // Reset failure counter on successful connection
    console.log(`✅ Bot spawned successfully on ${BOT_HOST}:${BOT_PORT}`);

    // Safe socket keepalive
    if (bot._client && bot._client.socket) {
      bot._client.socket.setKeepAlive(true, 30000);
    }
    
    // Move the player_info listener here to ensure _client exists
    if (bot._client) {
      bot._client.on('player_info', (packet) => {
        packet.data.forEach((player) => {
          if (player.uuid === bot.uuid) {
            const gamemodeMap = { 0: 'Survival', 1: 'Creative', 2: 'Adventure', 3: 'Spectator' };
            const currentGamemode = gamemodeMap[player.gamemode] || 'Unknown';
            bot.game = bot.game || {};
            bot.game.gameMode = currentGamemode;
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

  // ✅ FIXED: Properly handle kicks (including Aternos AFK kicks) with auto-rejoin
  bot.on('kicked', async (reason) => {
    console.log('⛔ Bot was kicked:', reason);
    const reasonStr = typeof reason === 'string' ? reason : JSON.stringify(reason);
    await sendDiscordEmbed('Bot Kicked', `Reason: ${reasonStr}`, ERROR_EMBED_COLOR);
    
    await ensureTimeUnfrozen();
    resetBotState();
    clearAllIntervals();
    
    // Check if it's an Aternos AFK kick
    const isAfkKick = reasonStr.toLowerCase().includes('idle') || 
                     reasonStr.toLowerCase().includes('afk') || 
                     reasonStr.toLowerCase().includes('terms of service');
    
    if (isAfkKick) {
      console.log('⚠️  Detected AFK kick from Aternos. Will attempt to rejoin.');
      consecutiveFailures++;
      // Use longer delay for AFK kicks (30 seconds)
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

      const onlinePlayersCount = getOnlinePlayersExcludingBot().length;
      sendChatEmbed('Player Joined', `**${player.username}** joined the game.`, SUCCESS_EMBED_COLOR, [
        { name: 'Current Players', value: `${onlinePlayersCount} (excluding bot)`, inline: true }
      ]);
      sendPlayerList();
      setTimeout(checkPlayerCount, 1000);
    }
  });

  bot.on('playerLeft', (player) => {
    if (player.username !== botOptions.username) {
      console.log(`👋 ${player.username} left the game`);
      const onlinePlayersCount = getOnlinePlayersExcludingBot().length;
      sendChatEmbed('Player Left', `**${player.username}** left the game.`, 0xff4500, [
        { name: 'Current Players', value: `${Math.max(0, onlinePlayersCount)} (excluding bot)`, inline: true }
      ]);
      sendPlayerList();
      setTimeout(checkPlayerCount, 1000);
    }
  });

  bot.on('health', () => {
    // Health monitoring
  });
}

// ✅ IMPROVED: Use exponential backoff for reconnection attempts
function reconnectBot() {
  if (isShuttingDown) {
    console.log('⚠️  Bot is shutting down, not reconnecting');
    return;
  }
  
  clearAllIntervals();
  
  // Exponential backoff with cap at 5 minutes
  const baseDelay = RECONNECT_DELAY;
  const maxDelay = 300000; // 5 minutes
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

// ✅ FIXED: Return proper offline status when bot is not connected
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

    // ✅ Return appropriate values based on online status
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

// Global Interval for Socket Updates
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

// Graceful shutdown
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
