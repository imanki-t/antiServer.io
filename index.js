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

const MOVEMENT_INTERVAL = config.intervals.movement;
const LOOK_INTERVAL = config.intervals.look;
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
const CHAT_EMBED_COLOR = config.embedColors.chat; // Removed the fallback


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
let movementInterval = null;
let lookInterval = null;
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
  if (movementInterval) {
    clearInterval(movementInterval);
    movementInterval = null;
  }
  if (lookInterval) {
    clearInterval(lookInterval);
    lookInterval = null;
  }
  if (reconnectTimeout) {
    clearTimeout(reconnectTimeout);
    reconnectTimeout = null;
  }
  if (activityCheckTimeout) {
    clearInterval(activityCheckTimeout);
    activityCheckTimeout = null;
  }
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
        color: CHAT_EMBED_COLOR, // ✅ Updated to Norwegian Blue
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

function performMovement() {
  if (!bot || !bot.entity || !isBotOnline) return;
  try {
    // 1. Random look direction (Simulates a human looking around)
    const yaw = Math.random() * Math.PI * 2;
    const pitch = (Math.random() * Math.PI / 2) - (Math.PI / 4);
    bot.look(yaw, pitch);

    const randomAction = Math.random();

    // 2. Action Logic
    if (randomAction < 0.4) {
        // 40% Chance: Walk briefly (Simulate small movements)
        bot.setControlState('forward', true);
        
        // 10% Chance: Jump while walking (to clear 1-block obstacles)
        if (Math.random() < 0.25) {
            bot.setControlState('jump', true);
        }

        // Stop after 0.5 - 1 second to avoid walking into danger
        // This is the "Safety Walk" feature
        const duration = 500 + Math.random() * 500; 
        setTimeout(() => {
            if (bot) {
                bot.clearControlStates(); // Stops walking and jumping
            }
        }, duration);

    } else if (randomAction < 0.7) {
        // 30% Chance: Jump in place (Classic AFK behavior)
        bot.setControlState('jump', true);
        setTimeout(() => {
            if (bot) bot.setControlState('jump', false);
        }, 500);

    } else {
        // 30% Chance: Just swing arm
        bot.swingArm('right');
    }

    movementCount++;
  } catch (err) {
    console.error('❌ Movement error:', err.message);
  }
}

function lookAround() {
  if (!bot || !bot.entity || !isBotOnline) return;
  try {
    const yaw = Math.random() * Math.PI * 2;
    const pitch = (Math.random() * Math.PI / 3) - (Math.PI / 6);
    bot.look(yaw, pitch, true);
  } catch (err) {
    console.error('❌ Look error:', err.message);
  }
}

function setupIntervals() {
  movementInterval = setInterval(performMovement, MOVEMENT_INTERVAL);
  lookInterval = setInterval(lookAround, LOOK_INTERVAL);
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
        // Only try crafatar if we have a UUID or it's a real player name (not starting with .)
        const faceUrl = uuid ? `https://crafatar.com/avatars/${uuid}?size=32&overlay` : `https://crafatar.com/avatars/${username}?size=32&overlay`; // Fallback to username for crafatar if uuid missing
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
      
      resetBotState(); // Ensure offline status
      clearAllIntervals();
      if (AUTO_REJOIN) {
        reconnectBot();
      }
    }
  });

  bot.on('end', async (reason) => {
    console.log('🔌 Bot disconnected:', reason);
    
    await ensureTimeUnfrozen();
    resetBotState(); // Ensure offline status
    clearAllIntervals();
    
    if (AUTO_REJOIN && !isShuttingDown) {
      reconnectBot();
    }
  });

  bot.on('kicked', async (reason) => {
    console.log('⛔ Bot was kicked:', reason);
    await sendDiscordEmbed('Bot Kicked', `Reason: ${reason}`, ERROR_EMBED_COLOR);
    
    await ensureTimeUnfrozen();
    resetBotState(); // Ensure offline status
    clearAllIntervals();
    
    if (AUTO_REJOIN && !isShuttingDown) {
      reconnectBot();
    }
  });

  bot.on('chat', async (username, message) => {
    if (username !== botOptions.username) {
      // Logic to find real username if obfuscated
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

function reconnectBot() {
  if (isShuttingDown) {
    console.log('⚠️  Bot is shutting down, not reconnecting');
    return;
  }
  
  clearAllIntervals();
  console.log(`⏳ Reconnecting in ${RECONNECT_DELAY / 1000} seconds...`);
  reconnectTimeout = setTimeout(() => {
    startBot();
  }, RECONNECT_DELAY);
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
  // Check division by zero or NaN
  if (totalDifference === 0) return 0;
  return 100 - (100 * idleDifference / totalDifference);
}

// --- HELPER to generate status payload safely ---
async function getBotStatusPayload() {
    const botActive = isBotOnline && bot && bot.entity;
    
    let onlinePlayersCount = 0;
    let playerDetails = [];
    
    if (botActive) {
        const playersExcludingBot = getOnlinePlayersExcludingBot();
        onlinePlayersCount = playersExcludingBot.length;
        // Map players
        playerDetails = await Promise.all(playersExcludingBot.map(async p => {
            const skinUrl = await getOrCreatePlayerFace(p.username, p.uuid);
            return { username: p.username, uuid: p.uuid, skinUrl: skinUrl };
        }));
    }

    let diskInfo = { free: 0, total: 0 };
    try {
        // Safe check for disk usage (platform independent)
        const pathToCheck = os.platform() === 'win32' ? 'C:' : '/';
        diskInfo = await diskusage.check(pathToCheck);
    } catch (err) {
        // console.error('Disk usage error (ignoring):', err.message); 
        // Suppress generic disk errors to avoid log spam
    }

    return {
        message: botActive ? "Bot is running!" : "Bot is offline",
        onlinePlayersCount: onlinePlayersCount,
        playerDetails: playerDetails,
        
        // Return N/A or 0 if bot is not active
        gameMode: botActive && bot.game ? bot.game.gameMode : 'N/A',
        position: botActive ?
          {
            x: Math.floor(bot.entity.position.x),
            y: Math.floor(bot.entity.position.y),
            z: Math.floor(bot.entity.position.z)
          } : 'N/A',
        
        uptime: (botActive && botStartTime) ? Math.floor((Date.now() - botStartTime) / 1000) : 0,
        movements: botActive ? movementCount : 0,
        memoryUsage: `${Math.round(process.memoryUsage().rss / 1024 / 1024 * 100) / 100} MB`,
        
        lastOnline: lastOnlineTime,
        serverHost: currentServerHost,
        serverPort: currentServerPort,
        botName: BOT_USERNAME,
        
        botHealth: botActive && bot.health !== undefined ? `${Math.round(bot.health)}/20` : '0/20',
        botFood: botActive && bot.food !== undefined ? `${Math.round(bot.food)}/20` : '0/20',
        botLatency: botActive && bot.player && bot.player.ping !== undefined ? `${bot.player.ping}ms` : '0ms',
        
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
              
