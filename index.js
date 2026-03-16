const mineflayer = require('mineflayer');
const axios = require('axios');
const Vec3 = require('vec3');
const express = require('express');
const path = require('path');
const os = require('os');

const BOT_HOST = process.env.BOT_HOST || 'NoobsGang.aternos.me';
const BOT_PORT = parseInt(process.env.BOT_PORT, 10) || 45944;
const BOT_USERNAME = process.env.BOT_USERNAME || 'NOOB';
const DISCORD_WEBHOOK = process.env.DISCORD_WEBHOOK;
const CHAT_WEBHOOK = process.env.CHAT_WEBHOOK;
const MESSAGE_WEBHOOK = process.env.MESSAGE_WEBHOOK;
const WEB_SERVER_PORT = process.env.PORT || 3000;

const MOVEMENT_INTERVAL = 5000;
const LOOK_INTERVAL = 3000;
const RECONNECT_DELAY = 10000;
const PLAYER_LIST_INTERVAL = 30 * 60 * 1000;
const BOT_STATS_INTERVAL = 60 * 60 * 1000;

const DEFAULT_EMBED_COLOR = 0x3498db;
const SUCCESS_EMBED_COLOR = 0x00ff00;
const WARNING_EMBED_COLOR = 0xff9900;
const ERROR_EMBED_COLOR = 0xff0000;
const INFO_EMBED_COLOR = 0x9b59b6;

const botOptions = {
  host: BOT_HOST,
  port: BOT_PORT,
  username: BOT_USERNAME,
  connectTimeout: null,
};

let bot = null;
let reconnectTimeout = null;
let movementInterval = null;
let lookInterval = null;
let playerListInterval = null;
let botStatsInterval = null;
let botStartTime = null;
let movementCount = 0;
let isBotOnline = false;
let lastOnlineTime = null;
let currentServerHost = BOT_HOST;
let currentServerPort = BOT_PORT;

function clearAllIntervals() {
  if (movementInterval) {
    clearInterval(movementInterval);
    movementInterval = null;
  }
  if (lookInterval) {
    clearInterval(lookInterval);
    lookInterval = null;
  }
  if (playerListInterval) {
    clearInterval(playerListInterval);
    playerListInterval = null;
  }
  if (botStatsInterval) {
    clearInterval(botStatsInterval);
    botStatsInterval = null;
  }
  if (reconnectTimeout) {
    clearTimeout(reconnectTimeout);
    reconnectTimeout = null;
  }
}

async function sendDiscordEmbed(title, description, color = DEFAULT_EMBED_COLOR, fields = []) {
  if (!DISCORD_WEBHOOK) {
    return;
  }
  try {
    await axios.post(DISCORD_WEBHOOK, {
      embeds: [{ title, description, color, fields, timestamp: new Date().toISOString() }],
    });
  } catch (err) {
    console.error('Discord Webhook Error:', err.message);
  }
}

async function sendChatEmbed(title, description, color = SUCCESS_EMBED_COLOR, fields = []) {
  if (!CHAT_WEBHOOK) {
    return;
  }
  try {
    await axios.post(CHAT_WEBHOOK, {
      embeds: [{ title, description, color, fields, timestamp: new Date().toISOString() }],
    });
  } catch (err) {
    console.error('Chat Webhook Error:', err.message);
  }
}

async function sendPlayerMessage(username, message) {
  if (username === botOptions.username || !MESSAGE_WEBHOOK) {
    return;
  }
  try {
    await axios.post(MESSAGE_WEBHOOK, {
      embeds: [{ author: { name: username }, description: message, color: SUCCESS_EMBED_COLOR, timestamp: new Date().toISOString() }],
    });
  } catch (err) {
    console.error('Message Webhook Error:', err.message);
  }
}

function sendPlayerList() {
  if (!bot || !bot.players) {
    return;
  }
  try {
    const playerList = Object.keys(bot.players)
      .filter(name => name !== botOptions.username)
      .map(name => ({
        name: name,
        ping: bot.players[name].ping || 'N/A',
        entity: bot.players[name].entity ? 'Yes' : 'No'
      }));
    if (playerList.length === 0) {
      sendChatEmbed('Player List', 'No players online', DEFAULT_EMBED_COLOR);
      return;
    }

    const fields = playerList.map(player => ({
      name: player.name,
      value: `Ping: ${player.ping}ms | In Range: ${player.entity}`,
      inline: true
    }));
    sendChatEmbed('Player List', `${playerList.length} player(s) online`, DEFAULT_EMBED_COLOR, fields);
  } catch (err) {
    console.error('Error sending player list:', err.message);
  }
}

function sendBotStats() {
  if (!bot || !bot.entity) {
    return;
  }
  try {
    const uptime = botStartTime ? Math.floor((Date.now() - botStartTime) / 1000) : 0;
    const hours = Math.floor(uptime / 3600);
    const minutes = Math.floor((uptime % 3600) / 60);
    const seconds = uptime % 60;
    const uptimeStr = `${hours}h ${minutes}m ${seconds}s`;
    const position = bot.entity.position;
    const posStr = `X: ${Math.floor(position.x)}, Y: ${Math.floor(position.y)}, Z: ${Math.floor(position.z)}`;
    const memoryUsage = process.memoryUsage();
    const memoryStr = `${Math.round(memoryUsage.rss / 1024 / 1024 * 100) / 100} MB`;
    const ping = bot.player ? bot.player.ping : 'Unknown';

    const gameModeDisplay = (bot?.gameMode === 3 || (bot?.gameMode === undefined && isBotOnline)) ?
      'Spectator' : 'Unknown';

    sendChatEmbed('Bot Status Report', `Status report for ${botOptions.username}`, INFO_EMBED_COLOR, [
      { name: 'Uptime', value: uptimeStr, inline: true },
      { name: 'Position', value: posStr, inline: true },
      { name: 'Game Mode', value: gameModeDisplay, inline: true },
      { name: 'Memory Usage', value: memoryStr, inline: true },
      { name: 'Ping', value: `${ping}ms`, inline: true },
      { name: 'Movement Count', value: `${movementCount} moves`, inline: true },
      { name: 'Server Load', value: `${os.loadavg()[0].toFixed(2)}`, inline: true }
    ]);
  } catch (err) {
    console.error('Error sending bot stats:', err.message);
  }
}

function performMovement() {
  if (!bot || !bot.entity) return;
  try {
    spectatorMovement();
    movementCount++;
  } catch (err) {
    console.error('Movement error:', err.message);
  }
}

function spectatorMovement() {
  const currentPos = bot.entity.position;
  const action = Math.random();
  if (action < 0.5) {
    const x = currentPos.x + (Math.random() * 10 - 5);
    const z = currentPos.z + (Math.random() * 10 - 5);
    bot.entity.position.set(x, currentPos.y, z);
  } else {
    const x = currentPos.x + (Math.random() * 10 - 5);
    const z = currentPos.z + (Math.random() * 10 - 5);
    bot.entity.position.set(x, currentPos.y, z);
  }
}

function lookAround() {
  if (!bot || !bot.entity) return;
  try {
    const yaw = Math.random() * Math.PI * 2;
    const pitch = (Math.random() * Math.PI / 3) - (Math.PI / 6);
    bot.look(yaw, pitch, true);
  } catch (err) {
    console.error('Look error:', err.message);
  }
}

function setupIntervals() {
  movementInterval = setInterval(performMovement, MOVEMENT_INTERVAL);
  lookInterval = setInterval(lookAround, LOOK_INTERVAL);
  playerListInterval = setInterval(sendPlayerList, PLAYER_LIST_INTERVAL);
  botStatsInterval = setInterval(sendBotStats, BOT_STATS_INTERVAL);
  setTimeout(sendPlayerList, 5000);
  setTimeout(sendBotStats, 10000);
}

function startBot() {
  clearAllIntervals();
  if (bot) {
    bot.removeAllListeners();
    bot = null;
  }

  botStartTime = Date.now();
  movementCount = 0;
  isBotOnline = false;

  bot = mineflayer.createBot(botOptions);

  bot.once('spawn', () => {
    sendDiscordEmbed('Bot Connected', `${botOptions.username} has joined the server.`, SUCCESS_EMBED_COLOR);
    isBotOnline = true;
    lastOnlineTime = Date.now();

    if (bot._client && bot._client.socket) {
      bot._client.socket.setKeepAlive(true, 30000);
      bot._client.socket.on('close', (hadError) => {
      });
    }
    setTimeout(() => {
      setupIntervals();
    }, 1000);
  });

  bot.on('game', () => {
    if (bot.gameMode === 3) {
      sendDiscordEmbed('Mode Change', `${botOptions.username} entered spectator mode.`, INFO_EMBED_COLOR);
    } else {
      sendDiscordEmbed('Mode Change', `${botOptions.username} entered an unknown game mode (${bot.gameMode}).`, WARNING_EMBED_COLOR);
    }
  });

  bot.on('end', (reason) => {
    sendDiscordEmbed('Bot Disconnect', `${botOptions.username} was disconnected. Reason: ${reason}.`, ERROR_EMBED_COLOR);
    isBotOnline = false;
    clearAllIntervals();
    reconnectBot();
  });
  bot.on('kicked', (reason) => {
    sendDiscordEmbed('Bot Kicked', `${botOptions.username} was kicked. Reason: ${reason}.`, ERROR_EMBED_COLOR);
    isBotOnline = false;
    clearAllIntervals();
    reconnectBot();
  });
  bot.on('error', (err) => {
    sendDiscordEmbed('Bot Error', `Error: ${err.message}`, ERROR_EMBED_COLOR);

    if (err.message.includes("timed out") ||
      err.message.includes("ECONNRESET") ||
      err.name === 'PartialReadError' ||
      err.message.includes("Unexpected buffer end")) {
      clearAllIntervals();
      reconnectBot();
    }
  });
  bot.on('chat', (username, message) => {
    if (username !== botOptions.username) {
      sendPlayerMessage(username, message);
    }
  });
  bot.on('playerJoined', (player) => {
    if (player.username !== botOptions.username) {
      if (player.username.startsWith('.')) {
        player.skinType = Math.random() > 0.5 ? 'alex' : 'steve';
      }
      const onlinePlayers = bot?.players ? Object.keys(bot.players).filter(name => name !== botOptions.username).length : 0;
      sendChatEmbed('Player Joined', `**${player.username}** joined the game.`, SUCCESS_EMBED_COLOR, [
        { name: 'Current Players', value: `${onlinePlayers}`, inline: true }
      ]);
    }
  });
  bot.on('playerLeft', (player) => {
    if (player.username !== botOptions.username) {
      const onlinePlayers = bot?.players ? Object.keys(bot.players).filter(name => name !== botOptions.username).length - 1 : 0;
      sendChatEmbed('Player Left', `**${player.username}** left the game.`, 0xff4500, [
        { name: 'Current Players', value: `${Math.max(0, onlinePlayers)}`, inline: true }
      ]);
    }
  });
}

function reconnectBot() {
  clearAllIntervals();
  reconnectTimeout = setTimeout(() => {
    startBot();
  }, RECONNECT_DELAY);
}

const app = express();

app.use(express.static(path.join(__dirname, 'public')));
app.get('/', (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'dashboard.html'));
});
app.get('/api/status', (req, res) => {
  try {
    const players = bot?.players ? Object.values(bot.players).filter(p => p.username !== botOptions.username) : [];
    const onlinePlayersCount = players.length;
    const playerDetails = players.map(p => {
      let skinUrl;
      if (p.username.startsWith('.')) {
        skinUrl = `./${p.skinType || (Math.random() > 0.5 ? 'steve' : 'alex')}.png`;
      } else {
        skinUrl = `https://crafatar.com/avatars/${p.uuid}?size=24&overlay`;
      }
      return {
        username: p.username,
        uuid: p.uuid,
        skinUrl: skinUrl
      };
    });

    const gameModeApiDisplay = (bot?.gameMode === 3 ||
      (bot?.gameMode === undefined && isBotOnline)) ? "Spectator" : "Unknown";

    const botStatus = {
      message: isBotOnline ?
        "Bot is running!" : "Bot is offline",
      onlinePlayersCount,
      playerDetails,
      gameMode: gameModeApiDisplay,
      position: bot?.entity?.position ?
        {
          x: Math.floor(bot.entity.position.x),
          y: Math.floor(bot.entity.position.y),
          z: Math.floor(bot.entity.position.z)
        } : null,
      uptime: botStartTime && isBotOnline ?
        Math.floor((Date.now() - botStartTime) / 1000) : 0,
      movements: movementCount,
      memoryUsage: `${Math.round(process.memoryUsage().rss / 1024 / 1024 * 100) / 100} MB`,
      lastOnline: lastOnlineTime,
      serverHost: currentServerHost,
      serverPort: currentServerPort,
    };
    res.json(botStatus);
  } catch (err) {
    res.status(500).json({ error: "Internal Server Error" });
  }
});
app.listen(WEB_SERVER_PORT, () => {
  sendDiscordEmbed('Web Server', `Web monitoring server started on port ${WEB_SERVER_PORT}`, DEFAULT_EMBED_COLOR);
});

startBot();
   
