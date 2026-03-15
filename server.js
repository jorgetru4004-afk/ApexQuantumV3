// ═══════════════════════════════════════════════════════════════
//  APEX QUANTUM V3.0 — Autonomous Crypto Trading Engine
//  Built clean from scratch — every feature intentional
//  Real prices via CoinGecko · Real execution via Coinbase
//  No simulation — pure intelligence
// ═══════════════════════════════════════════════════════════════

require('dotenv').config();
const express  = require('express');
const http     = require('http');
const WebSocket= require('ws');
const cron     = require('node-cron');
const axios    = require('axios');
const crypto   = require('crypto');
const fs       = require('fs');
const path     = require('path');

const app    = express();
const server = http.createServer(app);
const wss    = new WebSocket.Server({ server });

app.use(express.json());
app.use(express.static(__dirname));
app.get('/', (req, res) => res.sendFile(path.join(__dirname, 'index.html')));

const PORT = process.env.PORT || 3000;

// ── ENVIRONMENT ──
const ANTHROPIC_KEY   = process.env.ANTHROPIC_API_KEY  || '';
const CB_KEY          = process.env.COINBASE_API_KEY    || '';
const CB_SECRET       = process.env.COINBASE_API_SECRET || '';
const DISCORD_WEBHOOK = process.env.DISCORD_WEBHOOK     || '';

// ── PERSISTENCE ──
const DATA_DIR       = path.join(__dirname, 'data');
const TRADES_FILE    = path.join(DATA_DIR, 'trades.json');
const PATTERNS_FILE  = path.join(DATA_DIR, 'patterns.json');
const ROSTER_FILE    = path.join(DATA_DIR, 'roster.json');
const STATE_FILE     = path.join(DATA_DIR, 'state.json');
const WATCHLIST_FILE = path.join(DATA_DIR, 'watchlist.json');
const LEARNING_FILE  = path.join(DATA_DIR, 'learning.json');

if (!fs.existsSync(DATA_DIR)) fs.mkdirSync(DATA_DIR, { recursive: true });

function loadJSON(file, fallback) {
  try { return JSON.parse(fs.readFileSync(file, 'utf8')); } catch { return fallback; }
}
function saveJSON(file, data) {
  try { fs.writeFileSync(file, JSON.stringify(data, null, 2)); } catch(e) { console.error('Save:', e.message); }
}

// ── RESTORE STATE ──
const savedState = loadJSON(STATE_FILE, {});
let totalPnl     = savedState.totalPnl    || 0;
let totalTrades  = savedState.totalTrades || 0;
let totalWins    = savedState.totalWins   || 0;
let allTimePeak  = savedState.allTimePeak || 0;
let weeklyPnl    = savedState.weeklyPnl   || 0;

function saveState() {
  saveJSON(STATE_FILE, { totalPnl, totalTrades, totalWins, allTimePeak, weeklyPnl });
}

// ── SETTINGS ──
const SETTINGS = {
  stopLoss:         5,
  takeProfit:       10,  // crypto moves more — wider target
  trailingStop:     true,
  trailingPct:      4,
  budget:           200,
  budgetCeiling:    1000,
  dailyLossLimit:   150,
  maxDailyTrades:   30,  // crypto runs 24/7
  maxBots:          12,
  minBots:          4,
  cooldownSecs:     90,
  maxPortfolioHeat: 0.70,
  drawdownLimit:    0.10,
  blackSwanPct:     10,  // crypto-specific — 10% drop
  minConfidence:    60,    // lowered from 65 — allows more trades in normal conditions
  dualAIRequired:   true,
};

// ── COIN GECKO ID MAP ──
const GECKO_IDS = {
  'BTC':'bitcoin','ETH':'ethereum','SOL':'solana','DOGE':'dogecoin',
  'PEPE':'pepe','BONK':'bonk','WIF':'dogwifhat','AVAX':'avalanche-2',
  'AAVE':'aave','ONDO':'ondo-finance','TAO':'bittensor','HYPE':'hyperliquid',
  'PENDLE':'pendle','VIRTUAL':'virtual-protocol','JUP':'jupiter-exchange-solana',
  'RNDR':'render-token','SUI':'sui','INJ':'injective-protocol','TON':'the-open-network',
  'LINK':'chainlink','DOT':'polkadot','MATIC':'matic-network','ARB':'arbitrum',
  'OP':'optimism','APT':'aptos','NEAR':'near','FTM':'fantom','ALGO':'algorand',
  'XRP':'ripple','ADA':'cardano','LTC':'litecoin','BCH':'bitcoin-cash',
  'FIL':'filecoin','GRT':'the-graph','LDO':'lido-dao','CRV':'curve-dao-token',
  'FLOKI':'floki','SHIB':'shiba-inu','BRETT':'brett','POPCAT':'popcat',
};

// ── STATE ──
let tickers       = [];
let COINS         = {};
let bots          = {};
let hist          = {};
let vols          = {};
let sentimentMap  = {};
let aiDecisions   = {};
let ai2Decisions  = {};
let tickerHealth  = {};
let tradeCooldown = {};
let trailPeaks    = {};
let rotationLog   = [];
let newsItems     = [];
let watchlist     = loadJSON(WATCHLIST_FILE, []);
let tradeJournal  = loadJSON(TRADES_FILE,    []);
let patternData   = loadJSON(PATTERNS_FILE,  { patterns:{}, totalDecisions:0 });
let learning      = loadJSON(LEARNING_FILE,  {
  hourlyWR:{}, sectorWR:{}, patternWR:{},
  lastOptimized:null
});

let botBudgets       = {};
let consecutiveWins  = {};

let dailyTrades  = 0;
let dailyLoss    = 0;
let dailyPnl     = 0;

let coinbaseConnected = false;
let cryptoRegime      = 'NEUTRAL'; // BULL / BEAR / NEUTRAL / VOLATILE
let fearGreedIndex    = 50;
let btcDominance      = 55;
let portfolioHeat     = 0;
let paused            = false;
let pauseReason       = '';
let lastAnalyzeTime   = null;
let lastRotateTime    = null;
let lastScanTime      = null;

// ── AUTO CAPITAL SCALING ──
function getBotBudget(sym) { return botBudgets[sym] || SETTINGS.budget; }

function scaleBudget(sym, won) {
  if (!botBudgets[sym])      botBudgets[sym]      = SETTINGS.budget;
  if (!consecutiveWins[sym]) consecutiveWins[sym]  = 0;
  if (won) {
    consecutiveWins[sym]++;
    if (consecutiveWins[sym] % 3 === 0) {
      botBudgets[sym] = Math.min(SETTINGS.budgetCeiling, parseFloat((botBudgets[sym]*1.10).toFixed(2)));
      console.log(`📈 ${sym} budget scaled to $${botBudgets[sym]}`);
    }
  } else {
    consecutiveWins[sym] = 0;
    botBudgets[sym] = Math.max(SETTINGS.budget, parseFloat((botBudgets[sym]*0.90).toFixed(2)));
  }
}

// ── COLORS ──
const COIN_COLORS = {
  BTC:'#f7931a', ETH:'#627eea', SOL:'#9945ff', DOGE:'#c2a633',
  PEPE:'#4caf50', BONK:'#f97316', WIF:'#e879f9', AVAX:'#e84142',
  AAVE:'#b6509e', ONDO:'#00d4aa', TAO:'#14b8a6', HYPE:'#6366f1',
  PENDLE:'#3b82f6', VIRTUAL:'#8b5cf6', JUP:'#22c55e', RNDR:'#ef4444',
  SUI:'#4da2ff', INJ:'#00b2ff', TON:'#0088cc', LINK:'#2a5ada',
  ARB:'#28a0f0', OP:'#ff0420', NEAR:'#00c08b',
};
const DEFAULT_COLORS = ['#00f5ff','#a855f7','#00ff88','#fbbf24','#ff6b6b','#06d6a0','#ffb347'];
function getCoinColor(sym) { return COIN_COLORS[sym] || DEFAULT_COLORS[tickers.length % DEFAULT_COLORS.length]; }

// ── INIT COIN ──
function initCoin(sym, price, mktCapB, vol24B, sector, color) {
  price = Math.max(0.00001, parseFloat(price) || 1);
  COINS[sym] = {
    name: sym, price,
    prev: price * 0.98,
    mktCap: parseFloat(mktCapB) || 1,
    vol24:  parseFloat(vol24B)  || 0.1,
    color:  color || getCoinColor(sym),
    sector: sector || 'Crypto',
    change24: 0, high24: price*1.05, low24: price*0.95,
    realPrice: false,
    geckoId: GECKO_IDS[sym] || sym.toLowerCase(),
  };
  hist[sym]         = Array.from({length:60},(_,i)=>parseFloat((price*(0.95+i*0.0009)).toFixed(8)));
  vols[sym]         = parseFloat(vol24B)||0.1;
  sentimentMap[sym] = { reddit:50, twitter:50, news:50, fearGreed:50, overall:50 };
  bots[sym] = {
    on:true, status:'WARMING UP', pos:0, entry:0, pnl:0,
    trades:0, wins:0, halted:false,
    vwap:price, vS:price, vC:1,
    pattern:'NONE', aiApproved:null, ai2Approved:null,
    allocated:0, sizingLabel:'FULL', confidence:0,
    sector: sector||'Crypto',
    regime: cryptoRegime
  };
  tickerHealth[sym]  = { score:50, noTradeCount:0, consecutiveLosses:0 };
  tradeCooldown[sym] = 0;
  trailPeaks[sym]    = 0;
  botBudgets[sym]    = SETTINGS.budget;
  consecutiveWins[sym] = 0;
}

// ── WEBSOCKET ──
function broadcast(type, data) {
  const msg = JSON.stringify({ type, data, ts:Date.now() });
  wss.clients.forEach(c => { if (c.readyState===WebSocket.OPEN) try{c.send(msg);}catch(e){} });
}

wss.on('connection', ws => {
  console.log('📱 Dashboard connected');
  ws.send(JSON.stringify({ type:'SNAPSHOT', data:getSnapshot() }));
});

function getSnapshot() {
  return {
    tickers, COINS, bots, hist, vols, sentimentMap,
    aiDecisions, ai2Decisions, tickerHealth, rotationLog, newsItems,
    totalPnl, totalTrades, totalWins, dailyTrades, dailyLoss, dailyPnl,
    weeklyPnl, allTimePeak, portfolioHeat, paused, pauseReason,
    tradeJournal: tradeJournal.slice(0,50),
    patternData, SETTINGS, coinbaseConnected,
    cryptoRegime, fearGreedIndex, btcDominance,
    learning, watchlist: watchlist.slice(0,20),
    lastAnalyzeTime, lastRotateTime, lastScanTime,
    botBudgets, serverTime: new Date().toISOString()
  };
}

// ── REAL PRICES — COINGECKO ──
async function fetchCoinGeckoPrices() {
  if (!tickers.length) return;
  const ids = tickers.map(sym => COINS[sym]?.geckoId || GECKO_IDS[sym] || sym.toLowerCase()).join(',');
  try {
    const resp = await axios.get(
      `https://api.coingecko.com/api/v3/simple/price?ids=${ids}&vs_currencies=usd&include_24hr_change=true&include_24hr_vol=true&include_market_cap=true`,
      { timeout: 10000 }
    );
    const data = resp.data || {};
    let updated = 0;
    tickers.forEach(sym => {
      const geckoId = COINS[sym]?.geckoId || GECKO_IDS[sym] || sym.toLowerCase();
      const d = data[geckoId];
      if (!d) return;
      const s = COINS[sym];
      if (!s) return;
      const realPrice   = d.usd;
      s.prev            = s.price;
      s.price           = realPrice;
      s.change24        = parseFloat((d.usd_24h_change || 0).toFixed(2));
      s.vol24           = parseFloat(((d.usd_24h_vol || 0) / 1e9).toFixed(3));
      s.mktCap          = parseFloat(((d.usd_market_cap || 0) / 1e9).toFixed(2));
      s.high24          = Math.max(s.high24, realPrice * 1.001);
      s.low24           = Math.min(s.low24,  realPrice * 0.999);
      s.realPrice       = true;
      hist[sym].push(realPrice);
      if (hist[sym].length > 200) hist[sym].shift();
      // VWAP
      const b = bots[sym];
      b.vC++; b.vS += realPrice;
      b.vwap = parseFloat((b.vS/b.vC).toFixed(8));
      updated++;
      if (b.on && !b.halted && !paused) runBotLogic(sym);
    });
    if (updated > 0) {
      broadcast('PRICES', {
        prices:  Object.fromEntries(tickers.map(s=>[s, COINS[s]?.price])),
        changes: Object.fromEntries(tickers.map(s=>[s, COINS[s]?.change24])),
        bots:    Object.fromEntries(tickers.map(s=>[s, bots[s]])),
        totalPnl, totalTrades, totalWins, dailyPnl, portfolioHeat
      });
    }
  } catch(e) { console.log('⚠️ CoinGecko:', e.message); }
}

// ── FEAR & GREED + MARKET REGIME ──
async function fetchMarketConditions() {
  // Fear & Greed
  try {
    const resp = await axios.get('https://api.alternative.me/fng/?limit=1', { timeout:8000 });
    fearGreedIndex = parseInt(resp.data?.data?.[0]?.value || 50);
  } catch(e) {}

  // BTC dominance — determines alt season
  try {
    const resp = await axios.get('https://api.coingecko.com/api/v3/global', { timeout:8000 });
    btcDominance = parseFloat(resp.data?.data?.market_cap_percentage?.btc || 55);
  } catch(e) {}

  // Determine crypto regime
  const prevRegime = cryptoRegime;
  if (fearGreedIndex <= 20) {
    cryptoRegime = 'EXTREME FEAR';
    if (!paused && fearGreedIndex <= 10) {
      paused = true;
      pauseReason = `Extreme Fear ${fearGreedIndex} — brain in protective mode`;
    }
  } else if (fearGreedIndex <= 40) {
    cryptoRegime = 'FEAR';
  } else if (fearGreedIndex >= 80) {
    cryptoRegime = 'EXTREME GREED';
  } else if (fearGreedIndex >= 60) {
    cryptoRegime = 'GREED';
    if (paused && pauseReason.includes('Extreme Fear')) { paused=false; pauseReason=''; }
  } else {
    cryptoRegime = 'NEUTRAL';
    if (paused && pauseReason.includes('Extreme Fear')) { paused=false; pauseReason=''; }
  }

  // Check BTC for black swan
  const btc = COINS['BTC'];
  if (btc && btc.change24 <= -SETTINGS.blackSwanPct && !paused) {
    paused      = true;
    pauseReason = `BTC crashed ${btc.change24}% — Black Swan protection active`;
    sendDiscordAlert(`🛑 **BLACK SWAN DETECTED**\nBTC: ${btc.change24}%\nAll trading paused — protecting capital`);
  } else if (btc && btc.change24 > -5 && paused && pauseReason.includes('Black Swan')) {
    paused = false; pauseReason = '';
  }

  if (prevRegime !== cryptoRegime) {
    console.log(`📊 Crypto regime: ${prevRegime} → ${cryptoRegime} (F&G: ${fearGreedIndex})`);
    broadcast('REGIME_CHANGE', { cryptoRegime, fearGreedIndex, btcDominance });
    if (cryptoRegime === 'EXTREME FEAR') {
      sendDiscordAlert(`⚠️ **EXTREME FEAR: ${fearGreedIndex}**\nMarket in panic — brain switching defensive\nLooking for oversold bounces only`);
    } else if (cryptoRegime === 'EXTREME GREED') {
      sendDiscordAlert(`🔥 **EXTREME GREED: ${fearGreedIndex}**\nMarket euphoric — tightening stops\nUsing momentum but watching for reversal`);
    }
  }
  broadcast('MARKET_CONDITIONS', { fearGreedIndex, cryptoRegime, btcDominance, paused, pauseReason });
}

// ── SIGNALS ──
function getSignals(sym) {
  const h = hist[sym], s = COINS[sym], b = bots[sym];
  if (!h || h.length < 20) return {
    rsi:50, volStrength:50, momentum:50, squeeze:30, sentiment:50,
    macd:0, bb:50, trend:'NEUTRAL', pattern:{ name:'NONE', signal:'WAIT' }, rr:2
  };
  // RSI
  let g=0, l=0;
  for (let i=h.length-14; i<h.length; i++) {
    const d = h[i]-(h[i-1]||h[i]);
    if(d>0) g+=d; else l-=d;
  }
  const rsi = Math.round(100-100/(1+(g/(l||0.001))));
  // Momentum
  const chg24   = s.change24 || 0;
  const momentum= Math.min(100,Math.max(0,Math.round(50+chg24*2)));
  // MACD
  const ema12   = h.slice(-12).reduce((a,v)=>a+v,0)/12;
  const ema26   = h.slice(-26).reduce((a,v)=>a+v,0)/Math.min(26,h.length);
  const macd    = parseFloat(((ema12-ema26)/(ema26||1)*100).toFixed(3));
  // Bollinger
  const mean    = h.slice(-20).reduce((a,v)=>a+v,0)/20;
  const std     = Math.sqrt(h.slice(-20).map(x=>(x-mean)**2).reduce((a,v)=>a+v,0)/20);
  const bb      = std>0?Math.round((s.price-mean)/std*50+50):50;
  // Volume strength (relative to market cap)
  const volStrength = Math.min(100,Math.round(s.vol24/(s.mktCap||1)*100));
  // Alt season boost (if BTC dominance falling, alts pump)
  const altBoost = btcDominance < 50 && sym !== 'BTC' ? 10 : 0;
  // Sentiment
  const sn = sentimentMap[sym];
  const sent = Math.min(99, Math.round(sn.overall + altBoost));
  // Pattern
  const patterns = ['BREAKOUT','BULL FLAG','OVERSOLD BOUNCE','MOMENTUM','VWAP RECLAIM','WHALE ACCUMULATION','SHORT SQUEEZE'];
  let pi = 3;
  if (rsi < 30 && chg24 > 0)          pi = 2; // oversold bounce
  else if (macd > 0 && momentum > 70) pi = 1; // bull flag
  else if (chg24 > 15 && macd > 0)    pi = 0; // breakout
  else if (s.price > b.vwap && macd>0) pi = 4; // vwap reclaim
  else if (volStrength > 60)           pi = 5; // whale accumulation
  const trend = macd > 0 && momentum > 50 ? 'BULLISH' : macd < 0 ? 'BEARISH' : 'NEUTRAL';
  return {
    rsi, volStrength, momentum, squeeze:Math.min(100,rsi<40?60:30),
    sentiment:sent, macd, bb, trend,
    pattern:{ name:patterns[pi], signal:pi<6?'BUY':'WAIT' },
    rr: parseFloat((SETTINGS.takeProfit/SETTINGS.stopLoss).toFixed(1))
  };
}

function getPositionSize(sym) {
  const conf   = Math.max(aiDecisions[sym]?.confidence||0, ai2Decisions[sym]?.confidence||0);
  const budget = getBotBudget(sym);
  // Reduce size in extreme fear
  const regimeMult = cryptoRegime==='EXTREME FEAR'?0.5:cryptoRegime==='FEAR'?0.75:1.0;
  let pct, label;
  if (conf >= 90)      { pct=1.00; label='FULL'; }
  else if (conf >= 80) { pct=0.75; label='75%'; }
  else if (conf >= 70) { pct=0.50; label='50%'; }
  else                 { pct=0.25; label='25%'; }
  const dollars = parseFloat((budget*pct*regimeMult).toFixed(2));
  return { dollars, pct, label, confidence:conf, regimeMult };
}

function calcPortfolioHeat() {
  const total = tickers.reduce((s,sym) => s+(bots[sym]?.pos>0?bots[sym].allocated||0:0), 0);
  const budget= tickers.length * SETTINGS.budget;
  portfolioHeat = budget>0?parseFloat((total/budget).toFixed(2)):0;
  return portfolioHeat;
}

function checkDrawdown() {
  if (totalPnl > allTimePeak) { allTimePeak=totalPnl; saveState(); }
  const dd = allTimePeak>0?(allTimePeak-totalPnl)/allTimePeak:0;
  if (dd>=SETTINGS.drawdownLimit&&!paused) {
    paused=true; pauseReason=`Drawdown protection — down ${(dd*100).toFixed(1)}% from peak`;
    sendDiscordAlert(`🛑 **DRAWDOWN PROTECTION**\nDown ${(dd*100).toFixed(1)}% from peak — pausing all trades`);
    broadcast('PAUSED',{paused,pauseReason});
  } else if (dd<SETTINGS.drawdownLimit*0.5&&paused&&pauseReason.includes('Drawdown')) {
    paused=false; pauseReason=''; broadcast('RESUMED',{paused});
  }
}

// ── BOT LOGIC ──
function runBotLogic(sym) {
  if (paused) return;
  if (dailyTrades >= SETTINGS.maxDailyTrades) return;
  if (dailyLoss   >= SETTINGS.dailyLossLimit) return;
  const s=COINS[sym], b=bots[sym];
  if (!s||!b||b.halted) return;
  const sg = getSignals(sym);

  // ── EXIT ──
  if (b.pos > 0) {
    const pct    = (s.price-b.entry)/b.entry*100;
    const profit = b.pos*(s.price-b.entry);
    if (s.price>(trailPeaks[sym]||0)) trailPeaks[sym]=s.price;
    const trailDrop     = trailPeaks[sym]>0?(trailPeaks[sym]-s.price)/trailPeaks[sym]*100:0;
    const trailTriggered= SETTINGS.trailingStop&&trailDrop>=SETTINGS.trailingPct&&profit>0;
    const stopTriggered = pct<=-SETTINGS.stopLoss;
    const tgtTriggered  = pct>=SETTINGS.takeProfit;
    if (stopTriggered||tgtTriggered||trailTriggered) {
      const pnl  = parseFloat((b.pos*(s.price-b.entry)).toFixed(2));
      b.pnl     += pnl; totalPnl=parseFloat((totalPnl+pnl).toFixed(2));
      dailyPnl   = parseFloat((dailyPnl+pnl).toFixed(2));
      weeklyPnl  = parseFloat((weeklyPnl+pnl).toFixed(2));
      dailyTrades++;
      const won = pnl>0;
      if (won){b.wins++;totalWins++;}else{dailyLoss+=Math.abs(pnl);tickerHealth[sym].consecutiveLosses++;}
      b.trades++;totalTrades++;
      const exitPrice=s.price, entryPrice=b.entry;
      b.pos=0;b.entry=0;b.status='WATCHING';b.aiApproved=null;b.ai2Approved=null;
      tradeCooldown[sym]=Date.now(); trailPeaks[sym]=0;
      if(won) tickerHealth[sym].consecutiveLosses=0;
      const reason=trailTriggered?'TRAIL STOP':tgtTriggered?'TARGET HIT':'STOP LOSS';
      scaleBudget(sym,won);
      updateLearning(sym,won,sg,pnl);
      const trade=logTrade(sym,entryPrice,exitPrice,b.allocated,pnl,reason,sg);
      sendDiscordTrade(trade);
      if(coinbaseConnected) placeCoinbaseOrder(sym,'SELL',b.allocated/exitPrice).catch(()=>{});
      learnFromTrade(sym,trade,aiDecisions[sym]);
      saveState(); checkDrawdown();
      broadcast('TRADE',{trade,bot:bots[sym],totalPnl,totalTrades,totalWins,dailyPnl,weeklyPnl});
      if(won&&pnl>30) momentumChain(s.sector);
    } else {
      b.status=pct>5?'RIPPING 🚀':pct>0?'WINNING ✅':'HOLDING';
    }
    return;
  }

  // ── COOLDOWN ──
  if(Date.now()-(tradeCooldown[sym]||0)<SETTINGS.cooldownSecs*1000){b.status='COOLDOWN';return;}
  if(calcPortfolioHeat()>=SETTINGS.maxPortfolioHeat){b.status='HEAT LIMIT';return;}
  if((tickerHealth[sym]?.consecutiveLosses||0)>=2){b.status='FLAGGED';return;}

  // ── ENTRY SIGNALS ──
  const regimeOk = cryptoRegime!=='EXTREME FEAR' || sg.rsi<30; // allow bounce in extreme fear
  const signalOk = sg.rsi<70&&sg.momentum>45&&sg.macd>-0.5;
  if(!regimeOk||!signalOk){b.status='WATCHING';return;}

  // ── DUAL AI ──
  const dec1=aiDecisions[sym], dec2=ai2Decisions[sym];
  if(!dec1||!dec2){b.status='WAITING AI';return;}
  if(dec1.verdict!=='YES'){b.status='AI1 SKIP';return;}
  if(dec2.verdict!=='YES'){b.status='AI2 SKIP';return;}
  if(dec1.confidence<SETTINGS.minConfidence){b.status='LOW CONF';return;}
  if(dec2.confidence<SETTINGS.minConfidence){b.status='LOW CONF';return;}

  // ── ENTER ──
  const sizing=getPositionSize(sym);
  tradeCooldown[sym]=Date.now();
  b.pos         = sizing.dollars/s.price; // fractional crypto
  b.entry       = s.price;
  b.allocated   = sizing.dollars;
  b.sizingLabel = sizing.label;
  b.confidence  = sizing.confidence;
  b.status      = 'IN POSITION';
  b.pattern     = sg.pattern.name;
  b.aiApproved  = true;
  b.ai2Approved = true;
  b.regime      = cryptoRegime;
  trailPeaks[sym]=s.price;

  console.log(`⚡ ENTRY: ${sym} @ $${s.price} | ${sizing.label} ($${sizing.dollars}) | AI1:${dec1.confidence}% AI2:${dec2.confidence}%`);
  sendDiscordAlert(
    `⚡ **${sym} ENTRY** @ $${formatPrice(s.price)}\n`+
    `💰 Size: ${sizing.label} ($${sizing.dollars})\n`+
    `🧠 AI1: ${dec1.confidence}% · AI2: ${dec2.confidence}%\n`+
    `📊 Pattern: ${sg.pattern.name} · RSI: ${sg.rsi} · Trend: ${sg.trend}\n`+
    `😱 Fear & Greed: ${fearGreedIndex} · Regime: ${cryptoRegime}`
  );
  if(coinbaseConnected) placeCoinbaseOrder(sym,'BUY',sizing.dollars).catch(()=>{});
  broadcast('ENTRY',{sym,price:s.price,sizing,bot:bots[sym]});
}

async function momentumChain(sector) {
  const candidates = tickers.filter(s=>COINS[s]?.sector===sector&&bots[s]?.pos===0);
  for (const sym of candidates) {
    const sg=getSignals(sym);
    if(sg.momentum>65&&sg.volStrength>40){
      await askAI(sym,'primary'); await askAI(sym,'secondary');
    }
  }
}

// ── LOGS & LEARNING ──
function logTrade(sym,entry,exit,allocated,pnl,reason,sg) {
  const now=new Date();
  const trade={
    id:tradeJournal.length+1, sym, entry, exit, allocated, pnl, reason,
    pattern:sg?.pattern?.name||'—', sentiment:sentimentMap[sym]?.overall||0,
    aiVerdict:aiDecisions[sym]?.verdict||'—', ai2Verdict:ai2Decisions[sym]?.verdict||'—',
    aiConf:aiDecisions[sym]?.confidence||0, ai2Conf:ai2Decisions[sym]?.confidence||0,
    regime:cryptoRegime, fearGreed:fearGreedIndex,
    hour:now.getHours(), sector:COINS[sym]?.sector||'—',
    date:now.toLocaleDateString(), time:now.toLocaleTimeString()
  };
  tradeJournal.unshift(trade);
  if(tradeJournal.length>1000) tradeJournal.pop();
  saveJSON(TRADES_FILE,tradeJournal);
  return trade;
}

function learnFromTrade(sym,trade,aiDec) {
  if(!aiDec) return;
  const key=`${trade.pattern}_${trade.sector}_${trade.hour}`;
  if(!patternData.patterns[key]) patternData.patterns[key]={wins:0,losses:0,totalPnl:0,avgConf:0,count:0};
  const p=patternData.patterns[key]; p.count++;
  if(trade.pnl>0) p.wins++; else p.losses++;
  p.totalPnl=parseFloat((p.totalPnl+trade.pnl).toFixed(2));
  p.avgConf=parseFloat(((p.avgConf*(p.count-1)+(aiDec.confidence||0))/p.count).toFixed(1));
  patternData.totalDecisions++;
  saveJSON(PATTERNS_FILE,patternData);
}

function updateLearning(sym,won,sg,pnl) {
  const now=new Date(); const hour=now.getHours().toString();
  const sector=COINS[sym]?.sector||'Unknown'; const pattern=sg.pattern.name;
  if(!learning.hourlyWR[hour]) learning.hourlyWR[hour]={wins:0,total:0};
  learning.hourlyWR[hour].total++; if(won) learning.hourlyWR[hour].wins++;
  if(!learning.sectorWR[sector]) learning.sectorWR[sector]={wins:0,total:0,totalPnl:0};
  learning.sectorWR[sector].total++; if(won) learning.sectorWR[sector].wins++;
  learning.sectorWR[sector].totalPnl=parseFloat((learning.sectorWR[sector].totalPnl+pnl).toFixed(2));
  if(!learning.patternWR[pattern]) learning.patternWR[pattern]={wins:0,total:0};
  learning.patternWR[pattern].total++; if(won) learning.patternWR[pattern].wins++;
  saveJSON(LEARNING_FILE,learning);
}

// ── DUAL AI ──
async function askAI(sym, role='primary') {
  if(!ANTHROPIC_KEY) return;
  const s=COINS[sym], sg=getSignals(sym), b=bots[sym];
  if(!s) return;
  const patKey=`${sg.pattern.name}_${s.sector}_${new Date().getHours()}`;
  const patStats=patternData.patterns[patKey];
  const patHistory=patStats
    ?`${sg.pattern.name} at this hour: ${patStats.wins}W/${patStats.losses||0}L`
    :'No history yet';
  const sectorStats=learning.sectorWR[s.sector];
  const sectorPerf=sectorStats?.total>=3
    ?`${s.sector}: ${Math.round(sectorStats.wins/sectorStats.total*100)}% WR (${sectorStats.total} trades)`
    :'Building data';
  const rolePrompt=role==='secondary'
    ?`You are QUANTUM VERIFIER #2. Your job is to challenge the primary AI and find reasons NOT to trade. Be skeptical and conservative.`
    :`You are QUANTUM ANALYST #1. Expert crypto trader specializing in momentum, breakouts, and sentiment-driven moves.`;
  const prompt=
    `${rolePrompt}\n\n`+
    `Crypto: ${sym} | Price: $${formatPrice(s.price)} | 24h: ${s.change24}%\n`+
    `RSI: ${sg.rsi} | Momentum: ${sg.momentum}/100 | Trend: ${sg.trend}\n`+
    `MACD: ${sg.macd} | Bollinger: ${sg.bb}/100 | Vol Strength: ${sg.volStrength}\n`+
    `Market Cap: $${s.mktCap}B | 24h Volume: $${s.vol24}B\n`+
    `VWAP: ${s.price>b.vwap?'ABOVE ✅':'BELOW ⚠️'} | Pattern: ${sg.pattern.name}\n`+
    `Fear & Greed: ${fearGreedIndex} | BTC Dominance: ${btcDominance}% | Regime: ${cryptoRegime}\n`+
    `Sentiment: ${sg.sentiment}/100 | Pattern History: ${patHistory}\n`+
    `Sector: ${sectorPerf}\n\n`+
    `Respond ONLY with JSON: {"verdict":"YES" or "NO","confidence":0-100,"reason":"2 sentences max","entry":${formatPrice(s.price)},"stop":float,"target":float,"risk":"LOW|MEDIUM|HIGH","catalyst":"key driver"}`;

  const target=role==='primary'?aiDecisions:ai2Decisions;
  target[sym]={verdict:'THINKING',confidence:0,sym,role,time:new Date().toLocaleTimeString()};
  broadcast('AI_DECISION',{sym,role,decision:target[sym]});
  try {
    const resp=await axios.post('https://api.anthropic.com/v1/messages',{
      model:'claude-sonnet-4-6',max_tokens:400,
      messages:[{role:'user',content:prompt}]
    },{headers:{'Content-Type':'application/json','x-api-key':ANTHROPIC_KEY,'anthropic-version':'2023-06-01'}});
    const txt=resp.data?.content?.[0]?.text||'{}';
    const dec=JSON.parse(txt.replace(/```json|```/g,'').trim());
    dec.sym=sym;dec.role=role;dec.time=new Date().toLocaleTimeString();
    target[sym]=dec;
    console.log(`🧠 ${role==='primary'?'AI1':'AI2'} ${sym}: ${dec.verdict} (${dec.confidence}%)`);
    broadcast('AI_DECISION',{sym,role,decision:dec});
    if(role==='secondary'&&dec.verdict==='YES'&&aiDecisions[sym]?.verdict==='YES') {
      sendDiscordAlert(
        `🧠🧠 **QUANTUM DUAL AI: ${sym}**\n`+
        `AI1: ${aiDecisions[sym].confidence}% · AI2: ${dec.confidence}%\n`+
        `💡 ${dec.reason}\n`+
        `🎯 Entry $${dec.entry} · Stop $${dec.stop} · Target $${dec.target}`
      );
    }
  } catch(e) {
    console.error(`AI ${role} error ${sym}:`,e.message);
    target[sym]={verdict:'ERROR',confidence:0,sym,role,reason:e.message.slice(0,60),time:new Date().toLocaleTimeString()};
  }
}

async function analyzeAll() {
  if(!tickers.length) return;
  const toAnalyze=tickers.filter(sym=>!bots[sym]||bots[sym].pos===0);
  if(!toAnalyze.length) return;
  lastAnalyzeTime=new Date();
  console.log(`🧠 Analyzing ${toAnalyze.length} coins (smart dual AI)...`);
  for(const sym of toAnalyze) {
    const dec=aiDecisions[sym];
    if(dec&&dec.verdict!=='ERROR'&&dec.verdict!=='THINKING') {
      const ageMs=Date.now()-new Date().setHours(
        parseInt(dec.time?.split(':')[0]||0),parseInt(dec.time?.split(':')[1]||0),0,0);
      if(ageMs<300000) continue; // Skip if fresh decision under 5 min
    }
    // AI #1 first
    await askAI(sym,'primary'); await sleep(400);
    // Only call AI #2 if AI #1 said YES — saves 60% of API costs
    if(aiDecisions[sym]?.verdict==='YES') {
      await askAI(sym,'secondary'); await sleep(400);
    } else {
      ai2Decisions[sym]={verdict:'SKIPPED',confidence:0,sym,role:'secondary',
        reason:'AI1 rejected — AI2 not needed',time:new Date().toLocaleTimeString()};
    }
  }
  broadcast('ANALYZE_COMPLETE',{count:toAnalyze.length,time:lastAnalyzeTime});
}

// ── CRYPTO SCANNER ──
async function scanCrypto(scanType) {
  if(!ANTHROPIC_KEY) return [];
  lastScanTime=new Date();
  const existing=tickers.length?`Currently tracking: ${tickers.join(', ')}. Find DIFFERENT coins.`:'';
  const hotSectors=Object.entries(learning.sectorWR)
    .filter(([,v])=>v.total>=3).sort(([,a],[,b])=>(b.wins/b.total)-(a.wins/a.total))
    .slice(0,2).map(([s])=>s).join(', ')||'any sector';
  const scanFocus={
    full:     `top 6 crypto opportunities right now based on momentum — prioritize ${hotSectors}`,
    memes:    '6 hottest meme coins with active communities and volume surging — PEPE BONK WIF BRETT style',
    defi:     '6 DeFi tokens with strong fundamentals and recent catalyst — AAVE PENDLE ONDO style',
    layer1:   '6 L1/L2 blockchain tokens with ecosystem growth — SOL AVAX SUI ARB style',
    whale:    '6 crypto assets showing whale accumulation patterns — large buy volume, price stability',
    momentum: '6 highest momentum cryptos with RSI 50-70 and volume surge',
  };
  const prompt=
    `You are an elite crypto scanner. Fear & Greed Index: ${fearGreedIndex}. BTC Dominance: ${btcDominance}%.\n`+
    `Market Regime: ${cryptoRegime}. ${existing}\n`+
    `Find: ${scanFocus[scanType]||scanFocus.full}\n\n`+
    `Return ONLY JSON array:\n`+
    `[{"sym":"TICKER","name":"Coin Name","price":float,"mktCapB":float,"vol24B":float,`+
    `"sector":"DeFi|Meme|Layer1|Layer2|AI|Gaming|RWA","score":0-100,`+
    `"catalyst":"specific reason why NOW","ai_verdict":"YES" or "WATCH","confidence":0-100,`+
    `"entry":float,"stop":float,"target":float}]`;
  try {
    const resp=await axios.post('https://api.anthropic.com/v1/messages',{
      model:'claude-sonnet-4-6',max_tokens:1500,
      messages:[{role:'user',content:prompt}]
    },{headers:{'Content-Type':'application/json','x-api-key':ANTHROPIC_KEY,'anthropic-version':'2023-06-01'}});
    const txt=resp.data?.content?.[0]?.text||'[]';
    const results=JSON.parse(txt.replace(/```json|```/g,'').trim());
    broadcast('DISCOVERY_RESULTS',{results,scanType});
    for(const r of results) {
      if(r.ai_verdict==='YES'&&!tickers.includes(r.sym)&&tickers.length<SETTINGS.maxBots){
        addCoin(r); await sleep(400);
      } else if(r.ai_verdict==='WATCH'&&!tickers.includes(r.sym)&&!watchlist.find(w=>w.sym===r.sym)){
        watchlist.unshift({sym:r.sym,catalyst:r.catalyst,score:r.score,added:new Date().toISOString()});
        if(watchlist.length>30) watchlist.pop();
        saveJSON(WATCHLIST_FILE,watchlist);
      }
    }
    return results;
  } catch(e) { console.error('Scan error:',e.message); return []; }
}

async function reviewWatchlist() {
  if(!watchlist.length) return;
  for(const item of watchlist.slice(0,8)) {
    const sym=item.sym;
    if(tickers.includes(sym)||tickers.length>=SETTINGS.maxBots) continue;
    const prompt=`Is ${sym} ready to trade? It was watchlisted for: ${item.catalyst}\nFear & Greed: ${fearGreedIndex}. Respond ONLY with JSON: {"ready":true/false,"reason":"one sentence"}`;
    try {
      const resp=await axios.post('https://api.anthropic.com/v1/messages',{
        model:'claude-sonnet-4-6',max_tokens:100,
        messages:[{role:'user',content:prompt}]
      },{headers:{'Content-Type':'application/json','x-api-key':ANTHROPIC_KEY,'anthropic-version':'2023-06-01'}});
      const dec=JSON.parse((resp.data?.content?.[0]?.text||'{}').replace(/```json|```/g,'').trim());
      if(dec.ready){
        addCoin({sym,catalyst:item.catalyst,ai_verdict:'YES',confidence:70,price:1,sector:'Crypto'});
        watchlist=watchlist.filter(w=>w.sym!==sym);
        saveJSON(WATCHLIST_FILE,watchlist);
      }
    } catch(e) {}
    await sleep(500);
  }
}

// ── ROSTER ──
function addCoin(disc) {
  const sym=(disc.sym||'').toUpperCase().trim();
  if(!sym||tickers.includes(sym)||tickers.length>=SETTINGS.maxBots) return;
  initCoin(sym, disc.price||1, disc.mktCapB||1, disc.vol24B||0.1, disc.sector||'Crypto', getCoinColor(sym));
  tickers.push(sym);
  if(disc.ai_verdict) {
    aiDecisions[sym]={sym,verdict:disc.ai_verdict,confidence:disc.confidence||70,
      reason:disc.catalyst||'AI selected',entry:disc.entry,stop:disc.stop,target:disc.target,
      time:new Date().toLocaleTimeString()};
  }
  addRotationLog('ADD',sym,(disc.catalyst||'AI selected').slice(0,60));
  saveJSON(ROSTER_FILE,tickers);
  console.log(`➕ ${sym} added | $${formatPrice(disc.price||1)} | ${disc.sector||'Crypto'}`);
  sendDiscordAlert(`➕ **NEW BOT: ${sym}**\n📊 ${disc.catalyst||'AI selected'}\n💰 Conf: ${disc.confidence||70}%`);
  broadcast('TICKER_ADDED',{sym,stock:COINS[sym],bot:bots[sym],hist:hist[sym],sent:sentimentMap[sym]});
}

function dropCoin(sym,reason) {
  if(!tickers.includes(sym)) return false;
  if(tickers.length<=SETTINGS.minBots) return false;
  if(bots[sym]?.pos>0) return false;
  tickers=tickers.filter(s=>s!==sym);
  delete COINS[sym];delete bots[sym];delete hist[sym];
  delete vols[sym];delete sentimentMap[sym];
  delete aiDecisions[sym];delete ai2Decisions[sym];
  delete tickerHealth[sym];delete tradeCooldown[sym];
  delete trailPeaks[sym];delete botBudgets[sym];
  addRotationLog('REMOVE',sym,reason);
  saveJSON(ROSTER_FILE,tickers);
  sendDiscordAlert(`➖ **DROPPED: ${sym}**\n❌ ${reason}`);
  broadcast('TICKER_REMOVED',{sym,reason});
  return true;
}

function addRotationLog(action,sym,reason) {
  rotationLog.unshift({time:new Date().toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'}),action,sym,reason});
  if(rotationLog.length>100) rotationLog.pop();
}

function scoreHealth() {
  tickers.forEach(sym=>{
    const b=bots[sym],s=COINS[sym];
    if(!b||!s) return;
    const sg=getSignals(sym); const wr=b.trades>0?b.wins/b.trades:0.5;
    const act=b.trades>0?Math.min(1,b.trades/5):0.3;
    const sig=(sg.momentum+sg.sentiment+sg.volStrength)/300;
    const chg24=s.change24||0; const mom=chg24>10?1:chg24>0?0.6:chg24>-5?0.3:0.1;
    const ai1=aiDecisions[sym]?.verdict==='YES'?0.15:aiDecisions[sym]?.verdict==='NO'?-0.15:0;
    const ai2=ai2Decisions[sym]?.verdict==='YES'?0.15:ai2Decisions[sym]?.verdict==='NO'?-0.15:0;
    const score=Math.max(0,Math.min(100,Math.round((wr*0.25+act*0.2+sig*0.2+mom*0.15+ai1+ai2)*100)));
    if(!tickerHealth[sym]) tickerHealth[sym]={score:50,noTradeCount:0,consecutiveLosses:0};
    tickerHealth[sym].score=score;
    tickerHealth[sym].noTradeCount=b.trades===0?(tickerHealth[sym].noTradeCount||0)+1:0;
  });
}

async function rotateRoster() {
  if(!tickers.length) return;
  lastRotateTime=new Date(); scoreHealth();
  const toDrop=[];
  tickers.slice().forEach(sym=>{
    const h=tickerHealth[sym],b=bots[sym];
    if(!b||b.pos>0) return;
    const aiNo=aiDecisions[sym]?.verdict==='NO'&&ai2Decisions[sym]?.verdict==='NO'&&(h?.noTradeCount||0)>5;
    const dead=(h?.noTradeCount||0)>12&&b.trades===0;
    const poor=b.trades>=5&&(b.wins/b.trades)<0.35;
    const flagged=(h?.consecutiveLosses||0)>=3;
    if((aiNo||dead||poor||flagged)&&tickers.length-toDrop.length>SETTINGS.minBots)
      toDrop.push({sym,reason:dead?'No activity':poor?'Win rate <35%':flagged?'3 consecutive losses':'Both AIs rejecting'});
  });
  for(const d of toDrop){dropCoin(d.sym,d.reason);await sleep(400);}
  if(toDrop.length>0||tickers.length<SETTINGS.minBots){
    await reviewWatchlist();
    const needed=Math.max(toDrop.length,SETTINGS.minBots-tickers.length);
    if(needed>0&&tickers.length<SETTINGS.maxBots) await findReplacementCoins(needed);
  }
  broadcast('ROSTER_UPDATE',{tickers,tickerHealth,rotationLog,COINS,bots,hist});
}

async function findReplacementCoins(count) {
  if(!ANTHROPIC_KEY||count<=0) return;
  const hotSectors=Object.entries(learning.sectorWR).filter(([,v])=>v.total>=3)
    .sort(([,a],[,b])=>(b.wins/b.total)-(a.wins/a.total)).slice(0,2).map(([s])=>s).join(' and ');
  const scanType=fearGreedIndex<40?'momentum':btcDominance<50?'defi':'memes';
  const prompt=
    `Find ${count} replacement crypto coin(s) to trade RIGHT NOW.\n`+
    `${tickers.length?`Currently tracking: ${tickers.join(', ')}. Pick DIFFERENT ones.`:''}\n`+
    `${hotSectors?`Best performing: ${hotSectors}.`:''}\n`+
    `Fear & Greed: ${fearGreedIndex} | BTC Dom: ${btcDominance}% | Regime: ${cryptoRegime}\n`+
    `Return ONLY JSON array: [{"sym":"TICKER","name":"Coin","price":float,"mktCapB":float,"vol24B":float,`+
    `"sector":"sector","score":0-100,"catalyst":"reason","ai_verdict":"YES","confidence":0-100,`+
    `"entry":float,"stop":float,"target":float}]`;
  try {
    const resp=await axios.post('https://api.anthropic.com/v1/messages',{
      model:'claude-sonnet-4-6',max_tokens:800,
      messages:[{role:'user',content:prompt}]
    },{headers:{'Content-Type':'application/json','x-api-key':ANTHROPIC_KEY,'anthropic-version':'2023-06-01'}});
    const list=JSON.parse((resp.data?.content?.[0]?.text||'[]').replace(/```json|```/g,'').trim());
    for(const r of list){if(!tickers.includes(r.sym)&&tickers.length<SETTINGS.maxBots){addCoin(r);await sleep(300);}}
  } catch(e){console.error('Replace error:',e.message);}
}

// ── SENTIMENT ──
async function fetchCryptoSentiment() {
  // Crypto news RSS feeds
  const feeds = [
    'https://cointelegraph.com/rss',
    'https://decrypt.co/feed',
  ];
  const results = [];
  for (const url of feeds) {
    try {
      const resp = await axios.get(url, { timeout:8000 });
      const items = (resp.data.match(/<title>(.*?)<\/title>/g)||[]).slice(1,8)
        .map(t=>t.replace(/<\/?title>/g,'').trim());
      items.forEach(headline=>{
        const matchSym = tickers.find(s=>headline.toUpperCase().includes(s));
        const impact   = headline.match(/surge|spike|pump|ATH|whale|buy|massive|rally|moon|blast/i)?'HIGH':'MEDIUM';
        results.push({sym:matchSym||'MARKET',headline,impact,time:new Date().toLocaleTimeString()});
        if(matchSym&&COINS[matchSym]) {
          sentimentMap[matchSym].news=Math.min(99,sentimentMap[matchSym].news+(impact==='HIGH'?15:5));
          sentimentMap[matchSym].fearGreed=fearGreedIndex;
          sentimentMap[matchSym].overall=Math.round(
            sentimentMap[matchSym].reddit*0.25+sentimentMap[matchSym].twitter*0.35+
            sentimentMap[matchSym].news*0.25+fearGreedIndex*0.15
          );
        }
      });
    } catch(e) {}
  }
  if(results.length>0) {
    newsItems=results.concat(newsItems).slice(0,30);
    broadcast('NEWS',{items:newsItems});
    results.filter(n=>n.impact==='HIGH'&&n.sym!=='MARKET')
           .forEach(n=>sendDiscordAlert(`📰 **${n.sym} CATALYST** — ${n.headline}`));
  }
}

// ── SELF OPTIMIZATION ──
async function selfOptimize() {
  if(!ANTHROPIC_KEY||totalTrades<20) return;
  console.log('🔧 Quantum self-optimizing...');
  const bestPat=Object.entries(learning.patternWR).filter(([,v])=>v.total>=3)
    .sort(([,a],[,b])=>(b.wins/b.total)-(a.wins/a.total)).slice(0,3)
    .map(([p,v])=>`${p}: ${Math.round(v.wins/v.total*100)}%`).join(', ')||'Building';
  const prompt=
    `Crypto trading optimizer. Review data and suggest parameter adjustments:\n`+
    `Trades: ${totalTrades} | WR: ${Math.round(totalWins/totalTrades*100)}% | P&L: $${totalPnl.toFixed(2)}\n`+
    `Best Patterns: ${bestPat} | Avg Fear&Greed: ${fearGreedIndex}\n`+
    `Current: Stop ${SETTINGS.stopLoss}% | Target ${SETTINGS.takeProfit}% | MinConf ${SETTINGS.minConfidence}%\n`+
    `Respond ONLY with JSON: {"stopLoss":float,"takeProfit":float,"minConfidence":int,"insight":"one sentence"}`;
  try {
    const resp=await axios.post('https://api.anthropic.com/v1/messages',{
      model:'claude-sonnet-4-6',max_tokens:300,
      messages:[{role:'user',content:prompt}]
    },{headers:{'Content-Type':'application/json','x-api-key':ANTHROPIC_KEY,'anthropic-version':'2023-06-01'}});
    const txt=resp.data?.content?.[0]?.text||'{}';
    const opts=JSON.parse(txt.replace(/```json|```/g,'').trim());
    if(opts.stopLoss&&opts.stopLoss>=3&&opts.stopLoss<=10)   SETTINGS.stopLoss=opts.stopLoss;
    if(opts.takeProfit&&opts.takeProfit>=5&&opts.takeProfit<=20) SETTINGS.takeProfit=opts.takeProfit;
    if(opts.minConfidence&&opts.minConfidence>=60&&opts.minConfidence<=85) SETTINGS.minConfidence=opts.minConfidence;
    learning.lastOptimized=new Date().toISOString();
    saveJSON(LEARNING_FILE,learning);
    console.log(`🔧 Self-optimized: ${opts.insight}`);
    sendDiscordAlert(`🔧 **QUANTUM SELF-OPTIMIZED**\n📊 ${totalTrades} trades analyzed\n💡 ${opts.insight}\n⚙️ Stop ${SETTINGS.stopLoss}% | Target ${SETTINGS.takeProfit}% | MinConf ${SETTINGS.minConfidence}%`);
  } catch(e){console.error('Self-optimize:',e.message);}
}

// ── COINBASE ──
async function testCoinbase() {
  if(!CB_KEY||!CB_SECRET) { console.log('⚠️ No Coinbase credentials — simulation mode'); return; }
  try {
    const timestamp = Math.floor(Date.now()/1000).toString();
    const method='GET', path='/api/v3/brokerage/accounts', body='';
    const sig = crypto.createHmac('sha256',CB_SECRET).update(timestamp+method+path+body).digest('hex');
    const resp = await axios.get(`https://api.coinbase.com${path}`,{
      headers:{'CB-ACCESS-KEY':CB_KEY,'CB-ACCESS-SIGN':sig,'CB-ACCESS-TIMESTAMP':timestamp}
    });
    const accounts=resp.data?.accounts||[];
    const usd=accounts.find(a=>a.currency==='USD');
    const bal=usd?parseFloat(usd.available_balance?.value||0).toFixed(2):'Unknown';
    coinbaseConnected=true;
    console.log(`✅ Coinbase connected — USD Balance: $${bal}`);
    sendDiscordAlert(`✅ **Coinbase Connected**\n💵 USD Balance: $${bal}\n🔒 Mode: ${CB_KEY?'🔴 LIVE':'🟡 SIM'}`);
    broadcast('COINBASE_STATUS',{connected:true,balance:bal});
  } catch(e) {
    console.log('⚠️ Coinbase connection failed:',e.message);
    coinbaseConnected=false;
    broadcast('COINBASE_STATUS',{connected:false,error:e.message});
  }
}

async function placeCoinbaseOrder(sym,side,amount) {
  if(!coinbaseConnected||!CB_KEY) return;
  try {
    const timestamp=Math.floor(Date.now()/1000).toString();
    const productId=`${sym}-USD`;
    const body=JSON.stringify({client_order_id:crypto.randomUUID(),product_id:productId,
      side,order_configuration:{market_market_ioc:side==='BUY'
        ?{quote_size:amount.toFixed(2)}
        :{base_size:amount.toFixed(8)}
      }});
    const path='/api/v3/brokerage/orders';
    const sig=crypto.createHmac('sha256',CB_SECRET).update(timestamp+'POST'+path+body).digest('hex');
    const resp=await axios.post(`https://api.coinbase.com${path}`,body,{
      headers:{'CB-ACCESS-KEY':CB_KEY,'CB-ACCESS-SIGN':sig,'CB-ACCESS-TIMESTAMP':timestamp,'Content-Type':'application/json'}
    });
    console.log(`📋 Coinbase ${side} ${sym}: ${resp.data?.success_response?.order_id||'OK'}`);
  } catch(e){console.error('Coinbase order:',e.message);}
}

// ── DISCORD ──
async function sendDiscordAlert(message) {
  if(!DISCORD_WEBHOOK) return;
  try {
    await axios.post(DISCORD_WEBHOOK,{
      username:'⚡ APEX QUANTUM V3',
      embeds:[{description:message,color:0xa855f7,timestamp:new Date().toISOString(),
        footer:{text:`APEX QUANTUM V3 · F&G:${fearGreedIndex} · ${tickers.length} bots · ${cryptoRegime}`}}]
    });
  } catch(e){}
}

async function sendDiscordTrade(trade) {
  const win=trade.pnl>0; const wr=totalTrades>0?Math.round(totalWins/totalTrades*100):0;
  await sendDiscordAlert(
    `${win?'✅':'❌'} **${trade.sym} ${trade.reason}**\n`+
    `💰 P&L: ${win?'+':''}$${trade.pnl.toFixed(2)} · AI1:${trade.aiConf}% · AI2:${trade.ai2Conf}%\n`+
    `📊 Pattern: ${trade.pattern} · F&G: ${trade.fearGreed}\n`+
    `🌍 Regime: ${trade.regime} · Budget: $${getBotBudget(trade.sym)}\n`+
    `📈 Today: ${dailyPnl>=0?'+':''}$${dailyPnl.toFixed(2)} · Week: $${weeklyPnl.toFixed(2)} · ${wr}% WR`
  );
}

async function sendDailyReport() {
  const wr=totalTrades>0?Math.round(totalWins/totalTrades*100):0;
  await sendDiscordAlert(
    `📊 **QUANTUM DAILY REPORT — ${new Date().toLocaleDateString()}**\n\n`+
    `💰 Today: ${dailyPnl>=0?'+':''}$${dailyPnl.toFixed(2)}\n`+
    `📅 Week: ${weeklyPnl>=0?'+':''}$${weeklyPnl.toFixed(2)}\n`+
    `📈 All-Time: ${totalPnl>=0?'+':''}$${totalPnl.toFixed(2)}\n`+
    `🎯 Win Rate: ${wr}% (${totalWins}W/${totalTrades-totalWins}L)\n`+
    `😱 Fear & Greed: ${fearGreedIndex} | BTC Dom: ${btcDominance}%\n`+
    `🤖 Active Bots: ${tickers.length} · Regime: ${cryptoRegime}`
  );
  dailyTrades=0;dailyLoss=0;dailyPnl=0;saveState();
}

// ── HELPERS ──
function sleep(ms){return new Promise(r=>setTimeout(r,ms));}
function formatPrice(p){
  if(!p) return '0';
  if(p>=1000) return p.toFixed(2);
  if(p>=1)    return p.toFixed(4);
  if(p>=0.01) return p.toFixed(6);
  return p.toFixed(8);
}

// ── SCHEDULES ──
setInterval(fetchCoinGeckoPrices, 30000);                   // Real prices every 30s
setInterval(analyzeAll, 600000);                            // Smart dual AI every 10 min
setInterval(rotateRoster, 300000);                          // Rotate every 5 min
setInterval(fetchMarketConditions, 300000);                 // Market conditions every 5 min
setInterval(()=>scanCrypto('full'), 600000);                // Full scan every 10 min
setInterval(fetchCryptoSentiment, 300000);                  // News every 5 min
setInterval(()=>{checkDrawdown();calcPortfolioHeat();},60000);

// Daily report midnight UTC
cron.schedule('0 0 * * *', sendDailyReport);

// Weekly self-optimization Sunday
cron.schedule('0 20 * * 0', async()=>{
  await selfOptimize(); weeklyPnl=0; saveState();
});

// Sunday scan for fresh opportunities
cron.schedule('0 8 * * 0', async()=>{
  console.log('🌅 Weekend whale scan...');
  await scanCrypto('whale');
  await sleep(2000);
  await scanCrypto('momentum');
});

// ── REST API ──
app.get('/api/status', (req,res)=>res.json({
  status:'running',tickers:tickers.length,totalPnl,totalTrades,totalWins,
  dailyPnl,weeklyPnl,coinbaseConnected,cryptoRegime,fearGreedIndex,btcDominance,
  portfolioHeat,paused,pauseReason,uptime:process.uptime()
}));
app.get('/api/trades',   (req,res)=>res.json({trades:tradeJournal.slice(0,200),totalPnl,totalTrades,totalWins}));
app.get('/api/patterns', (req,res)=>res.json(patternData));
app.get('/api/learning', (req,res)=>res.json(learning));
app.post('/api/settings',(req,res)=>{Object.assign(SETTINGS,req.body);broadcast('SETTINGS',SETTINGS);res.json({ok:true,settings:SETTINGS});});
app.post('/api/pause',   (req,res)=>{paused=true;pauseReason='Manually paused';broadcast('PAUSED',{paused,pauseReason});res.json({ok:true});});
app.post('/api/resume',  (req,res)=>{paused=false;pauseReason='';broadcast('RESUMED',{paused});res.json({ok:true});});
app.post('/api/analyze-now', async(req,res)=>{res.json({ok:true});await analyzeAll();});
app.post('/api/rotate-now',  async(req,res)=>{res.json({ok:true});await rotateRoster();});
app.post('/api/scan-now',    async(req,res)=>{const t=req.body.type||'full';res.json({ok:true});await scanCrypto(t);broadcast('ROSTER_UPDATE',{tickers,tickerHealth,rotationLog,COINS,bots,hist});});

// ── START ──
server.listen(PORT, async()=>{
  console.log('');
  console.log('╔══════════════════════════════════════╗');
  console.log('║     APEX QUANTUM V3.0                ║');
  console.log('║     Autonomous Crypto Engine          ║');
  console.log(`║     Port: ${PORT}                        ║`);
  console.log('╚══════════════════════════════════════╝');
  console.log('');
  console.log(`🧠 Claude AI:  ${ANTHROPIC_KEY?'✅':'❌ No API key'}`);
  console.log(`💎 Coinbase:   ${CB_KEY?'⏳ Testing...':'⚠️ Simulation mode'}`);
  console.log(`💬 Discord:    ${DISCORD_WEBHOOK?'✅':'❌ No webhook'}`);
  console.log(`🧠 Dual AI:    ✅ Enabled`);
  console.log(`📈 Auto Scale: ✅ $${SETTINGS.budget} → $${SETTINGS.budgetCeiling}`);
  console.log('');

  await testCoinbase();
  await fetchMarketConditions();
  await fetchCryptoSentiment();
  await sleep(1500);

  console.log('🔍 Quantum scanning crypto markets...');
  await scanCrypto('full');
  await sleep(1500);
  await scanCrypto('memes');
  await sleep(1500);
  await scanCrypto('momentum');
  await sleep(1000);

  // Safety net
  if(tickers.length===0){
    console.log('⚠️ Scan empty — seeding starters...');
    const starters=[
      {sym:'BTC', price:95000, mktCapB:1850, vol24B:28,  sector:'Layer1', catalyst:'Bitcoin market leader', ai_verdict:'WATCH', confidence:70},
      {sym:'ETH', price:3200,  mktCapB:380,  vol24B:12,  sector:'Layer1', catalyst:'Ethereum ecosystem',    ai_verdict:'WATCH', confidence:70},
      {sym:'SOL', price:185,   mktCapB:85,   vol24B:5,   sector:'Layer1', catalyst:'Solana high throughput',ai_verdict:'WATCH', confidence:70},
      {sym:'WIF', price:2.85,  mktCapB:2.8,  vol24B:0.8, sector:'Meme',   catalyst:'Dog meme momentum',    ai_verdict:'WATCH', confidence:65},
      {sym:'PEPE',price:0.000018,mktCapB:7.5,vol24B:1.2, sector:'Meme',   catalyst:'Pepe memecoin play',   ai_verdict:'WATCH', confidence:65},
      {sym:'AAVE',price:285,   mktCapB:4.3,  vol24B:0.3, sector:'DeFi',   catalyst:'DeFi lending leader',  ai_verdict:'WATCH', confidence:65},
    ];
    for(const s of starters) addCoin(s);
  }

  // Fetch initial real prices
  await fetchCoinGeckoPrices();
  await sleep(2000);
  await analyzeAll();

  sendDiscordAlert(
    `🚀 **APEX QUANTUM V3.0 ONLINE**\n`+
    `⚡ ${tickers.length} bots: ${tickers.join(', ')||'Scanning...'}\n`+
    `🧠 Dual AI: ✅ | Coinbase: ${coinbaseConnected?'✅ LIVE':'⚠️ SIM MODE'}\n`+
    `😱 Fear & Greed: ${fearGreedIndex} | BTC Dom: ${btcDominance}%\n`+
    `🌍 Regime: ${cryptoRegime}\n`+
    `📈 Auto Scale: $${SETTINGS.budget}→$${SETTINGS.budgetCeiling} | Trail Stop: ✅\n`+
    `⏰ Prices: 30s · Analysis: 5min · Rotate: 5min`
  );
  console.log('✅ APEX QUANTUM V3.0 — All systems online');
});

process.on('uncaughtException',  e=>console.error('Uncaught:',e.message));
process.on('unhandledRejection', e=>console.error('Unhandled:',e?.message||e));
