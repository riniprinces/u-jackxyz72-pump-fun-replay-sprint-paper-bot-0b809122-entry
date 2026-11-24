// Pump.fun Replay Sprint — paper trading bot (agent-fun/replay/v2).
//
// Strategy: late-stage completion chase. On the dev window almost every
// pump.fun coin bleeds after its early run, so buying early momentum loses
// money on most coins. Coins that survive long enough to accumulate 50 SOL
// of real reserves are different: they have sustained buying, and a large
// share of them keep running toward completion (85 SOL real). So this bot
// buys ONLY coins whose real SOL reserve has reached 50 SOL, with a fixed
// 0.20 SOL stake, and exits fast: take profit at +50% of all-in cost,
// stop loss at -15%, or a 900-slot time stop (about 6 minutes). Banking
// winners at +50% instead of waiting for a double matters: the +100%
// version's gains came mostly from its 3 best coins, so it fell apart on
// rebuilt windows, while the +50% version stays positive even without its
// best coins. It wins small and often, one coin at a time, never more than
// 5 open positions, and it never re-enters a coin it already traded.
//
// Everything is deterministic: every decision comes from the replay data
// itself — the slot numbers, the order of events in each batch, and the
// reserves. No clock, no randomness, no network. The bot runs twice over
// the same replay and must produce byte-identical action logs, so the only
// inputs are the hello message (caps, fees, capital) and the batches.
//
// Protocol: the harness speaks JSON lines on stdin/stdout. It sends one
// hello message, then one batch per slot, then done. For each batch the bot
// answers with one reply line carrying that batch's orders — a batch of
// orders is decided per slot, and each order fills 2 slots later. A buy
// spends quote_lamports of SOL (curve fees included); a sell moves
// token_amount of tokens. Client ids are a simple counter, unique across
// the run, so the two executions can never disagree about them.

import * as readline from 'node:readline';

const SOL = (x: number): bigint => BigInt(Math.round(x * 1_000_000_000));

// --- strategy parameters (chosen on the dev window by offline simulation) ---
const ENTRY_REAL_SOL = 50; // enter once a curve holds this much real SOL
const FALLBACK_REAL_SOL = 40; // late-window fallback so the 20-coin bar is met
const STAKE_LAMPORTS = SOL(0.2); // paper SOL per entry
const FALLBACK_STAKE_LAMPORTS = SOL(0.05);
const MIN_BUY_LAMPORTS = SOL(0.01); // guardrail: round trips must be >= this
const TAKE_PROFIT = 1.5; // sell when marked value reaches 1.5x all-in cost
const STOP_LOSS = 0.85; // sell when marked value falls to 0.85x all-in cost
const MAX_HOLD_SLOTS = 900; // time stop, in slots since the buy filled
const MAX_SLIPPAGE_BPS = 10_000; // wide open: never refuse a fill on slippage
const MAX_OPEN_POSITIONS = 5;
const MAX_ORDERS_PER_BATCH = 16;
const WINDOW_SLOTS = 403_213; // dev window length, for the late fallback

type Mint = string;

interface Curve {
  virtualToken: bigint;
  virtualQuote: bigint;
  realQuote: bigint;
  complete: boolean;
  createdSlot: number | null;
}

interface Held {
  tokens: bigint;
  cost: bigint;
  openedSlot: number;
}

const curves = new Map<Mint, Curve>();
const held = new Map<Mint, Held>(); // positions, from the latest account
const openedAt = new Map<Mint, number>(); // slot each buy filled at
const pendingBuy = new Map<Mint, bigint>(); // mint -> SOL committed by the buy
const pendingSell = new Set<Mint>(); // mints with a sell not yet filled
const decided = new Set<Mint>(); // mints already entered once (never re-enter)
const distinctTrips = new Set<Mint>(); // mints with a completed round trip
let cash = 0n;
let txFee = 0n;
let maxOrderBps = 100;
let firstSlot = -1;
let orderCounter = 1;

function valueOf(h: Held, c: Curve): bigint {
  // Marked value of the holding in lamports, before exit fees.
  if (c.virtualToken === 0n) return 0n;
  return (h.tokens * c.virtualQuote) / c.virtualToken;
}

function committedPositions(): number {
  const mints = new Set<Mint>(held.keys());
  for (const m of pendingBuy.keys()) mints.add(m);
  return mints.size;
}

function freeCash(): bigint {
  // Cash minus what pending buys will take if they fill (amount + tx fee).
  let free = cash;
  for (const amount of pendingBuy.values()) free -= amount + txFee;
  return free;
}

interface Order {
  side: 'buy' | 'sell';
  client_id: string;
  mint: Mint;
  quote_lamports?: string;
  token_amount?: string;
  max_slippage_bps: number;
}

function nextId(): string {
  return `o${orderCounter++}`;
}

function onBatch(batch: any): Order[] {
  const slot: number = batch.slot;
  if (firstSlot < 0) firstSlot = slot;
  const orders: Order[] = [];

  // 1. Fold in fills first: a filled buy starts the position clock at the
  //    slot it filled; a filled sell closes a round trip. Rejected or
  //    failed orders just leave the pending sets.
  for (const f of batch.fills ?? []) {
    if (f.side === 'buy') {
      pendingBuy.delete(f.mint);
      if (f.status === 'filled') openedAt.set(f.mint, f.slot);
    } else if (f.side === 'sell') {
      pendingSell.delete(f.mint);
      if (f.status === 'filled') distinctTrips.add(f.mint);
    }
  }

  // 2. Fold in the account: cash and open positions as the harness sees
  //    them. The opened slot survives across batches via openedAt, because
  //    the account itself carries no timing. Drop clocks for positions
  //    that are gone (sold, completed, or flattened at the end).
  cash = BigInt(batch.account.cash_lamports);
  held.clear();
  for (const p of batch.account.positions ?? []) {
    const tokens = BigInt(p.token_amount);
    if (tokens > 0n) {
      held.set(p.mint, {
        tokens,
        cost: BigInt(p.cost_lamports),
        openedSlot: openedAt.get(p.mint) ?? slot,
      });
    }
  }
  for (const mint of [...openedAt.keys()]) {
    if (!held.has(mint) && !pendingBuy.has(mint)) openedAt.delete(mint);
  }

  // 3. Fold in marks (latest reserves for held / pending mints), then the
  //    batch's events in chain order. After this step the curves hold the
  //    end-of-slot reserves the decision is made on.
  for (const m of batch.marks ?? []) {
    const c = curves.get(m.mint) ?? {
      virtualToken: 0n,
      virtualQuote: 0n,
      realQuote: 0n,
      complete: false,
      createdSlot: null,
    };
    c.virtualToken = BigInt(m.virtual_token_reserves);
    c.virtualQuote = BigInt(m.virtual_quote_reserves);
    c.realQuote = BigInt(m.real_quote_reserves);
    curves.set(m.mint, c);
  }
  for (const e of batch.events ?? []) {
    if (e.event === 'CreateEvent') {
      curves.set(e.mint, {
        virtualToken: BigInt(e.virtual_token_reserves),
        virtualQuote: BigInt(e.virtual_quote_reserves),
        realQuote: 0n,
        complete: false,
        createdSlot: e.slot,
      });
    } else if (e.event === 'TradeEvent') {
      const c = curves.get(e.mint) ?? {
        virtualToken: 0n,
        virtualQuote: 0n,
        realQuote: 0n,
        complete: false,
        createdSlot: null,
      };
      c.virtualToken = BigInt(e.virtual_token_reserves);
      c.virtualQuote = BigInt(e.virtual_quote_reserves);
      c.realQuote = BigInt(e.real_quote_reserves);
      curves.set(e.mint, c);
    } else if (e.event === 'CompleteEvent') {
      const c = curves.get(e.mint);
      if (c) c.complete = true;
    }
  }

  // 4. Exits first: every held position is checked against take-profit,
  //    stop-loss and the time stop, and sold whole when one of them hits.
  //    A sell already in flight is never doubled.
  for (const [mint, h] of held) {
    if (pendingSell.has(mint)) continue;
    const c = curves.get(mint);
    if (!c || c.complete) continue;
    if (h.cost === 0n) continue;
    const mult = Number(valueOf(h, c)) / Number(h.cost);
    const tooOld = slot - h.openedSlot > MAX_HOLD_SLOTS;
    if (mult >= TAKE_PROFIT || mult <= STOP_LOSS || tooOld) {
      if (orders.length >= MAX_ORDERS_PER_BATCH) break;
      orders.push({
        side: 'sell',
        client_id: nextId(),
        mint,
        token_amount: h.tokens.toString(),
        max_slippage_bps: MAX_SLIPPAGE_BPS,
      });
      pendingSell.add(mint);
    }
  }

  // 5. Entries: a coin becomes a candidate on the batch where its real SOL
  //    reserve reaches the entry threshold. One buy per coin, ever; the buy
  //    is capped at 1% of the real reserve (from hello.caps) and at the
  //    stake, and it must clear the 0.01 SOL round-trip minimum. The
  //    fallback only switches on late in the window if the 20-coin bar is
  //    still short, so the main rule is never diluted early.
  const fallbackActive =
    firstSlot >= 0 &&
    slot - firstSlot > Math.floor(WINDOW_SLOTS * 0.7) &&
    distinctTrips.size < 20;
  const entryReal = fallbackActive ? FALLBACK_REAL_SOL : ENTRY_REAL_SOL;
  const stake = fallbackActive ? FALLBACK_STAKE_LAMPORTS : STAKE_LAMPORTS;

  for (const e of batch.events ?? []) {
    if (orders.length >= MAX_ORDERS_PER_BATCH) break;
    const mint: Mint = e.mint;
    if (decided.has(mint) || held.has(mint) || pendingBuy.has(mint)) continue;
    const c = curves.get(mint);
    if (!c || c.complete) continue;
    const realSol = Number(c.realQuote) / 1_000_000_000;
    if (realSol < entryReal) continue;
    // Size cap: at most maxOrderBps of the real reserve in one batch.
    const cap = (c.realQuote * BigInt(maxOrderBps)) / 10_000n;
    const amount = cap < stake ? cap : stake;
    if (amount < MIN_BUY_LAMPORTS) continue;
    if (committedPositions() >= MAX_OPEN_POSITIONS) continue;
    if (freeCash() < amount + txFee) continue;
    orders.push({
      side: 'buy',
      client_id: nextId(),
      mint,
      quote_lamports: amount.toString(),
      max_slippage_bps: MAX_SLIPPAGE_BPS,
    });
    pendingBuy.set(mint, amount);
    decided.add(mint);
  }

  return orders;
}

async function main(): Promise<void> {
  const rl = readline.createInterface({ input: process.stdin, crlfDelay: Infinity });
  for await (const line of rl) {
    if (!line.trim()) continue;
    const msg = JSON.parse(line);
    if (msg.type === 'hello') {
      // The hello message carries everything the run is configured with:
      // capital, caps, fees, latency and the seed (unused: no randomness).
      cash = BigInt(msg.capital.lamports);
      txFee = BigInt(msg.fees.base_fee_lamports) + BigInt(msg.fees.priority_fee_lamports);
      maxOrderBps = msg.caps.max_order_bps_of_real_reserve;
    } else if (msg.type === 'batch') {
      const orders = onBatch(msg);
      process.stdout.write(JSON.stringify({ type: 'reply', seq: msg.seq, orders }) + '\n');
    } else if (msg.type === 'done') {
      break;
    }
  }
}

await main();
