// Pump.fun Replay Sprint — paper-trading bot for the replay harness.
//
// What it does: late-stage completion chase. The dev window shows that
// nearly every pump.fun coin bleeds after its opening run, so early
// momentum entries lose money on most names. Coins that live long
// enough to accumulate 50 SOL of real reserves are different — real
// buying sits behind them, and a large share keep running toward
// completion (85 SOL real). The bot therefore buys ONLY a coin whose
// real reserve has reached 50 SOL, stakes a flat 0.20 SOL, and exits
// fast: +50% take-profit, -15% stop-loss, or a 900-slot time stop
// (roughly six minutes). Banking at +50% instead of waiting for a
// double is the whole point: the +100% variant's profit came mostly
// from its three best coins and collapsed on rebuilt windows, while the
// +50% variant stays positive even with its best coins taken out. Small
// wins, often, one coin at a time, never more than five open positions,
// and never a second entry into a coin already traded.
//
// Determinism: every decision is a pure function of the replay stream —
// the slot numbers, the order of events inside each batch, and the
// reserves. No clock, no randomness, no network. The harness runs the
// same window twice and the two action logs must match byte for byte,
// so the only inputs are the hello message (capital, caps, fees) and
// the batches.
//
// Protocol: JSON lines on stdin/stdout. Hello first, then one batch
// per slot, then done. One reply line per batch carries that slot's
// orders; an order fills two slots later. A buy spends quote_lamports
// of SOL (curve fees included); a sell moves token_amount of tokens.
// Client ids are a simple counter, unique across the run, so two
// executions can never disagree about them.

import * as readline from 'node:readline';

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

interface Order {
  side: 'buy' | 'sell';
  client_id: string;
  mint: Mint;
  quote_lamports?: string;
  token_amount?: string;
  max_slippage_bps: number;
}

// Strategy parameters, chosen on the dev window by offline simulation.
const PARAMS = {
  entryRealSol: 50, // enter once a curve holds this much real SOL
  fallbackRealSol: 40, // late-window fallback so the 20-coin bar is met
  stakeSol: 0.2, // paper SOL per entry
  fallbackStakeSol: 0.05,
  minBuySol: 0.01, // guardrail: a round trip must be at least this
  takeProfitMult: 1.5, // sell when marked value reaches 1.5x all-in cost
  stopLossMult: 0.85, // sell when marked value falls to 0.85x all-in cost
  maxHoldSlots: 900, // time stop, in slots since the buy filled
  maxSlippageBps: 10_000, // wide open: never refuse a fill on slippage
  maxOpenPositions: 5,
  maxOrdersPerBatch: 16,
  windowSlots: 403_213, // dev window length, for the late fallback
  fallbackAfter: 0.7, // fallback switches on past this share of the window
  tripBar: 20, // fallback only while fewer than this many trips are done
} as const;

const solToLamports = (sol: number): bigint => BigInt(Math.round(sol * 1_000_000_000));
const STAKE_LAMPORTS = solToLamports(PARAMS.stakeSol);
const FALLBACK_STAKE_LAMPORTS = solToLamports(PARAMS.fallbackStakeSol);
const MIN_BUY_LAMPORTS = solToLamports(PARAMS.minBuySol);

// --- live state, rebuilt from the harness messages as they arrive ---
const curves = new Map<Mint, Curve>();
const held = new Map<Mint, Held>(); // positions, from the latest account
const openedAt = new Map<Mint, number>(); // slot each buy filled at
const pendingBuy = new Map<Mint, bigint>(); // mint -> SOL committed by the buy
const pendingSell = new Set<Mint>(); // mints with a sell not yet filled
const decided = new Set<Mint>(); // mints already entered once (never re-enter)
const roundTrips = new Set<Mint>(); // mints with a completed round trip
let cash = 0n;
let txFee = 0n;
let maxOrderBps = 100;
let firstSlot = -1;
let orderCounter = 1;

function emptyCurve(): Curve {
  return {
    virtualToken: 0n,
    virtualQuote: 0n,
    realQuote: 0n,
    complete: false,
    createdSlot: null,
  };
}

function markedValue(h: Held, c: Curve): bigint {
  // Marked value of the holding in lamports, before exit fees.
  if (c.virtualToken === 0n) return 0n;
  return (h.tokens * c.virtualQuote) / c.virtualToken;
}

function openCount(): number {
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

function nextClientId(): string {
  return `o${orderCounter++}`;
}

function handleBatch(batch: any): Order[] {
  const slot: number = batch.slot;
  if (firstSlot < 0) firstSlot = slot;
  const orders: Order[] = [];

  // 1. Fills first: a filled buy starts the position clock at the slot
  //    it filled; a filled sell closes a round trip. Rejected or failed
  //    orders just leave the pending sets.
  for (const f of batch.fills ?? []) {
    if (f.side === 'buy') {
      pendingBuy.delete(f.mint);
      if (f.status === 'filled') openedAt.set(f.mint, f.slot);
    } else if (f.side === 'sell') {
      pendingSell.delete(f.mint);
      if (f.status === 'filled') roundTrips.add(f.mint);
    }
  }

  // 2. The account: cash and open positions as the harness sees them.
  //    The opened slot survives across batches via openedAt, because the
  //    account itself carries no timing. Drop clocks for positions that
  //    are gone (sold, completed, or flattened at the end).
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

  // 3. Marks (latest reserves for held / pending mints), then the
  //    batch's events in chain order. After this the curves hold the
  //    end-of-slot reserves the decision is made on.
  for (const m of batch.marks ?? []) {
    const c = curves.get(m.mint) ?? emptyCurve();
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
      const c = curves.get(e.mint) ?? emptyCurve();
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
    const mult = Number(markedValue(h, c)) / Number(h.cost);
    const tooOld = slot - h.openedSlot > PARAMS.maxHoldSlots;
    if (mult >= PARAMS.takeProfitMult || mult <= PARAMS.stopLossMult || tooOld) {
      if (orders.length >= PARAMS.maxOrdersPerBatch) break;
      orders.push({
        side: 'sell',
        client_id: nextClientId(),
        mint,
        token_amount: h.tokens.toString(),
        max_slippage_bps: PARAMS.maxSlippageBps,
      });
      pendingSell.add(mint);
    }
  }

  // 5. Entries: a coin becomes a candidate on the batch where its real
  //    SOL reserve reaches the entry threshold. One buy per coin, ever;
  //    the buy is capped at 1% of the real reserve (from hello.caps) and
  //    at the stake, and it must clear the 0.01 SOL round-trip minimum.
  //    The fallback only switches on late in the window if the 20-coin
  //    bar is still short, so the main rule is never diluted early.
  const fallbackActive =
    firstSlot >= 0 &&
    slot - firstSlot > Math.floor(PARAMS.windowSlots * PARAMS.fallbackAfter) &&
    roundTrips.size < PARAMS.tripBar;
  const entryReal = fallbackActive ? PARAMS.fallbackRealSol : PARAMS.entryRealSol;
  const stake = fallbackActive ? FALLBACK_STAKE_LAMPORTS : STAKE_LAMPORTS;

  for (const e of batch.events ?? []) {
    if (orders.length >= PARAMS.maxOrdersPerBatch) break;
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
    if (openCount() >= PARAMS.maxOpenPositions) continue;
    if (freeCash() < amount + txFee) continue;
    orders.push({
      side: 'buy',
      client_id: nextClientId(),
      mint,
      quote_lamports: amount.toString(),
      max_slippage_bps: PARAMS.maxSlippageBps,
    });
    pendingBuy.set(mint, amount);
    decided.add(mint);
  }

  return orders;
}

async function run(): Promise<void> {
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
      const orders = handleBatch(msg);
      process.stdout.write(JSON.stringify({ type: 'reply', seq: msg.seq, orders }) + '\n');
    } else if (msg.type === 'done') {
      break;
    }
  }
}

await run();
