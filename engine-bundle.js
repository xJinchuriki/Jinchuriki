(function (g) {

// ===== game.js =====
// Pure state model for the Metin2 Okey card minigame.
// 24 unique cards: values 1..8 across three colors (R/B/Y). The game shows 5
// cards on the field; you can either discard cards (any subset, even just one)
// to draw replacements, or pick 3 to score. There's no fixed round structure —
// you keep playing until you decide to finish.
//
// No DOM, no I/O. Exports state/transition functions consumed by ui + solver.

const COLORS = ["R", "B", "Y"];
const COLOR_NAMES = { R: "Red", B: "Blue", Y: "Yellow" };
const VALUES = [1, 2, 3, 4, 5, 6, 7, 8];
const BOARD_SIZE = 5;
const HAND_SIZE = 3;

const CHEST_THRESHOLDS = { gold: 400, silver: 300, bronze: 0 };

function cardId(color, value) { return `${color}${value}`; }
function parseCardId(id) {
  return { color: id[0], value: Number(id.slice(1)) };
}

// ----- scoring -----
//
// Three-of-a-kind (all same value, any colors): 20 + (value-1) * 10
//   1→20, 2→30, …, 8→90
// Same-color sequence (3 consecutive, all same color):
//   low=1 → 50, low=2 → 60, …, low=6 → 100  (formula: 50 + (low-1)*10)
// Mixed-color sequence (3 consecutive, NOT all same color):
//   low=1 → 10, low=2 → 20, …, low=6 → 60   (formula: low * 10)
// No combination → 0.

function scoreThreeOfAKind(value) {
  return 20 + (value - 1) * 10;
}
function scoreSameColorSeq(low) {
  return 50 + (low - 1) * 10;
}
function scoreMixedSeq(low) {
  return low * 10;
}

// Score a 3-card hand. Returns { score, type, label } where type ∈
// {"three", "sameSeq", "mixedSeq", "none"} and label is human-readable.
// The score of three cards is a pure function of those three cards, and there
// are only 24 cards — so it is a lookup, not a computation. The old version
// allocated three objects (parseCardId), three arrays (map/map/sort) and a
// template-literal label on EVERY call, and a 2026-09-15 CPU profile put it at
// 20% of all search time: it runs in the innermost loop of every playout.
//
// The table is built once over every a <= b <= c triple (duplicates included,
// so degenerate input behaves exactly as it did before) and holds SHARED frozen
// result objects. A lookup therefore allocates nothing at all.
//
// Exhaustively verified identical to the old implementation over all 24^3
// ordered triples by bench/scorehand-equiv.mjs.

const CARD_INDEX = new Map();
for (let ci = 0; ci < COLORS.length; ci++) {
  for (let vi = 0; vi < VALUES.length; vi++) {
    CARD_INDEX.set(cardId(COLORS[ci], VALUES[vi]), ci * 8 + vi);
  }
}

const INVALID_HAND = Object.freeze({ score: 0, type: "none", label: "—" });
const NO_COMBO = Object.freeze({ score: 0, type: "none", label: "No combo" });

// Indexed by a * 576 + b * 24 + c with a <= b <= c (indices, not values).
const COMBO_TABLE = new Array(24 * 24 * 24).fill(NO_COMBO);
for (let a = 0; a < 24; a++) {
  for (let b = a; b < 24; b++) {
    for (let c = b; c < 24; c++) {
      const va = (a & 7) + 1, vb = (b & 7) + 1, vc = (c & 7) + 1;
      const values = [va, vb, vc].sort((x, y) => x - y);
      let entry = NO_COMBO;
      if (values[0] === values[1] && values[1] === values[2]) {
        const v = values[0];
        entry = Object.freeze({ score: scoreThreeOfAKind(v), type: "three", label: `Three ${v}s` });
      } else if (values[1] === values[0] + 1 && values[2] === values[1] + 1) {
        const low = values[0];
        const sameColour = (a >> 3) === (b >> 3) && (b >> 3) === (c >> 3);
        entry = sameColour
          ? Object.freeze({ score: scoreSameColorSeq(low), type: "sameSeq", label: `${low}-${low + 1}-${low + 2} same color` })
          : Object.freeze({ score: scoreMixedSeq(low), type: "mixedSeq", label: `${low}-${low + 1}-${low + 2} mixed` });
      }
      COMBO_TABLE[a * 576 + b * 24 + c] = entry;
    }
  }
}

function scoreHand(cards) {
  if (!cards || cards.length !== 3) return INVALID_HAND;
  let a = CARD_INDEX.get(cards[0]);
  let b = CARD_INDEX.get(cards[1]);
  let c = CARD_INDEX.get(cards[2]);
  // An id the table does not know (malformed input) must not silently score 0
  // against a wrong slot, so it takes the same "no combo" answer as before.
  if (a === undefined || b === undefined || c === undefined) return NO_COMBO;
  // Sort three integers without allocating an array.
  let t;
  if (a > b) { t = a; a = b; b = t; }
  if (b > c) { t = b; b = c; c = t; }
  if (a > b) { t = a; a = b; b = t; }
  return COMBO_TABLE[a * 576 + b * 24 + c];
}

function chestForScore(score) {
  if (score >= CHEST_THRESHOLDS.gold) return "gold";
  if (score >= CHEST_THRESHOLDS.silver) return "silver";
  return "bronze";
}

// ----- state -----
//
// board:    array of 5 slots, each cardId or null
// score:    running score for the current game
// consumed: Set of cardIds permanently out of the deck this game (discarded
//           or scored) — these stay greyed in the palette
// history:  stack of past actions (for undo)
// log:      confirmed picks for the current game (in order)

function createState() {
  return {
    board: Array(BOARD_SIZE).fill(null),
    score: 0,
    consumed: new Set(),
    history: [],
    log: [],
  };
}

function setSlot(state, slotIndex, cardId) {
  if (slotIndex < 0 || slotIndex >= BOARD_SIZE) return state;
  state.history.push({ kind: "setSlot", slotIndex, prev: state.board[slotIndex] });
  state.board[slotIndex] = cardId;
  return state;
}

function clearSlot(state, slotIndex) {
  return setSlot(state, slotIndex, null);
}

// discardSlot: remove the card AND mark it as consumed (out of deck for the
// rest of this game). Distinct from clearSlot, which just empties the slot
// without affecting the deck — that path is reserved for setSlot/undo.
function discardSlot(state, slotIndex) {
  const card = state.board[slotIndex];
  if (!card) return false;
  state.history.push({ kind: "discard", slotIndex, card });
  state.consumed.add(card);
  state.board[slotIndex] = null;
  return true;
}

function firstEmptySlot(state) {
  return state.board.findIndex((c) => c === null);
}

// addCard: place into the first empty slot. Returns slot index used, or -1
// if board is full.
// Returns the slot used, -1 if the field is full, and -2 if that exact card is
// already in play.
//
// The palette greys out cards that are on the board or already consumed, but
// the keyboard path (press R, then 6) never goes through the palette — so R6
// could be entered twice. Two copies of one card cannot exist in the real game,
// and every solver number downstream is computed from the card set, so a
// duplicate silently corrupts the rest of the run.
// Reported by Flavius (flaviusrzv/metin2-okey-helper), 2026-09-15.
function addCard(state, cardId) {
  if (state.consumed.has(cardId)) return -2;
  for (let i = 0; i < state.board.length; i++) {
    if (state.board[i] === cardId) return -2;
  }
  const idx = firstEmptySlot(state);
  if (idx < 0) return -1;
  setSlot(state, idx, cardId);
  return idx;
}

// confirmPick: lock in a 3-card selection, score it, remove the picked cards
// from the board. Returns {gained, hand, type, label}.
function confirmPick(state, pickedSlots) {
  if (!pickedSlots || pickedSlots.length !== HAND_SIZE) {
    return { gained: 0, hand: [], type: "none", label: "Need 3 cards" };
  }
  const hand = pickedSlots.map((i) => state.board[i]);
  if (hand.some((c) => !c)) {
    return { gained: 0, hand: [], type: "none", label: "Empty slots in pick" };
  }
  const { score: gained, type, label } = scoreHand(hand);

  state.history.push({
    kind: "confirm",
    prevBoard: [...state.board],
    prevScore: state.score,
    pickedSlots: [...pickedSlots],
    hand: [...hand],
    gained, type, label,
  });

  // Picked cards leave the board AND the deck — scored cards never come back.
  for (const i of pickedSlots) {
    state.consumed.add(state.board[i]);
    state.board[i] = null;
  }
  state.score += gained;
  state.log.push({ hand, gained, type, label });

  return { gained, hand, type, label };
}

function undo(state) {
  // Step over auto-fills from practice mode — they belong to the prior user
  // action, not their own undo step. Without this, undo would unwind one
  // random draw at a time, which feels broken to the user.
  while (state.history.length > 0 && state.history[state.history.length - 1].auto) {
    const auto = state.history.pop();
    if (auto.kind === "setSlot") state.board[auto.slotIndex] = auto.prev;
  }
  const last = state.history.pop();
  if (!last) return false;
  if (last.kind === "setSlot") {
    state.board[last.slotIndex] = last.prev;
    return true;
  }
  if (last.kind === "discard") {
    state.board[last.slotIndex] = last.card;
    state.consumed.delete(last.card);
    return true;
  }
  if (last.kind === "confirm") {
    state.board = last.prevBoard;
    state.score = last.prevScore;
    state.log.pop();
    for (const c of last.hand) state.consumed.delete(c);
    return true;
  }
  return false;
}

function resetState(state) {
  state.board = Array(BOARD_SIZE).fill(null);
  state.score = 0;
  state.consumed = new Set();
  state.history = [];
  state.log = [];
}

function isBoardFull(state) {
  return state.board.every((c) => c !== null);
}

function filledCards(state) {
  return state.board.filter((c) => c !== null);
}

// Set of card IDs the palette should grey out — currently-on-board union with
// consumed (discarded or scored). Both are out of the deck for this game.
function usedCardSet(state) {
  const out = new Set(state.consumed);
  for (const c of state.board) if (c) out.add(c);
  return out;
}

// Cards still in the deck (not on the board and not consumed). Used by the
// solver for discard EV and by practice mode for random draws.
// Every card id in the canonical order (colours outer, values inner). Callers
// depend on that order being stable, so it is the same order the old nested
// loop produced.
const ALL_CARD_IDS = [];
for (const color of COLORS) for (const v of VALUES) ALL_CARD_IDS.push(cardId(color, v));

// Called several times per decision and once per playout step. The old version
// allocated a fresh Set (copying `consumed`) and built all 24 ids as template
// literals on EVERY call — 8.4% of search time in the 2026-09-15 profile, all
// of it rebuilding constants. The ids are now shared, and with a board of at
// most five slots a linear scan beats constructing a Set to query it.
function deckRemaining(state) {
  const consumed = state.consumed;
  const board = state.board;
  const out = [];
  for (let i = 0; i < ALL_CARD_IDS.length; i++) {
    const id = ALL_CARD_IDS[i];
    if (consumed.has(id)) continue;
    let onBoard = false;
    for (let s = 0; s < board.length; s++) {
      if (board[s] === id) { onBoard = true; break; }
    }
    if (!onBoard) out.push(id);
  }
  return out;
}

// Practice mode: fill empty slots with random cards from deckRemaining.
// History entries get `auto: true` so undo() can step over them and treat
// the entire user-action-plus-refill as one "round" boundary.
//
// `rand` is plug-in for testing; defaults to Math.random.
function autoFillBoardFromDeck(state, rand = Math.random) {
  while (true) {
    const slot = firstEmptySlot(state);
    if (slot < 0) break;
    const deck = deckRemaining(state);
    if (deck.length === 0) break;
    const card = deck[Math.floor(rand() * deck.length)];
    state.history.push({ kind: "setSlot", slotIndex: slot, prev: null, auto: true });
    state.board[slot] = card;
  }
}


// ===== potential.js =====
// Card potential — what a single card is still worth, given the exact set of
// cards that are still in play.
//
// The deck is perfect information: 24 unique cards (1..8 x R/B/Y), and a card
// that has been picked or discarded never comes back. So at any moment we know
// exactly which combos are still ALIVE:
//
//   three of a kind (value v)  needs all three colors of v  -> 20 + (v-1)*10
//   same-color run (low L)     needs c(L), c(L+1), c(L+2)   -> 50 + (L-1)*10
//   mixed run (low L)          needs one card of each of     -> L * 10
//                              L, L+1, L+2 (any colors)
//
// potentialOf(card) = the best alive combo that card can still join. That is
// the honest replacement for a flat opportunity-cost constant: dumping a card
// whose partners are all gone costs almost nothing, dumping the B7 while B6
// and B8 are alive costs a 100-point run.

const MIN_RUN_LOW = 1;
const MAX_RUN_LOW = 6; // runs are L, L+1, L+2 with L+2 <= 8

function scoreTriple(v) { return 20 + (v - 1) * 10; }
function scoreSameRun(low) { return 50 + (low - 1) * 10; }
function scoreMixedRun(low) { return low * 10; }

// availableSet: Set of cardIds still in play (deck + face-up board).
function makeAvailableSet(deckCards, boardCards) {
  const s = new Set(deckCards);
  for (const c of boardCards) if (c) s.add(c);
  return s;
}

function valueIsAvailable(available, v) {
  for (const c of COLORS) if (available.has(`${c}${v}`)) return true;
  return false;
}

// Best alive combo score containing `id`. Always >= 10 while the card exists
// in a run-able neighbourhood; 0 only if nothing at all can be formed.
function potentialOf(id, available) {
  const { color, value } = parseCardId(id);
  let best = 0;

  // three of a kind: needs the other two colors of the same value
  let allColors = true;
  for (const c of COLORS) if (!available.has(`${c}${value}`)) { allColors = false; break; }
  if (allColors) best = Math.max(best, scoreTriple(value));

  const lowFrom = Math.max(MIN_RUN_LOW, value - 2);
  const lowTo = Math.min(MAX_RUN_LOW, value);
  for (let low = lowFrom; low <= lowTo; low++) {
    // same-color run
    if (available.has(`${color}${low}`) &&
        available.has(`${color}${low + 1}`) &&
        available.has(`${color}${low + 2}`)) {
      best = Math.max(best, scoreSameRun(low));
    }
    // mixed run: any color per value is fine
    if (valueIsAvailable(available, low) &&
        valueIsAvailable(available, low + 1) &&
        valueIsAvailable(available, low + 2)) {
      best = Math.max(best, scoreMixedRun(low));
    }
  }
  return best;
}

// Convenience: potentials for a whole board (nulls -> 0).
function boardPotentials(board, available) {
  return board.map((c) => (c ? potentialOf(c, available) : 0));
}

// Total remaining upside of the cards still in play: greedy set-packing over
// alive combos, highest score first. Used as a state value function / for
// reporting "how much is still on the table".
// Highest total still theoretically reachable. Used to decide whether a better
// chest is possible at all, so it MUST NOT come out too low — calling a run
// finished while it is still winnable is the one unacceptable error.
//
// packCombos only knows triples and same-colour runs. A position whose only
// remaining scoring options are mixed runs would come back as 0, which is
// exactly that unacceptable error (it happened once in 26 detector firings
// before mixed runs were added here). Mixed runs are therefore thrown into the
// pool without a disjointness check: that can over-count, and over-counting is
// the harmless direction.
function bestAchievable(available, maxPicks) {
  if (maxPicks <= 0) return 0;
  const pool = [...packCombos(available), ...mixedRunScores(available)];
  pool.sort((a, b) => b - a);
  return pool.slice(0, maxPicks).reduce((a, b) => a + b, 0);
}

// Score of every mixed run still formable: three consecutive values, each of
// which still exists in some colour.
function mixedRunScores(available) {
  const out = [];
  for (let low = MIN_RUN_LOW; low <= MAX_RUN_LOW; low++) {
    if (valueIsAvailable(available, low) &&
        valueIsAvailable(available, low + 1) &&
        valueIsAvailable(available, low + 2)) {
      out.push(scoreMixedRun(low));
    }
  }
  return out;
}

function packCombos(available) {
  const combos = [];
  for (const v of VALUES) {
    let ok = true;
    for (const c of COLORS) if (!available.has(`${c}${v}`)) { ok = false; break; }
    if (ok) combos.push({ score: scoreTriple(v), cards: COLORS.map((c) => `${c}${v}`) });
  }
  for (const c of COLORS) {
    for (let low = MIN_RUN_LOW; low <= MAX_RUN_LOW; low++) {
      const cards = [`${c}${low}`, `${c}${low + 1}`, `${c}${low + 2}`];
      if (cards.every((id) => available.has(id))) {
        combos.push({ score: scoreSameRun(low), cards });
      }
    }
  }
  combos.sort((a, b) => b.score - a.score);

  const used = new Set();
  const out = [];
  for (const combo of combos) {
    if (combo.cards.some((id) => used.has(id))) continue;
    for (const id of combo.cards) used.add(id);
    out.push(combo.score);
  }
  return out;
}

function deckPotential(available) {
  return packCombos(available).reduce((a, b) => a + b, 0);
}

// ---------- board-aware potential ----------
//
// potentialOf() judges a card in isolation: the lone R6 and the R6 sitting
// next to an R7 both score "a 100-point run is still alive". But those are
// completely different cards to hold. Completing a combo means gathering all
// three cards in a 5-slot window one draw at a time, so a card whose partners
// are ALREADY face-up is worth far more than one whose partners are somewhere
// in the deck.
//
// synergyPotential weights each alive combo by how many of its other two
// cards are already on the board:
//
//   2 partners on board -> 1.00  (one draw away; in practice we just pick it)
//   1 partner on board  -> PARTNER_WEIGHT
//   0 partners on board -> LONE_WEIGHT
//
// Defaults grid-searched in bench/benchmark.mjs.
const LONE_WEIGHT = 0.25;
const PARTNER_WEIGHT = 0.55;

function comboPartners(id, available) {
  const { color, value } = parseCardId(id);
  const out = [];

  let allColors = true;
  for (const c of COLORS) if (!available.has(`${c}${value}`)) { allColors = false; break; }
  if (allColors) {
    out.push({
      score: scoreTriple(value),
      partners: COLORS.filter((c) => c !== color).map((c) => `${c}${value}`),
    });
  }

  const lowFrom = Math.max(MIN_RUN_LOW, value - 2);
  const lowTo = Math.min(MAX_RUN_LOW, value);
  for (let low = lowFrom; low <= lowTo; low++) {
    const same = [`${color}${low}`, `${color}${low + 1}`, `${color}${low + 2}`];
    if (same.every((c) => available.has(c))) {
      out.push({ score: scoreSameRun(low), partners: same.filter((c) => c !== id) });
    }
    // Mixed runs: the cheapest partner of each neighbouring value that is
    // still alive. Low value, but it keeps dead-end cards from reading as 0.
    const neighbours = [low, low + 1, low + 2].filter((v) => v !== value);
    const picks = [];
    for (const v of neighbours) {
      const found = COLORS.map((c) => `${c}${v}`).find((c) => available.has(c) && c !== id);
      if (found) picks.push(found);
    }
    if (picks.length === neighbours.length) {
      out.push({ score: scoreMixedRun(low), partners: picks });
    }
  }
  return out;
}

// `exclude` (array of 3 cardIds) drops one combo from consideration. Needed
// when costing a PICK: the cards of the hand we are about to take obviously
// all sit on the board, so without the exclusion every pick would look free.
// What we actually want to know is what those cards could do INSTEAD.
function synergyPotential(id, board, available, weights = {}, exclude = null) {
  const lone = weights.lone ?? LONE_WEIGHT;
  const partnerW = weights.partner ?? PARTNER_WEIGHT;
  const onBoard = new Set(board.filter(Boolean));
  const excludeKey = exclude ? [...exclude].sort().join(",") : null;

  let best = 0;
  for (const combo of comboPartners(id, available)) {
    if (excludeKey && [id, ...combo.partners].sort().join(",") === excludeKey) continue;
    let have = 0;
    for (const p of combo.partners) if (onBoard.has(p)) have++;
    const w = have >= 2 ? 1 : have === 1 ? partnerW : lone;
    best = Math.max(best, combo.score * w);
  }
  return best;
}


// ===== endgame.js =====
// Exact endgame solver.
//
// Once few cards are left, the position is small enough to solve outright
// instead of estimating it. The deck is perfect information as a SET — only
// the order is unknown — so the game is a finite MDP:
//
//   state   = (cards still in play A, the face-up cards B subset of A)
//   actions = pick any 3 of B (scores, those cards leave A), or discard 1 of B
//   chance  = replacements are drawn uniformly from A \ B
//
// Consumed cards never matter again, so they stay out of the state. That is
// what keeps this tractable: from a position with `a` cards left there are
// O(3^a) reachable (A, B) pairs, not O(2^24).
//
// Threshold objective, every threshold at once
// --------------------------------------------
// Chests are thresholds, so the value of a state is not a number but a curve:
// P(score at least 0 more), P(at least 10 more), P(at least 20 more), ...
// Every combo pays a multiple of 10, so that curve is a small array, and one
// pass answers silver, gold, and "we are 40 short with two rounds left" — the
// situation that actually decides chests.
//
//   value[t] = max over actions of E[ value_after[t - gained] ]
//
// The per-threshold max is legitimate: the player knows their score, so for
// each t this is a well-defined MDP and the best action may differ per t. That
// is the point — the same board is "bank it" at t=20 and "gamble" at t=90.

const CARD_COUNT = 24;
const STEP = 10; // every combo pays a multiple of 10
const GOLD_WEIGHT = 2;

// ---- card indexing: 0..23, index = colour * 8 + (value - 1) ----
function cardIndex(id) {
  return COLORS.indexOf(id[0]) * 8 + (Number(id.slice(1)) - 1);
}
function indexToCard(i) {
  return cardId(COLORS[Math.floor(i / 8)], (i % 8) + 1);
}
function maskOf(cards) {
  let m = 0;
  for (const c of cards) if (c) m |= 1 << cardIndex(c);
  return m;
}
function bitsOf(mask) {
  const out = [];
  for (let i = 0; i < CARD_COUNT; i++) if (mask & (1 << i)) out.push(i);
  return out;
}
function popcount(m) {
  let n = 0;
  while (m) { m &= m - 1; n++; }
  return n;
}

// ---- precomputed scores for all C(24,3) triples ----
const TRIPLE_SCORE = new Int16Array(CARD_COUNT * CARD_COUNT * CARD_COUNT);
(function buildScores() {
  for (let i = 0; i < CARD_COUNT; i++) {
    for (let j = i + 1; j < CARD_COUNT; j++) {
      for (let k = j + 1; k < CARD_COUNT; k++) {
        TRIPLE_SCORE[i * 576 + j * 24 + k] =
          scoreHand([indexToCard(i), indexToCard(j), indexToCard(k)]).score;
      }
    }
  }
})();
function tripleScore(i, j, k) {
  const a = Math.min(i, j, k), c = Math.max(i, j, k);
  return TRIPLE_SCORE[a * 576 + (i + j + k - a - c) * 24 + c];
}

// All k-element subsets of `bits`, returned as bitmasks.
function subsetsOfSize(bits, k) {
  const out = [];
  const n = bits.length;
  if (k > n || k < 0) return out;
  if (k === 0) return [0];
  const idx = Array.from({ length: k }, (_, i) => i);
  for (;;) {
    let m = 0;
    for (let p = 0; p < k; p++) m |= 1 << bits[idx[p]];
    out.push(m);
    let i = k - 1;
    while (i >= 0 && idx[i] === n - k + i) i--;
    if (i < 0) break;
    idx[i]++;
    for (let j = i + 1; j < k; j++) idx[j] = idx[j - 1] + 1;
  }
  return out;
}


// ---- colour symmetry (MEASURED, OFF BY DEFAULT) ----
//
// Red, blue and yellow are interchangeable, so a position and any recolouring
// of it have identical value. Folding the memo key onto a canonical colouring
// looks like a free 6x — and it is not.
//
// From a real position the set of cards in play is FIXED. Recolouring it
// produces a card set that never occurs anywhere in that search tree, so
// almost nothing collapses: measured 1.03x fewer states and ~10% slower from
// the extra work per lookup (bench/symmetry-check.mjs; results identical to
// the last digit). Symmetry would only pay off for a fully precomputed table
// over all positions, which is a different project.
//
// Kept, off by default, so the idea is not retried blind.
//
// Colour c owns bits c*8 .. c*8+7, so a permutation is just moving three bytes.
const COLOR_PERMS = [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]];

function permuteMask(mask, perm) {
  let out = 0;
  for (let c = 0; c < 3; c++) out |= ((mask >> (c * 8)) & 0xFF) << (perm[c] * 8);
  return out;
}

// Largest (available, board) pair over all recolourings — a stable
// representative of the whole symmetry class.
function canonicalKey(available, board) {
  let bestA = -1, bestB = -1;
  for (let p = 0; p < COLOR_PERMS.length; p++) {
    const a = permuteMask(available, COLOR_PERMS[p]);
    if (a < bestA) continue;
    const b = permuteMask(board, COLOR_PERMS[p]);
    if (a > bestA || b > bestB) { bestA = a; bestB = b; }
  }
  return bestA * 16777216 + bestB;
}

class EndgameSolver {
  // nodeLimit guards against being handed a position that is still too big.
  constructor({ nodeLimit = 5e6, symmetry = false } = {}) {
    this.memo = new Map();
    this.symmetry = symmetry;
    this.nodeLimit = nodeLimit;
    this.nodes = 0;
    this.NT = 1;
  }

  // Value curve of a position. Throws RangeError past nodeLimit.
  // Sets the threshold grid from the root position and resets the table.
  solve(available, board) {
    this.prepare(available);
    return this.value(available, board);
  }

  // Set up the threshold grid without discarding the table — for playing a
  // position out move by move, where every later state is a sub-state of the
  // first and the memo stays valid.
  prepare(available) {
    this.NT = Math.floor(popcount(available) / 3) * 10 + 1;
    this.nodes = 0;
    this.memo.clear();
  }

  value(available, board) {
    const key = this.symmetry ? canonicalKey(available, board) : available * 16777216 + board;
    const hit = this.memo.get(key);
    if (hit !== undefined) return hit;
    if (++this.nodes > this.nodeLimit) throw new RangeError("endgame node limit exceeded");

    const NT = this.NT;
    const vec = new Float32Array(NT);
    vec[0] = 1; // "at least 0 more points" is free

    const boardBits = bitsOf(board);
    const deckBits = bitsOf(available & ~board);
    const drawCount = Math.min(3, deckBits.length);

    // --- picks ---
    for (let x = 0; x + 2 < boardBits.length; x++) {
      for (let y = x + 1; y + 1 < boardBits.length; y++) {
        for (let z = y + 1; z < boardBits.length; z++) {
          const i = boardBits[x], j = boardBits[y], k = boardBits[z];
          const gained = tripleScore(i, j, k);
          if (gained === 0) continue; // burning 3 cards for nothing never helps
          const hand = (1 << i) | (1 << j) | (1 << k);
          const acc = this.chance(available & ~hand, board & ~hand, deckBits, drawCount);
          const shift = gained / STEP;
          for (let t = 0; t < NT; t++) {
            const src = t - shift;
            const p = src <= 0 ? 1 : (src < NT ? acc[src] : 0);
            if (p > vec[t]) vec[t] = p;
          }
        }
      }
    }

    // --- discards (pointless with an empty deck: no replacement arrives) ---
    if (deckBits.length > 0) {
      for (const c of boardBits) {
        const kept = board & ~(1 << c);
        const nextAvail = available & ~(1 << c);
        const acc = this.chance(nextAvail, kept, bitsOf(nextAvail & ~kept), 1);
        for (let t = 0; t < NT; t++) if (acc[t] > vec[t]) vec[t] = acc[t];
      }
    }

    this.memo.set(key, vec);
    return vec;
  }

  // Value curve of a position whose field is not full yet.
  //
  // `value` reads the board mask as THE field, so a four-card board describes a
  // game played in a permanently four-wide window: every refill after a pick or
  // a discard tops it back up to four, never to five. That is not this game —
  // the missing cards are dealt before the player can do anything — and the
  // difference is not cosmetic: a hand that needs all five slots to be held
  // together comes out unreachable. So deal the gap first and average over
  // every equally likely fill.
  valueAfterFill(available, board, missing) {
    const deckBits = bitsOf(available & ~board);
    const n = Math.min(missing, deckBits.length);
    if (n <= 0) return this.value(available, board);
    return this.chance(available, board, deckBits, n);
  }

  // Average the value over every equally likely set of replacement cards.
  chance(available, kept, deckBits, drawCount) {
    const NT = this.NT;
    const acc = new Float32Array(NT);
    const k = Math.min(drawCount, deckBits.length);
    if (k <= 0) {
      acc.set(this.value(available, kept));
      return acc;
    }
    const draws = subsetsOfSize(deckBits, k);
    for (const draw of draws) {
      const v = this.value(available, kept | draw);
      for (let t = 0; t < NT; t++) acc[t] += v[t];
    }
    for (let t = 0; t < NT; t++) acc[t] /= draws.length;
    return acc;
  }


  // Best move judged by both chests at once.
  //
  // The value curve already holds P(reach silver) and P(reach gold) for every
  // action, so there is nothing to configure: rank by
  //
  //     P(silver) + GOLD_WEIGHT * P(gold)
  //
  // and the requested behaviour falls out on its own. Once silver is banked,
  // needSilver <= 0 makes P(silver) = 1 for every move and the ranking
  // collapses to pure gold hunting. Once gold is out of reach, P(gold) = 0
  // everywhere and it collapses to locking in silver. In between it trades the
  // two at their real prices, with no threshold constant to tune.
  //
  // GOLD_WEIGHT = 2 (gold counts triple overall, since gold implies silver)
  // is the setting that won the objective benchmark.
  bestMoveChest(available, board, needSilver, needGold, keepMemo = false) {
    if (!keepMemo) this.solve(available, board);
    else this.value(available, board);
    const NT = this.NT;
    const at = (vec, need, shift) => {
      const src = Math.ceil(need / STEP) - shift;
      if (src <= 0) return 1;
      return src < NT ? vec[src] : 0;
    };

    const boardBits = bitsOf(board);
    const deckBits = bitsOf(available & ~board);
    const drawCount = Math.min(3, deckBits.length);

    // Expected points still to come, read straight off the value curve: for a
    // non-negative variable on a 10-point grid, E[X] = 10 * sum of P(X >= t).
    const expected = (vec) => {
      let e = 0;
      for (let t = 1; t < NT; t++) e += vec[t];
      return e * STEP;
    };

    let best = null;
    const consider = (stats) => {
      const rank = stats.pSilver + GOLD_WEIGHT * stats.pGold;
      // Points are the LAST word, never the first. Once the chest is settled
      // — silver locked and gold gone — every line has the same probabilities
      // and the solver would otherwise pick at random, throwing away a
      // 90-point hand for a 10-point one. It costs no chest to also be greedy
      // about points in that situation, and it looks far less broken.
      const betterRank = !best || rank > best.rank + 1e-9;
      const tiedRank = best && Math.abs(rank - best.rank) <= 1e-9;
      if (betterRank || (tiedRank && stats.expected > best.expected + 1e-6)) {
        best = { ...stats, rank };
      }
    };

    for (let x = 0; x + 2 < boardBits.length; x++) {
      for (let y = x + 1; y + 1 < boardBits.length; y++) {
        for (let z = y + 1; z < boardBits.length; z++) {
          const i = boardBits[x], j = boardBits[y], k = boardBits[z];
          const gained = tripleScore(i, j, k);
          if (gained === 0) continue;
          const hand = (1 << i) | (1 << j) | (1 << k);
          const acc = this.chance(available & ~hand, board & ~hand, deckBits, drawCount);
          const shift = gained / STEP;
          consider({
            kind: "pick", cards: [i, j, k].map(indexToCard), gained,
            pSilver: at(acc, needSilver, shift), pGold: at(acc, needGold, shift),
            expected: gained + expected(acc),
          });
        }
      }
    }
    if (deckBits.length > 0) {
      for (const c of boardBits) {
        const kept = board & ~(1 << c);
        const nextAvail = available & ~(1 << c);
        const acc = this.chance(nextAvail, kept, bitsOf(nextAvail & ~kept), 1);
        consider({
          kind: "discard", cards: [indexToCard(c)], gained: 0,
          pSilver: at(acc, needSilver, 0), pGold: at(acc, needGold, 0),
          expected: expected(acc),
        });
      }
    }
    return best;
  }

  // Best move for a concrete need (points still required for the target chest).
  // `keepMemo` reuses the existing table (see prepare()).
  bestMove(available, board, need, keepMemo = false) {
    if (!keepMemo) this.solve(available, board);
    else this.value(available, board);
    const NT = this.NT;
    const want = Math.max(0, Math.min(NT - 1, Math.ceil(need / STEP)));
    const boardBits = bitsOf(board);
    const deckBits = bitsOf(available & ~board);
    const drawCount = Math.min(3, deckBits.length);

    let best = null;
    for (let x = 0; x + 2 < boardBits.length; x++) {
      for (let y = x + 1; y + 1 < boardBits.length; y++) {
        for (let z = y + 1; z < boardBits.length; z++) {
          const i = boardBits[x], j = boardBits[y], k = boardBits[z];
          const gained = tripleScore(i, j, k);
          if (gained === 0) continue;
          const hand = (1 << i) | (1 << j) | (1 << k);
          const acc = this.chance(available & ~hand, board & ~hand, deckBits, drawCount);
          const src = want - gained / STEP;
          const p = src <= 0 ? 1 : (src < NT ? acc[src] : 0);
          if (!best || p > best.p) {
            best = { p, kind: "pick", cards: [i, j, k].map(indexToCard), gained };
          }
        }
      }
    }
    if (deckBits.length > 0) {
      for (const c of boardBits) {
        const kept = board & ~(1 << c);
        const nextAvail = available & ~(1 << c);
        const acc = this.chance(nextAvail, kept, bitsOf(nextAvail & ~kept), 1);
        if (!best || acc[want] > best.p) {
          best = { p: acc[want], kind: "discard", cards: [indexToCard(c)] };
        }
      }
    }
    return best;
  }
}


// ===== solver.js =====
// Okey solver. Two responsibilities:
//
//   1. rankCombos(board) — score every C(5,3) three-card pick (used by the
//      "all combos" panel and by the EV calculation below).
//   2. suggestMove(state) — decides between PICKING the best 3 from the field
//      now vs DISCARDING some subset to draw replacements. For each non-empty
//      subset D of currently-filled slots, computes the expected score of the
//      best 3-pick after replacing D with random cards from the remaining
//      deck (sampling without replacement, exact enumeration). Picks if no
//      discard improves on the current best; otherwise recommends the subset
//      with the highest expected score.

function* combos3(n) {
  for (let i = 0; i < n - 2; i++)
    for (let j = i + 1; j < n - 1; j++)
      for (let k = j + 1; k < n; k++) yield [i, j, k];
}

// All k-element index combinations of [0..n).
function* combosK(n, k) {
  if (k === 0) { yield []; return; }
  if (k > n) return;
  const idx = Array.from({ length: k }, (_, i) => i);
  while (true) {
    yield idx.slice();
    let i = k - 1;
    while (i >= 0 && idx[i] === n - k + i) i--;
    if (i < 0) return;
    idx[i]++;
    for (let j = i + 1; j < k; j++) idx[j] = idx[j - 1] + 1;
  }
}

// ---------- pick scoring (existing API) ----------

function rankCombos(board) {
  const filled = [];
  for (let i = 0; i < board.length; i++) if (board[i]) filled.push(i);
  if (filled.length < 3) return [];

  const out = [];
  for (const [a, b, c] of combos3(filled.length)) {
    const slots = [filled[a], filled[b], filled[c]];
    const cards = slots.map((s) => board[s]);
    const result = scoreHand(cards);
    out.push({ slots, cards, ...result });
  }
  out.sort((x, y) => y.score - x.score);
  return out;
}

function bestPick(board) {
  const ranked = rankCombos(board);
  return ranked[0] || null;
}

// ---------- discard expected-value ----------

// Best 3-pick score on a 5-slot array (some may be null) — convenience for
// the EV inner loop.
function bestPickScore(boardArr) {
  const ranked = rankCombos(boardArr);
  return ranked.length ? ranked[0].score : 0;
}

// Expected best-pick score after discarding `discardSlots` and drawing
// |discardSlots| random replacement cards (without replacement) from `deck`.
// Returns null if the deck is too small to refill.
function expectedScoreAfterDiscard(board, discardSlots, deck) {
  const k = discardSlots.length;
  if (k > deck.length) return null;
  if (k === 0) return bestPickScore(board);

  // Slots we keep (their cards survive).
  const keepSlots = [];
  for (let i = 0; i < board.length; i++) {
    if (board[i] && !discardSlots.includes(i)) keepSlots.push(i);
  }
  const keepCards = keepSlots.map((s) => board[s]);

  let total = 0;
  let count = 0;
  for (const drawIdx of combosK(deck.length, k)) {
    const drawn = drawIdx.map((i) => deck[i]);
    const newBoard = [...keepCards, ...drawn];
    while (newBoard.length < BOARD_SIZE) newBoard.push(null);
    total += bestPickScore(newBoard);
    count++;
  }
  return count > 0 ? total / count : 0;
}


// ---------- exact EV, computed cheaply ----------
//
// expectedScoreAfterDiscard() re-ranks the whole 5-card board once per deck
// card. That is O(deck * 10) hand scorings per candidate discard, and it is
// the reason the solver is too slow to put inside a search.
//
// It is also unnecessary. After discarding one card, four cards stay. A drawn
// card can only score by joining TWO of those four, so:
//
//     best pick after the draw = max(best pick among the 4 kept,
//                                    best combo the drawn card forms with a pair)
//
// The second term is a lookup: enumerate the C(4,2)=6 pairs once, write down
// which single card completes each of them and for how many points, then walk
// the deck. Same numbers as the old function, ~20x less work.
//
// completionsFor returns Map(cardId -> best score that card would create).
function completionsFor(kept) {
  const out = new Map();
  const bump = (id, score) => {
    const prev = out.get(id);
    if (prev === undefined || score > prev) out.set(id, score);
  };

  for (let i = 0; i < kept.length - 1; i++) {
    for (let j = i + 1; j < kept.length; j++) {
      const a = parseCardId(kept[i]);
      const b = parseCardId(kept[j]);

      if (a.value === b.value) {
        // third colour of the same value completes a three-of-a-kind
        for (const c of COLORS) {
          if (c === a.color || c === b.color) continue;
          bump(`${c}${a.value}`, scoreHand([kept[i], kept[j], `${c}${a.value}`]).score);
        }
        continue;
      }

      const lo = Math.min(a.value, b.value);
      const hi = Math.max(a.value, b.value);
      const gap = hi - lo;
      if (gap > 2) continue;

      // Which values would turn the pair into three consecutive values?
      const wanted = gap === 2 ? [lo + 1] : [lo - 1, hi + 1];
      for (const v of wanted) {
        if (v < 1 || v > 8) continue;
        for (const c of COLORS) {
          const id = `${c}${v}`;
          if (id === kept[i] || id === kept[j]) continue;
          bump(id, scoreHand([kept[i], kept[j], id]).score);
        }
      }
    }
  }
  return out;
}

// Expected best-pick score after discarding one card and drawing one, exact.
function evAfterSingleDiscard(kept, deck) {
  if (deck.length === 0) return null;
  const keptBoard = [...kept];
  while (keptBoard.length < BOARD_SIZE) keptBoard.push(null);
  const base = bestPickScore(keptBoard);
  const completions = completionsFor(kept);

  let total = 0;
  for (const card of deck) {
    const withDraw = completions.get(card) ?? 0;
    total += withDraw > base ? withDraw : base;
  }
  return total / deck.length;
}

// ---------- suggestion entry point ----------

// Returns one of:
//   { kind: "pick",    slots, cards, score, type, label, reasoning }
//   { kind: "discard", slots, expectedAfter, reasoning }
//   null  — nothing on the board
//
// Why we only consider single-card discards: sequential single discards
// weakly dominate any batch discard in EV. After each single discard you see
// the new card and can choose pick / discard-another, which is strictly more
// flexible than committing to "discard N at once". So the optimal policy is
// always a sequence of single discards (or pick).
//
// Why we charge OPPORTUNITY_COST per discard: each discard burns one card
// from the deck — that's ~1/3 of a future pick (since picks consume 3
// cards). Without this charge, the solver "infinitely" discards low-EV
// improvements and runs the deck dry on marginal draws (avg ~169pts in
// 2000-game simulation, 94% bronze). With the charge, it stops chasing
// trivial improvements and accumulates picks (266pts avg, 29% silver, 2.5%
// gold). Empirically tuned via grid search; OC=5 was best in [1..12], with
// a flat plateau around 4-6 (so the value isn't fragile).

const EV_TIE_EPSILON = 0.01;
const OPPORTUNITY_COST_PER_DISCARD = 5;

// ---------- v2: potential-based costs ----------
//
// v1 (above) charges a flat 5 points per discard and judges a pick purely by
// its own score. Both are blind to WHICH cards are being spent. v2 replaces
// them with the exact card potential (see potential.js):
//
//   discard cost   = lambda * potential(card) / 3
//       A combo eats three cards, so one card is worth ~1/3 of the best combo
//       it could still join. Dumping a dead 2 costs ~3 pts; dumping the B7
//       between a live B6 and B8 costs ~33.
//
//   pick damage    = lambda * max(0, avg(potential of the 3 cards) - score)
//       Taking a mixed 6-7-8 for 60 spends three cards that were each worth
//       ~90 in the best case -> it is punished. Taking a same-color 6-7-8 for
//       100 spends cards worth exactly that -> free.
//
// Net effect: the solver stops cannibalising high cards for cheap mixed runs
// and stops churning discards on cards nothing can use.
// lambda weights the potential terms against raw points. Grid-searched on
// 5000 games (bench/benchmark.mjs --sweep): monotone up to ~6, then a flat
// plateau through 20 (45.5% silver either way), so 6 sits mid-plateau and is
// not fragile.
const DEFAULT_LAMBDA = 6;

// `options.policy`: "v1" (flat opportunity cost) or "v2" (potential-based,
// default). `options.opportunityCost` / `options.lambda` tune them; only the
// offline benchmark passes these — the UI calls suggestMove(state).
function suggestMove(state, options = {}) {
  const policy = options.policy ?? "v2";
  if (policy === "fast") return suggestMoveFast(state, options);
  if (policy === "v1") return suggestMoveV1(state, options);
  return suggestMoveV2(state, options);
}

// How many scoring rounds are still physically possible: every pick eats 3
// cards and every discard eats 1, so the cards left (deck + face-up) divided
// by 3 is the hard ceiling on remaining picks.
function picksLeft(state) {
  const deck = deckRemaining(state);
  let filled = 0;
  for (const c of state.board) if (c) filled++;
  return Math.floor((deck.length + filled) / 3);
}

// Two ideas contributed by Flavius (flaviusrzv/metin2-okey-helper, 2026-09-15),
// ported here as OPTIONS so they can be measured in the shipping policy before
// anything changes. Both default OFF, so the helper plays exactly as before
// until a fresh-seed benchmark says otherwise.
//
//   typeAware      scale the pick damage by what KIND of combo is being taken.
//                  A mixed run spends cards that a same-colour run would pay
//                  far more for, so it is punished double; a same-colour run
//                  or a big triple spends them at full value, so it is free.
//   residualWeight the two cards still on the board after a 3-pick have value
//                  of their own. Weight > 0 adds their potential to the pick's
//                  score, preferring picks that leave a live board behind.
//
// NB both cost playout time, and the heuristic runs inside every rollout
// playout — so they must be judged on rate AND latency, not rate alone.
const DEFAULT_TYPE_AWARE = false;
const DEFAULT_RESIDUAL_WEIGHT = 0;

// Damage multiplier by combo type. Derived from the scoring table in game.js:
// a same-colour run pays 50-100, a mixed run of the same three values only
// 10-60, so the mixed run is the one that wastes the cards.
function typeMultiplier(cards, score) {
  const values = cards.map((c) => Number(c.slice(1))).sort((a, b) => a - b);
  const isRun = values[0] + 1 === values[1] && values[1] + 1 === values[2];
  if (isRun && cards.every((c) => c[0] === cards[0][0])) return 0;   // same-colour run
  if (isRun) return 2.0;                                            // mixed run
  const isTriple = values[0] === values[1] && values[1] === values[2];
  if (isTriple) return score >= 60 ? 0 : 0.5;
  return 1;                                                         // no combo
}

function suggestMoveV2(state, options = {}) {
  const lambda = options.lambda ?? DEFAULT_LAMBDA;
  const endgame = options.endgame ?? true;
  const typeAware = options.typeAware ?? DEFAULT_TYPE_AWARE;
  const residualWeight = options.residualWeight ?? DEFAULT_RESIDUAL_WEIGHT;
  const board = state.board;
  const filledIndices = [];
  for (let i = 0; i < board.length; i++) if (board[i]) filledIndices.push(i);
  if (filledIndices.length === 0) return null;

  const deck = deckRemaining(state);
  const available = makeAvailableSet(deck, board);
  // v4 (REJECTED, kept for the record): board-aware potential, see
  // potential.js. Weighting combos by how many partners are already face-up
  // lost on every setting; a weight sweep converged monotonically on 1.0/1.0,
  // i.e. on plain v2. Off by default; options.synergy=true to re-measure.
  const useSynergy = options.synergy ?? false;
  const weights = { lone: options.lone, partner: options.partner };
  const potential = {};
  for (const i of filledIndices) {
    potential[i] = useSynergy
      ? synergyPotential(board[i], board, available, weights)
      : potentialOf(board[i], available);
  }

  // Endgame: card potential is only worth protecting while there are rounds
  // left to cash it in. On the last round a "valuable" card that we cannot
  // spend is worth nothing, so the cost terms fade out.
  const rounds = Math.floor((deck.length + filledIndices.length) / 3);
  const scale = endgame ? Math.max(0, Math.min(1, (rounds - 1) / 2)) : 1;
  if (endgame && rounds <= 1) {
    const final = finalRoundMove(state, board, deck, filledIndices);
    if (final) return final;
  }

  // Evaluate EVERY C(5,3) pick, not just the highest-scoring one. The best
  // pick by raw points is often the worst by net value: a mixed 6-7-8 scores
  // 60 but spends three cards that a same-colour run would pay 100 for, while
  // the triple 3s next to it scores 40 out of cards nothing else wants.
  const ranked = rankCombos(board);

  // Threshold-aware tail (options.thresholdTail = how many closing rounds it
  // applies to; 0 = off, which is the behaviour everything before 2026-09-08
  // was measured with).
  //
  // v2 is otherwise completely blind to the score: it maximises net points and
  // never looks at how far the player is from a chest. That is defensible for
  // the opening, where points and chest chances point the same way, and wrong
  // at the close, where they separate hard — at 280 with one pick left a
  // guaranteed 20 is the whole game and a 90 that might not land is worth
  // nothing, while at 220 it is exactly the other way round.
  //
  // It matters here more than it did when a threshold rule was tried as a
  // standalone policy and rejected (iteration 2): v2 is also the PLAYOUT policy
  // inside the rollout, so a tail that misjudges the close does not merely play
  // those positions badly, it feeds every candidate's P(silver) a biased
  // estimate — the failure that inverted a real position on 2026-09-08.
  //
  // Two rules, both consequences of the fact that the score only ever goes up,
  // so crossing a threshold locks that chest for good:
  //
  //   reach it   a pick that gets to the target now secures the chest; take the
  //              best of those and stop gambling.
  //   keep it    a pick that leaves more than the remaining rounds can possibly
  //              score is a chest thrown away — drop it, unless every candidate
  //              does that.
  const thresholdTail = options.thresholdTail ?? 0;
  let usable = ranked;
  if (thresholdTail > 0 && rounds <= thresholdTail && rounds >= 1) {
    const need = chestTarget(state.score) - state.score;
    const scoring = ranked.filter((c) => c.score > 0);
    const reaching = scoring.filter((c) => c.score >= need);
    if (reaching.length > 0) {
      usable = reaching;
    } else {
      // 100 is the highest a single pick can pay, so this is the most optimistic
      // bound there is — it only ever rules out the genuinely hopeless.
      const keeping = scoring.filter((c) => need - c.score <= 100 * (rounds - 1));
      if (keeping.length > 0) usable = keeping;
    }
  }

  let pick = null;
  let pickNet = -Infinity;
  let pickDamage = 0;
  for (const cand of usable) {
    if (cand.score <= 0) continue;
    // Cost a pick against what its cards could do INSTEAD — the combo being
    // taken is excluded, otherwise every completed hand costs nothing.
    const altPot = useSynergy
      ? cand.slots.map((s) => synergyPotential(board[s], board, available, weights, cand.cards))
      : cand.slots.map((s) => potential[s]);
    const avgPot = altPot.reduce((a, b) => a + b, 0) / 3;
    const typeMul = typeAware ? typeMultiplier(cand.cards, cand.score) : 1;
    const damage = lambda * scale * typeMul * Math.max(0, avgPot - cand.score);
    let net = cand.score - damage;
    // The cards this pick LEAVES behind. Their potential has to be recomputed
    // against the deck minus the picked cards — those leave the deck for good,
    // so scoring the residue against the old available set would credit it with
    // partners this very pick just consumed.
    if (residualWeight > 0) {
      const resSlots = filledIndices.filter((i) => !cand.slots.includes(i));
      if (resSlots.length === 2) {
        const resAvailable = new Set(available);
        for (const s of cand.slots) resAvailable.delete(board[s]);
        const r0 = potentialOf(board[resSlots[0]], resAvailable);
        const r1 = potentialOf(board[resSlots[1]], resAvailable);
        net += residualWeight * scale * (r0 + r1) / 2;
      }
    }
    if (net > pickNet) { pickNet = net; pick = cand; pickDamage = damage; }
  }
  if (!pick) {
    // Only fall back to a pick that actually SCORES. A zero-score pick spends
    // three cards for nothing and removes them from the deck for good, and the
    // UI used to render it as a live suggestion ("Pick R1 · R4 · B2 — no combo
    // for 0 pts") with an active confirm button. When nothing scores, the
    // honest answer is "no move", which lets the end-of-run overlay appear.
    // Reported by Flavius (flaviusrzv/metin2-okey-helper), 2026-09-15.
    pick = ranked.length && ranked[0].score > 0 ? ranked[0] : null;
    pickNet = -Infinity;
    pickDamage = 0;
  }
  const pickScore = pick ? pick.score : 0;

  let bestDiscard = null;
  for (const slot of filledIndices) {
    const kept = [];
    for (const i of filledIndices) if (i !== slot) kept.push(board[i]);
    const ev = evAfterSingleDiscard(kept, deck);
    if (ev === null) continue;
    const cost = lambda * scale * (potential[slot] / 3);
    const net = ev - cost;
    if (bestDiscard === null || net > bestDiscard.net) {
      bestDiscard = { slots: [slot], expectedAfter: ev, cost, net };
    }
  }

  if (!pick && !bestDiscard) return null;
  if (!pick) return makeDiscardV2(state, bestDiscard, pickScore);
  if (!bestDiscard) return makePickV2(pick, null, pickDamage);

  if (bestDiscard.net > pickNet + EV_TIE_EPSILON) {
    return makeDiscardV2(state, bestDiscard, pickScore);
  }
  return makePickV2(pick, bestDiscard, pickDamage);
}



// ---------- fast policy (rollout base) ----------
//
// v2 enumerates the whole deck for every candidate discard. That is fine for
// a single suggestion but far too slow to use as the inner policy of a
// rollout search. This is the same idea without the enumeration:
//
//   pick the highest-net hand if that net clears a bar, otherwise throw the
//   card with the least remaining potential.
//
// The bar falls as the deck empties: early on a 40-point hand is not worth
// three cards, on the last round it is everything we are going to get.
const FAST_BAR = 62;

function suggestMoveFast(state, options = {}) {
  const lambda = options.lambda ?? DEFAULT_LAMBDA;
  const bar = options.bar ?? FAST_BAR;
  const board = state.board;
  const filledIndices = [];
  for (let i = 0; i < board.length; i++) if (board[i]) filledIndices.push(i);
  if (filledIndices.length === 0) return null;

  const deck = deckRemaining(state);
  const available = makeAvailableSet(deck, board);
  const potential = {};
  for (const i of filledIndices) potential[i] = potentialOf(board[i], available);

  const rounds = Math.floor((deck.length + filledIndices.length) / 3);
  const scale = Math.max(0, Math.min(1, (rounds - 1) / 2));

  const ranked = rankCombos(board);
  let pick = null, pickNet = -Infinity;
  for (const cand of ranked) {
    if (cand.score <= 0) continue;
    const avgPot = cand.slots.reduce((a, sl) => a + potential[sl], 0) / 3;
    const net = cand.score - lambda * scale * Math.max(0, avgPot - cand.score);
    if (net > pickNet) { pickNet = net; pick = cand; }
  }

  // Bar scales with how much game is left: no rounds left to build anything
  // means take what is on the table.
  const effectiveBar = bar * scale;
  if (pick && (pickNet >= effectiveBar || deck.length === 0)) {
    return { kind: "pick", slots: pick.slots, cards: pick.cards, score: pick.score,
      type: pick.type, label: pick.label, reasoning: `Pick ${formatHandLabel(pick)} for ${pick.score} pts.` };
  }
  if (deck.length === 0) return pick ? { kind: "pick", slots: pick.slots, cards: pick.cards,
    score: pick.score, type: pick.type, label: pick.label, reasoning: "Deck is empty — take the best hand left." } : null;

  let worst = filledIndices[0];
  for (const i of filledIndices) if (potential[i] < potential[worst]) worst = i;
  return { kind: "discard", slots: [worst], cards: [board[worst]], expectedAfter: 0,
    reasoning: `Discard ${prettyCard(board[worst])} — least useful card left on the field.` };
}

// ---------- final round: play the threshold, not the average ----------
//
// Chests are thresholds, not points. With one pick left, a move that adds 30
// points is worthless at 250 (still bronze) and decisive at 280. So on the
// last round we stop maximising expected points and maximise
// P(reach the next chest) instead, tie-broken by P(reach the one above) and
// then by expected points.
//
// Target: silver while we are below it, gold once silver is banked.
function chestTarget(score) {
  return score < CHEST_THRESHOLDS.silver ? CHEST_THRESHOLDS.silver : CHEST_THRESHOLDS.gold;
}

// Distribution of the best pick available after discarding `slot` and drawing
// one card: exact, since every remaining deck card is equally likely.
function drawStats(board, slot, deck, target, above) {
  if (deck.length === 0) return null;
  const keep = [];
  for (let i = 0; i < board.length; i++) if (board[i] && i !== slot) keep.push(board[i]);
  let hit = 0, hitAbove = 0, sum = 0;
  for (const card of deck) {
    const newBoard = [...keep, card];
    while (newBoard.length < BOARD_SIZE) newBoard.push(null);
    const best = bestPickScore(newBoard);
    if (best >= target) hit++;
    if (best >= above) hitAbove++;
    sum += best;
  }
  return { p: hit / deck.length, pAbove: hitAbove / deck.length, ev: sum / deck.length };
}

function finalRoundMove(state, board, deck, filledIndices) {
  const pick = bestPick(board);
  if (!pick) return null;
  const target = chestTarget(state.score);
  const need = target - state.score;
  const above = CHEST_THRESHOLDS.gold - state.score;

  // Already good enough? Bank it — no reason to gamble the chest away.
  if (pick.score >= need) return makePickV2(pick, null, 0);

  const pickStats = { p: 0, pAbove: 0, ev: pick.score };
  let best = { stats: pickStats, move: null };
  for (const slot of filledIndices) {
    const stats = drawStats(board, slot, deck, need, above);
    if (!stats) continue;
    const b = best.stats;
    const better = stats.p > b.p + 1e-9 ||
      (Math.abs(stats.p - b.p) <= 1e-9 && stats.pAbove > b.pAbove + 1e-9) ||
      (Math.abs(stats.p - b.p) <= 1e-9 && Math.abs(stats.pAbove - b.pAbove) <= 1e-9 && stats.ev > b.ev);
    if (better) best = { stats, move: { slots: [slot], expectedAfter: stats.ev, cost: 0 } };
  }

  // Same rule in the final round, and null-safe: bestPick() returns null on a
  // board with fewer than three cards, and makePickV2 would dereference it.
  if (!best.move) return pick && pick.score > 0 ? makePickV2(pick, null, 0) : null;
  const card = board[best.move.slots[0]];
  const chest = target === CHEST_THRESHOLDS.gold ? "gold" : "silver";
  return {
    kind: "discard",
    slots: best.move.slots,
    cards: [card],
    expectedAfter: best.stats.ev,
    reasoning: `Last round: picking now scores ${pick.score}, but you need ${need} for ${chest}. Discard ${prettyCard(card)} — that gives a ${(best.stats.p * 100).toFixed(0)}% chance of drawing into a big enough combo (E[${best.stats.ev.toFixed(1)}]).`,
  };
}

function makePickV2(pick, bestDiscard, pickDamage) {
  let note = "";
  if (pickDamage > 0.5) {
    note = ` These cards could still be worth more elsewhere (spend-cost ≈ ${pickDamage.toFixed(0)}), but nothing better is reachable.`;
  }
  if (bestDiscard && bestDiscard.expectedAfter > pick.score) {
    note += ` (One discard would yield E[${bestDiscard.expectedAfter.toFixed(1)}], but that card is worth ≈ ${bestDiscard.cost.toFixed(1)} to future combos.)`;
  }
  const reasoning = `Pick ${formatHandLabel(pick)} for ${pick.score} pts.${note}`;
  return {
    kind: "pick",
    slots: pick.slots,
    cards: pick.cards,
    score: pick.score,
    type: pick.type,
    label: pick.label,
    reasoning,
  };
}

function makeDiscardV2(state, bestDiscard, pickScore) {
  const slot = bestDiscard.slots[0];
  const card = state.board[slot];
  const compare = pickScore > 0 ? ` (best pick now: ${pickScore} pts)` : ` (no scoring combo on the field)`;
  const reasoning = `Discard ${prettyCard(card)} — nothing alive needs it (worth ≈ ${bestDiscard.cost.toFixed(1)}), and the redraw is worth E[${bestDiscard.expectedAfter.toFixed(1)}]${compare}.`;
  return {
    kind: "discard",
    slots: bestDiscard.slots,
    cards: [card],
    expectedAfter: bestDiscard.expectedAfter,
    reasoning,
  };
}

function suggestMoveV1(state, options = {}) {
  const opportunityCost = options.opportunityCost ?? OPPORTUNITY_COST_PER_DISCARD;
  const board = state.board;
  const filledIndices = [];
  for (let i = 0; i < board.length; i++) if (board[i]) filledIndices.push(i);
  if (filledIndices.length === 0) return null;

  const pick = bestPick(board);
  const pickScore = pick ? pick.score : 0;
  const deck = deckRemaining(state);

  // Best single-card discard: for each filled slot, expected best-pick score
  // after replacing that one card with a random draw from deckRemaining.
  let bestSingle = null;
  for (const slot of filledIndices) {
    const ev = expectedScoreAfterDiscard(board, [slot], deck);
    if (ev === null) continue;
    if (bestSingle === null || ev > bestSingle.expectedAfter) {
      bestSingle = { slots: [slot], expectedAfter: ev };
    }
  }

  const canPick = pick !== null;
  const canDiscard = bestSingle !== null;

  if (!canPick && !canDiscard) return null;
  if (!canPick) return makeDiscard(state, bestSingle, pickScore);
  if (!canDiscard) return makePick(pick, bestSingle, opportunityCost);

  // Discard wins only if its EV beats picking by at least the opportunity
  // cost of the card it burns (see comment at OPPORTUNITY_COST_PER_DISCARD).
  // Ties go to picking so the helper doesn't churn when the two are close.
  if (bestSingle.expectedAfter > pickScore + opportunityCost + EV_TIE_EPSILON) {
    return makeDiscard(state, bestSingle, pickScore);
  }
  return makePick(pick, bestSingle, opportunityCost);
}

function makePick(pick, bestSingle, opportunityCost = OPPORTUNITY_COST_PER_DISCARD) {
  // If a single discard had higher raw EV but lost out to the opportunity
  // cost, surface that — otherwise the user might think the solver missed it.
  let evNote = "";
  if (bestSingle) {
    const adj = bestSingle.expectedAfter - opportunityCost;
    if (bestSingle.expectedAfter > pick.score) {
      evNote = ` (one discard would yield E[${bestSingle.expectedAfter.toFixed(1)}], but with deck-burn cost ≈ ${opportunityCost} that's only ${adj.toFixed(1)} net).`;
    }
  }
  const reasoning = `Pick ${formatHandLabel(pick)} for ${pick.score} pts.${evNote}`;
  return {
    kind: "pick",
    slots: pick.slots,
    cards: pick.cards,
    score: pick.score,
    type: pick.type,
    label: pick.label,
    reasoning,
  };
}

function makeDiscard(state, bestSingle, pickScore) {
  const board = state.board;
  const slot = bestSingle.slots[0];
  const card = board[slot];
  const ev = bestSingle.expectedAfter.toFixed(1);
  const compare = pickScore > 0
    ? ` (best pick now: ${pickScore} pts)`
    : ` (no scoring combo on the field)`;
  const reasoning = `Discard ${prettyCard(card)} — E[best pick after draw] ≈ ${ev}${compare}. After you enter the new card, the helper will re-evaluate.`;
  return {
    kind: "discard",
    slots: bestSingle.slots,
    cards: [card],
    expectedAfter: bestSingle.expectedAfter,
    reasoning,
  };
}

// ---------- formatting helpers ----------

const TYPE_LABEL = {
  three: "three of a kind",
  sameSeq: "same-color run",
  mixedSeq: "mixed run",
  none: "no combo",
};

function formatHandLabel(combo) {
  const cardStr = combo.cards.map(prettyCard).join(" · ");
  const typeStr = TYPE_LABEL[combo.type] || "—";
  return `${cardStr} — ${typeStr}`;
}

function prettyCard(id) {
  const color = COLOR_NAMES[id[0]] || id[0];
  return `${color[0]}${id.slice(1)}`;
}


// ===== rollout.js =====
// Policy rollout with a chest objective.
//
// Everything up to v2 maximises expected points. Chests are thresholds: at 250
// with one round left, +30 points is worth nothing (still bronze) while at 280
// the same +30 is the whole game. The only way to price that correctly is to
// ask, for each candidate move, "how often does this end in silver/gold?"
//
// Method (Tesauro & Galperin policy rollout): apply the candidate move, then
// let the v2 heuristic play the rest against a randomly ordered deck, N times.
// Rank candidates by P(>=silver), tie-broken by P(>=gold), then mean score.
//
// Variance reduction: all candidates are evaluated against the SAME N deck
// orders (common random numbers), so the comparison between them is paired and
// N can stay small enough for the browser.

// Playouts per candidate.
//
// Was 24, and that number was a latency budget rather than a quality finding:
// the search used to run inside the click handler, so it could not cost more.
// It no longer runs there at all — it runs in a worker thread (search-worker.js)
// — and the 2026-09-09 overnight campaign measured what the extra playouts are
// worth on fresh seeds, against the same decks:
//
//   N=24 (was shipping)   64.4% silver-or-better, 6.0% gold
//   N=64 + halving        69.4%                   6.8%
//   N=96 + halving        70.6%                   7.3%
//
// Both chests improve together, which is what makes this different from the
// noise-band attempt of the day before: that one bought silver by giving up
// gold and was rolled back for it. The gain is monotone in N up to here, and
// N=96 is where the curve is flat enough that another doubling is not worth
// the memory churn.
//
// Cost, measured single-process: ~146 ms per decision (p90 299 ms, worst 415 ms)
// against ~41 ms before — all of it in the worker, none of it in front of a
// click. The instant heuristic answer is still what paints first.
// 2026-09-16: raised 96 -> 160 after the scoring/deck optimisations made it
// CHEAPER than the old 96. Measured on an idle machine, p90 per decision:
//
//   old code, N=96    311 ms   <- what shipped until today
//   new code, N=160   280 ms   <- what ships now
//   new code, N=240   360 ms   <- better rate still, but above the old lag
//
// Rate on fresh seeds 2-4, 6000 games: silver+ 70.6% -> 71.6%, gold 7.5% ->
// 8.0%. Neither difference is individually significant (z = 1.13 / 0.96); what
// carries it is that the gain is monotone in N across 96/160/240 and the sign
// is the same on all three seeds. N=240 is the better player and is left on the
// table deliberately: it costs more lag than the config it replaces.
const DEFAULT_N = 160;

// Options for the heuristic that finishes each playout. Contributed by Flavius
// (flaviusrzv/metin2-okey-helper) and measured here, not adopted on faith:
// type-aware pick damage, residual synergy, lambda 10.
//
// NB this is the PLAYOUT heuristic only. The instant provisional answer the UI
// paints first still runs plain v2 (lambda 6) — that is exactly the combination
// the benchmark measured, so it is exactly the combination that ships.
//
// Worth knowing before tuning further: at N=96 this heuristic is worth nothing
// measurable (+0.22pp silver+, z=0.26). It only starts paying once there are
// enough playouts to carry it, which is why it must never be tuned at low N.
const DEFAULT_BASE = { lambda: 10, typeAware: true, residualWeight: 1.0 };

// Where a rollout stops guessing and starts knowing. Below this many cards in
// play the exact solver evaluates the position outright, so a playout no
// longer has to be finished by the v2 heuristic — which only reaches ~46%
// silver on its own and therefore colours every estimate it produces.
//
// A second benefit is variance: an exact leaf returns a PROBABILITY (0.62),
// not a coin flip (0 or 1), so the same N of playouts carries far more
// information.
// Off. A 120-game A/B once favoured leaf=8, but the overnight search varied it
// TOGETHER with N over 5000 games each and the advantage disappeared: at equal
// N the leaf variants land on the same numbers as leaf=0, and the time it
// costs buys more silver when spent on rollouts instead. A good example of why
// knobs tuned one at a time mislead. Kept switchable for future measurement.
const DEFAULT_EXACT_LEAF = 0;
const MAX_PICK_CANDIDATES = 3;

// What "best" means. Chests are worth different amounts to the player, and
// that changes the play: chasing gold means passing up safe silver.
//   "silver"   lexicographic P(silver) -> P(gold) -> mean  (safest chest)
//   "balanced" maximise P(silver) + 2 * P(gold)            (gold counts triple,
//                                                          since gold implies
//                                                          silver)
//   "gold"     lexicographic P(gold) -> P(silver) -> mean  (gold hunting)
// //   "points"   plain expected score (for comparison)
//   "auto"     what the helper actually ships with: hunt gold while gold is
//              still on, fall back to locking in silver once it is not. No
//              setting for the player to get wrong.
//
// Each objective is the list of keys to rank by, in order, most important
// first. "balanced" ranks on a derived key (pSilver + 2 * pGold) computed per
// playout, so it goes through the same machinery as the rest.
const OBJECTIVES = {
  silver: ["pSilver", "pGold", "mean"],
  balanced: ["balanced", "mean"],
  gold: ["pGold", "pSilver", "mean"],
  points: ["mean"],
};

// Noise band on the ranking keys, in standard errors of the PAIRED difference
// between two candidates (the playouts share deck orders, so the pairing is
// valid). A candidate that is not separated from the leader by more than the
// band stays in the running and is decided by the next key.
//
// OFF BY DEFAULT, and that is deliberate: with the band on every key, a
// 2026-09-08 A/B over 800 paired games moved silver-or-better from 65.8% to
// 68.9% but gold from 6.5% down to 5.4%. Losing gold is the wrong trade to make
// silently — gold is what the player is actually playing for once it is in
// reach — so the band ships off until a setting is measured that keeps both.
//
// Per-key values are allowed: { pSilver: 1, pGold: 0 } bands the safety key but
// never the gold key, which is the variant under test. A plain number applies
// to every key.
const DEFAULT_TIE_Z = 0;

function tieZFor(tieZ, key) {
  if (tieZ == null) return 0;
  if (typeof tieZ === "number") return tieZ;
  return tieZ[key] ?? 0;
}

// How the playout budget is spread over the candidate moves.
//
//   "flat"    every candidate gets N playouts. Simple, and what has always
//             shipped — but on a five-card field with a full deck there are
//             usually 6-8 candidates, and most of them are not close: throwing
//             the one card that carries the whole run scores 0% in every
//             playout, and it costs exactly as much to establish that as it
//             costs to separate the two moves that are actually competing.
//   "halving" sequential halving. Same total playouts, spent in rounds: every
//             survivor is measured, the worse half is dropped, the budget moves
//             to the rest. The two real candidates end up with several times
//             the playouts they get now, at identical cost.
//
// "halving" ships: same total playouts, spent in rounds so the candidates that
// are actually competing get several times the resolution. Worth +0.7pp silver
// over flat at N=96 and slightly FASTER (146 ms vs 152 ms), because candidates
// that are settled stop being paid for.
//
// It needs the budget to be worth having: at N=24 halving measured WORSE than
// flat (62.1% against 65.2%) — splitting a small budget into rounds leaves too
// few playouts per round to drop the right half. Do not enable it without N.
const DEFAULT_ALLOCATE = "halving";

// "Gold is still on" has two readings, and they play very differently:
//
//   feasible — arithmetically still possible (score + best remaining >= 400).
//              Stays true almost to the end, so this hunts gold all game.
//   likely   — some candidate move still reaches gold in at least
//              AUTO_GOLD_MIN of its rollouts. Gives up on gold earlier and
//              banks silver instead.
//
// Both are measured in bench/benchmark.mjs; the default is set from that.
const AUTO_GOLD_MIN = 0.10;

function autoWantsGold(state, all, mode, goldMin = AUTO_GOLD_MIN) {
  if (mode === "feasible") {
    const deck = deckRemaining(state);
    let filled = 0;
    for (const c of state.board) if (c) filled++;
    const rounds = Math.floor((deck.length + filled) / 3);
    const ceiling = bestAchievable(makeAvailableSet(deck, state.board), rounds);
    return state.score + ceiling >= CHEST_THRESHOLDS.gold;
  }
  for (const entry of all) if (entry.stats.pGold >= goldMin) return true;
  return false;
}

function makeRng(seed) {
  let a = seed >>> 0;
  return function () {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function cloneState(state) {
  return {
    board: [...state.board],
    score: state.score,
    consumed: new Set(state.consumed),
    history: [],
    log: [],
  };
}

// Candidate moves: every scoring pick plus every single discard. Non-scoring
// picks are never worth considering while a discard is possible.
function candidates(state) {
  const out = [];
  let picks = 0;
  for (const combo of rankCombos(state.board)) {
    // rankCombos is sorted by score; the 4th-best hand on a 5-card board is
    // never the right pick, and each extra candidate costs N playouts.
    if (combo.score > 0 && picks++ < MAX_PICK_CANDIDATES) {
      out.push({ kind: "pick", slots: combo.slots, cards: combo.cards, combo });
    }
  }
  if (deckRemaining(state).length > 0) {
    for (let i = 0; i < state.board.length; i++) {
      if (state.board[i]) out.push({ kind: "discard", slots: [i], cards: [state.board[i]] });
    }
  }
  return out;
}

function applyMove(state, move) {
  if (move.kind === "pick") confirmPick(state, move.slots);
  else discardSlot(state, move.slots[0]);
}

// Play forward with the base policy until the position is small enough to
// evaluate exactly, then hand it to the solver. Returns chest probabilities
// and an expected final score.
//
// E[score] comes out of the value curve for free: for a non-negative variable
// on a 10-point grid, E[X] = 10 * sum over t>=1 of P(X >= t).
function playout(state, rand, baseOptions, ctx) {
  let safety = 60;
  while (safety-- > 0) {
    autoFillBoardFromDeck(state, rand);
    const filled = filledCards(state);
    if (filled.length < 3) break;

    const deck = deckRemaining(state);
    if (ctx && ctx.solver && deck.length + filled.length <= ctx.exactLeaf) {
      const curve = ctx.solver.value(maskOf([...deck, ...filled]), maskOf(filled));
      const at = (need) => {
        const i = Math.ceil(Math.max(0, need) / 10);
        return i <= 0 ? 1 : (i < curve.length ? curve[i] : 0);
      };
      let ev = 0;
      for (let t = 1; t < curve.length; t++) ev += curve[t] * 10;
      return {
        pSilver: at(CHEST_THRESHOLDS.silver - state.score),
        pGold: at(CHEST_THRESHOLDS.gold - state.score),
        mean: state.score + ev,
      };
    }

    const move = suggestMove(state, baseOptions);
    if (!move) break;
    if (move.kind === "discard") {
      if (deck.length === 0) break;
      discardSlot(state, move.slots[0]);
    } else {
      confirmPick(state, move.slots);
    }
  }
  return {
    pSilver: state.score >= CHEST_THRESHOLDS.silver ? 1 : 0,
    pGold: state.score >= CHEST_THRESHOLDS.gold ? 1 : 0,
    mean: state.score,
  };
}

function suggestMoveRollout(state, options = {}) {
  const N = options.N ?? DEFAULT_N;
  const baseOptions = options.base ?? DEFAULT_BASE;
  const moves = candidates(state);
  if (moves.length === 0) return null;
  if (moves.length === 1) return decorate(state, moves[0], null);

  // Common random numbers: one fixed seed per playout index, reused by every
  // candidate, so differences between candidates are not draw luck.
  const seeds = [];
  for (let i = 0; i < N; i++) seeds.push((options.seed ?? 0x9E3779B9) + i * 0x85EBCA6B);

  const objective = options.objective ?? "auto";

  // One exact-solver table for the whole decision: the leaf positions of every
  // playout are sub-positions of the same card set, so they share heavily and
  // only the first few cost anything.
  const exactLeaf = options.exactLeaf ?? DEFAULT_EXACT_LEAF;
  let ctx = null;
  if (exactLeaf > 0) {
    const solver = new EndgameSolver({ nodeLimit: options.leafNodeLimit ?? 2e6 });
    solver.prepare(maskOf([...deckRemaining(state), ...state.board.filter(Boolean)]));
    ctx = { solver, exactLeaf };
  }

  // Total playouts to spend on this decision. Both allocation strategies get
  // the same budget, so "halving" is free: it only moves playouts from
  // candidates that are already settled onto the ones still competing.
  const budget = N * moves.length;
  const allocate = options.allocate ?? DEFAULT_ALLOCATE;

  // Per-playout results are kept, not only their averages: the band compares
  // candidates playout by playout, which is only meaningful because they share
  // deck orders. Capacity is the whole budget because under halving a single
  // survivor can end up with far more than N.
  const all = moves.map((move) => ({
    move,
    n: 0,
    sums: { pSilver: 0, pGold: 0, mean: 0 },
    samples: {
      pSilver: new Float64Array(budget),
      pGold: new Float64Array(budget),
      mean: new Float64Array(budget),
      balanced: new Float64Array(budget),
    },
    stats: null,
  }));

  // Playout i of every candidate uses seed i — that is what makes the
  // comparison paired, and it holds under halving too: two candidates with
  // different counts still share the whole shorter prefix.
  const seedAt = (i) => (options.seed ?? 0x9E3779B9) + i * 0x85EBCA6B;

  const extend = (entry, upTo) => {
    for (let i = entry.n; i < upTo; i++) {
      const s = cloneState(state);
      applyMove(s, entry.move);
      const r = playout(s, makeRng(seedAt(i)), baseOptions, ctx);
      entry.samples.pSilver[i] = r.pSilver;
      entry.samples.pGold[i] = r.pGold;
      entry.samples.mean[i] = r.mean;
      entry.samples.balanced[i] = r.pSilver + 2 * r.pGold;
      entry.sums.pSilver += r.pSilver;
      entry.sums.pGold += r.pGold;
      entry.sums.mean += r.mean;
    }
    entry.n = Math.max(entry.n, upTo);
    entry.stats = {
      pSilver: entry.sums.pSilver / entry.n,
      pGold: entry.sums.pGold / entry.n,
      mean: entry.sums.mean / entry.n,
      balanced: (entry.sums.pSilver + 2 * entry.sums.pGold) / entry.n,
    };
  };

  // The objective needs stats to decide (autoWantsGold reads every candidate's
  // gold rate), so under halving it is fixed after the first round and kept —
  // switching objectives mid-search would compare arms measured under different
  // targets.
  let keys = null;
  const chooseKeys = () => {
    if (keys) return keys;
    keys = objective === "auto"
      ? (autoWantsGold(state, all, options.autoMode ?? "likely", options.goldMin ?? AUTO_GOLD_MIN)
          ? OBJECTIVES.gold : OBJECTIVES.silver)
      : (OBJECTIVES[objective] ?? OBJECTIVES.silver);
    return keys;
  };

  let pool = all;
  if (allocate === "halving" && moves.length > 2) {
    const rounds = Math.ceil(Math.log2(moves.length));
    let spent = 0;
    for (let r = 0; r < rounds && pool.length > 1; r++) {
      // What is left, split evenly over the rounds that remain.
      const perArm = Math.max(1, Math.floor((budget - spent) / ((rounds - r) * pool.length)));
      for (const e of pool) {
        const before = e.n;
        extend(e, e.n + perArm);
        spent += e.n - before;
      }
      chooseKeys();
      // Drop the worse half on the primary key alone — that is the point of the
      // method: a cheap, noisy verdict is enough to stop paying for a candidate
      // that is not in the running.
      const key = keys[0];
      const sorted = [...pool].sort((a, b) => b.stats[key] - a.stats[key]);
      pool = sorted.slice(0, Math.max(1, Math.ceil(sorted.length / 2)));
    }
    // Anything the rounds left unspent goes to the finalists.
    if (pool.length > 1 && spent < budget) {
      const perArm = Math.floor((budget - spent) / pool.length);
      if (perArm > 0) for (const e of pool) extend(e, e.n + perArm);
    }
  } else {
    for (const e of all) extend(e, N);
  }

  const best = pickBest(pool, chooseKeys(), options.tieZ ?? DEFAULT_TIE_Z);
  // `all` still carries every candidate, including the ones dropped early —
  // their stats are simply based on fewer playouts.
  return decorate(state, best.move, best.stats, all, N);
}

// Rank by the objective's keys in order, keeping whatever a key cannot
// separate for the next key to decide.
//
// With every band at 0 this is plain lexicographic ranking with a 1e-9
// tolerance — the same answer the old comparison gave, candidate order breaking
// a perfect tie — so the switch is genuinely off when it is off.
function pickBest(all, keys, tieZ) {
  let pool = all;
  for (let k = 0; k < keys.length; k++) {
    const key = keys[k];
    let lead = pool[0];
    for (const e of pool) if (e.stats[key] > lead.stats[key] + 1e-9) lead = e;
    // The last key decides outright — there is nothing left to defer to.
    if (k === keys.length - 1 || pool.length === 1) return lead;
    const z = tieZFor(tieZ, key);
    const next = pool.filter((e) => e === lead || tied(lead, e, key, z));
    if (next.length === 1) return next[0];
    pool = next;
  }
  return pool[0];
}

// Is the gap between two candidates on this key smaller than the noise in the
// estimate of that gap?
//
// Paired, because both candidates played the same deck orders: the per-playout
// difference is what carries the signal, and its spread is far smaller than the
// spread of either candidate on its own.
function tied(lead, other, key, z) {
  const gap = lead.stats[key] - other.stats[key];
  if (z <= 0) return gap <= 1e-9;
  if (gap <= 1e-9) return true;
  // Under halving the two candidates may have different playout counts; the
  // shared prefix is the part that is actually paired, so the test uses that
  // and nothing else.
  const n = Math.min(lead.n, other.n);
  if (n < 2) return false;
  const a = lead.samples[key], b = other.samples[key];
  let sum = 0;
  for (let i = 0; i < n; i++) sum += a[i] - b[i];
  const meanDiff = sum / n;
  if (meanDiff <= 1e-9) return true;
  let sq = 0;
  for (let i = 0; i < n; i++) { const d = (a[i] - b[i]) - meanDiff; sq += d * d; }
  const se = Math.sqrt(sq / (n - 1) / n);
  return meanDiff <= z * se;
}

function decorate(state, move, stats, all, N) {
  const pct = (x) => Math.round(x * 100) + "%";
  const tail = stats
    ? ` P(silver)=${pct(stats.pSilver)} · P(gold)=${pct(stats.pGold)} · E[final]≈${Math.round(stats.mean)} (${N} rollouts)`
    : "";
  if (move.kind === "pick") {
    const c = move.combo;
    return {
      kind: "pick", slots: move.slots, cards: move.cards, score: c.score,
      type: c.type, label: c.label,
      reasoning: `Pick ${c.label} for ${c.score} pts.${tail}`,
      rollout: { stats, all },
    };
  }
  return {
    kind: "discard", slots: move.slots, cards: move.cards,
    expectedAfter: stats ? stats.mean : 0,
    reasoning: `Discard ${move.cards[0]}.${tail}`,
    rollout: { stats, all },
  };
}


// ===== policy.js =====
// The helper's single entry point: use the strongest method the position can
// afford.
//
//   <= EXACT_MAX_CARDS cards left  ->  exact solve (endgame.js). Optimal play,
//                                      no approximation, both chests priced
//                                      off the same value curve.
//   more than that                 ->  policy rollout (rollout.js) over the
//                                      v2 heuristic.
//
// The cutoff is a time budget, not a quality judgement. Exact solving costs
// ~2.8x per extra card still in play (measured in bench/endgame-timing.mjs):
// 12 cards is ~200 ms, 13 is ~630 ms, 16 is 22 s. Twelve keeps every
// suggestion under a fifth of a second.
//
// In a normal game (about 4 picks and 11 discards) the exact phase begins
// around the seventh action, so it covers every decision that actually settles
// which chest you end up with.

const EXACT_MAX_CARDS = 13;

// Per-game scratchpad. The exact solver's table stays valid for the rest of a
// game — every later position is a sub-position of the first one solved — so
// reusing it makes the closing turns nearly free.
function createPolicyCache() {
  return { solver: null };
}

function exactSuggestion(state, deck, cache) {
  const boardCards = state.board.filter(Boolean);
  const available = maskOf([...deck, ...boardCards]);
  const board = maskOf(boardCards);

  let solver = cache && cache.solver;
  if (!solver) {
    solver = new EndgameSolver();
    solver.prepare(available);
    if (cache) cache.solver = solver;
  }

  const best = solver.bestMoveChest(
    available,
    board,
    CHEST_THRESHOLDS.silver - state.score,
    CHEST_THRESHOLDS.gold - state.score,
    true,
  );
  if (!best) return null;

  // Map card ids back to the slots the UI works in.
  const slots = best.cards.map((id) => state.board.indexOf(id));
  if (slots.some((s) => s < 0)) return null;

  const pct = (x) => Math.round(x * 100) + "%";
  const odds = `Silver ${pct(best.pSilver)} · gold ${pct(best.pGold)} — exact, not an estimate.`;
  if (best.kind === "pick") {
    // type/label so an exact suggestion is shaped exactly like a heuristic one.
    const { type, label } = scoreHand(best.cards);
    return {
      kind: "pick",
      slots,
      cards: best.cards,
      score: best.gained,
      type,
      label,
      exact: best,
      reasoning: `Pick ${label} for ${best.gained} pts. ${odds}`,
    };
  }
  return {
    kind: "discard",
    slots,
    cards: best.cards,
    expectedAfter: 0,
    exact: best,
    reasoning: `Discard ${best.cards[0]}. ${odds}`,
  };
}

// Is a better chest still reachable at all?
//
// Two ways to answer, and we take the sharper one available:
//
//   exact    — with few enough cards left, the value curve says it outright:
//              the highest threshold with a non-zero probability IS the most
//              that can still be scored.
//   optimistic — otherwise, pack the best disjoint combos still alive into the
//              rounds still available. That ignores the 5-slot window, so it
//              over-estimates — which is the safe direction here: we only ever
//              call a run finished when even the optimistic bound falls short.
//
// Returns { canImprove, maxRemaining, nextThreshold, exact }.
function chestOutlook(state, options = {}) {
  const deck = deckRemaining(state);
  const boardCards = state.board.filter(Boolean);
  const cardsInPlay = deck.length + boardCards.length;
  const score = state.score;

  const nextThreshold =
    score < CHEST_THRESHOLDS.silver ? CHEST_THRESHOLDS.silver
    : score < CHEST_THRESHOLDS.gold ? CHEST_THRESHOLDS.gold
    : null; // already gold — nothing better exists

  if (nextThreshold === null) {
    return { canImprove: false, maxRemaining: 0, nextThreshold: null, exact: true };
  }

  // Slots the player has not typed in yet are cards the game has already
  // dealt — they are not a smaller field. Ask the solver for the position
  // AFTER those slots are filled, or a hand that needs all five slots at once
  // reads as unreachable and the run gets called finished while it isn't.
  const missing = Math.min(BOARD_SIZE - boardCards.length, deck.length);

  let maxRemaining = null;
  let exact = false;
  if (boardCards.length + missing >= 3 && cardsInPlay <= (options.exactMaxCards ?? EXACT_MAX_CARDS)) {
    try {
      const available = maskOf([...deck, ...boardCards]);
      const board = maskOf(boardCards);
      let solver = options.cache && options.cache.solver;
      if (!solver) {
        solver = new EndgameSolver();
        solver.prepare(available);
        if (options.cache) options.cache.solver = solver;
      }
      const curve = solver.valueAfterFill(available, board, missing);
      let top = 0;
      for (let i = curve.length - 1; i >= 0; i--) {
        if (curve[i] > 0) { top = i; break; }
      }
      maxRemaining = top * 10;
      exact = true;
    } catch (e) {
      if (!(e instanceof RangeError)) throw e;
    }
  }
  if (maxRemaining === null) {
    const rounds = Math.floor(cardsInPlay / 3);
    maxRemaining = bestAchievable(makeAvailableSet(deck, state.board), rounds);
  }

  return {
    canImprove: score + maxRemaining >= nextThreshold,
    maxRemaining,
    nextThreshold,
    exact,
  };
}

// options.cache — pass a createPolicyCache() per game to keep the exact table.
// options.mode — "auto" (default), "exact", "rollout", "heuristic".
function suggest(state, options = {}) {
  const deck = deckRemaining(state);
  const boardCards = state.board.filter(Boolean);
  if (boardCards.length === 0) return null;
  const cardsInPlay = deck.length + boardCards.length;
  const mode = options.mode ?? "auto";

  // Nothing to search while the field is still being filled in: with fewer
  // than 3 cards there is no hand to take, so the only advice is which card to
  // throw. The cheap heuristic answers that in 0.1 ms and keeps card entry
  // from feeling sticky.
  if (mode === "auto" && boardCards.length < 3) return suggestMove(state, options);

  if (mode === "heuristic") return suggestMove(state, options);
  if (mode === "rollout") return suggestMoveRollout(state, options);

  if (mode === "exact" || cardsInPlay <= (options.exactMaxCards ?? EXACT_MAX_CARDS)) {
    try {
      const exact = exactSuggestion(state, deck, options.cache);
      if (exact) return exact;
    } catch (e) {
      // Only a blown node limit falls through to the cheaper method.
      if (!(e instanceof RangeError)) throw e;
    }
  }
  return suggestMoveRollout(state, options);
}


g.OkeyEngine = {
  suggest, createPolicyCache, chestOutlook,
  createState, addCard, discardSlot, confirmPick, undo, resetState,
  deckRemaining, chestForScore, scoreHand, firstEmptySlot
};
})(window);
