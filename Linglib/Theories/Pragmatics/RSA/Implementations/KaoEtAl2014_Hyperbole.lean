import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Linglib.Theories.Semantics.Lexical.Numeral.Precision

/-!
# Kao et al. (2014) @cite{kao-etal-2014-hyperbole}

"Nonliteral understanding of number words"
PNAS 111(33): 12002-12007

## The Model

The key insight is that speakers may use literally false utterances to convey
*affective* information when the listener is uncertain about the speaker's
communicative goal.

Meaning space: PriceState × Affect
- PriceState: S = {50, 51, 500, 501, 1000, 1001, 5000, 5001, 10000, 10001}
- Affect: A = {0, 1} (binary: no affect / with affect)
- Utterances: U = S (the speaker can say any price)

The speaker S1 optimizes informativity w.r.t. a projected meaning under
a communicative goal g, following:

    S1(u|s,a,g) ∝ exp(α · [ln L0(g(s,a)|u) - C(u)])           [Eq. 5,7]

where g composes a precision projection f (exact vs approximate) with a
relevance projection r (price, affect, or both), yielding 5 distinct goals.

L0 is purely literal (Eq. 9):

    L0(s,a|u) = P_A(a|s) if s = u, 0 otherwise

The pragmatic listener L1 marginalizes over goals (Eq. 10):

    L1(s,a|u) ∝ P_S(s) · P_A(a|s) · Σ_g P_G(g) · S1(u|s,a,g)

## Two phenomena derived

1. **Hyperbole**: "The kettle cost $10,000" when the true price is $50.
   Under the valence QUD, S1 can rationally choose a false price to
   communicate affect (expensive → annoyed).

2. **Pragmatic halo**: Round numbers ("500") are interpreted less precisely
   than sharp numbers ("501"). Driven by differential utterance cost:
   C(round) < C(sharp), fitted to data (best fit ratio 3.4).

## Grounding

Price semantics is grounded in the `HasDegree` typeclass. The literal
meaning of "fifty dollars" is `numeralExact 50 price` — the price equals $50.

## References

- Kao, Wu, Bergen & Goodman (2014). Nonliteral understanding of number words.
  PNAS 111(33): 12002-12007.
-/

namespace RSA.KaoEtAl2014_Hyperbole

open Core.Scale (HasDegree)
open Semantics.Lexical.Numeral (MeasurePredicate DegreePhrase measureSentence numeralExact)
open Semantics.Lexical.Numeral.Precision (roundToNearest isRoundNumber)
open Real (exp log exp_pos)

-- ============================================================================
-- Domain Types
-- ============================================================================

/-- Item types from the paper (Experiments 3a/3b).

Three everyday items with distinct price distributions:
- Electric kettles: typically cheap ($50-$100)
- Laptops: moderate range ($500-$2000)
- Watches: highly variable ($50-$10000+)
-/
inductive Item where
  | electricKettle
  | laptop
  | watch
  deriving Repr, DecidableEq, BEq

/-- Price states S = {50, 51, 500, 501, 1000, 1001, 5000, 5001, 10000, 10001}.

Round/sharp pairs: each base price has a "sharp" neighbor (+1).
The round/sharp distinction drives pragmatic halo via differential
utterance cost. -/
inductive PriceState where
  | s50 | s51 | s500 | s501 | s1000 | s1001 | s5000 | s5001 | s10000 | s10001
  deriving Repr, DecidableEq, BEq

/-- Map PriceState to its numerical value. -/
def PriceState.value : PriceState → ℚ
  | .s50 => 50 | .s51 => 51
  | .s500 => 500 | .s501 => 501
  | .s1000 => 1000 | .s1001 => 1001
  | .s5000 => 5000 | .s5001 => 5001
  | .s10000 => 10000 | .s10001 => 10001

/-- PriceState implements HasDegree via its dollar value. -/
instance : HasDegree PriceState where
  degree := PriceState.value

/-- Affect: binary (0 = no affect, 1 = with affect).
The paper binarizes for simplicity (p. 12006). -/
inductive Affect where
  | none | notable
  deriving Repr, DecidableEq, BEq

/-- Full meaning: price state × affect. -/
abbrev World := PriceState × Affect

/-- Communicative goals.

The paper composes two projection types:
- Relevance: r_s (price), r_a (affect), r_{s,a} (both)
- Precision: f_e (exact), f_a (approximate = round)

This gives 3 × 2 = 6 combinations, but r_a ∘ f_e ≡ r_a ∘ f_a
(rounding doesn't affect affect), yielding 5 distinct goals. -/
inductive Goal where
  | price            -- r_s ∘ f_e: exact price only
  | valence          -- r_a: affect only
  | priceValence     -- r_{s,a} ∘ f_e: both exact price and affect
  | approxPrice      -- r_s ∘ f_a: approximate (rounded) price only
  | approxPriceValence -- r_{s,a} ∘ f_a: approximate price and affect
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Fintype Instances
-- ============================================================================

instance : Fintype PriceState where
  elems := {.s50, .s51, .s500, .s501, .s1000, .s1001, .s5000, .s5001, .s10000, .s10001}
  complete := fun x => by cases x <;> simp

instance : Fintype Affect where
  elems := {.none, .notable}
  complete := fun x => by cases x <;> simp

instance : Fintype Goal where
  elems := {.price, .valence, .priceValence, .approxPrice, .approxPriceValence}
  complete := fun x => by cases x <;> simp

instance : Fintype Item where
  elems := {.electricKettle, .laptop, .watch}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- Priors (Experiments 3a/3b)
-- ============================================================================

/-- Price prior P_S from Experiment 3a.

Item-parametric: different items have different typical price distributions.
These are crucial for hyperbole — "10,000 dollars" for a kettle is much more
likely to be hyperbolic than for a laptop.

Sharp variants get the same prior as their round neighbors (the paper
collapses round/sharp for hyperbole analysis). -/
def pricePrior (item : Item) : PriceState → ℝ
  | .s50 | .s51       => match item with | .electricKettle => 8 | .laptop => 1 | .watch => 3
  | .s500 | .s501      => match item with | .electricKettle => 2 | .laptop => 6 | .watch => 4
  | .s1000 | .s1001    => match item with | .electricKettle => 1 | .laptop => 4 | .watch => 3
  | .s5000 | .s5001    => match item with | .electricKettle => 1 | .laptop => 3 | .watch => 3
  | .s10000 | .s10001  => match item with | .electricKettle => 1 | .laptop => 2 | .watch => 3

/-- Affect prior P_A(a|s) from Experiment 3b.

The probability of having affect a given price state s.
Higher prices → more likely to think the item is too expensive.

The paper focuses on the affect of "too expensive" because hyperbole
is more commonly used for negative attitudes. -/
def affectPrior : PriceState → Affect → ℝ
  | .s50,    .none => 9   | .s50,    .notable => 1
  | .s51,    .none => 9   | .s51,    .notable => 1
  | .s500,   .none => 5   | .s500,   .notable => 5
  | .s501,   .none => 5   | .s501,   .notable => 5
  | .s1000,  .none => 3   | .s1000,  .notable => 7
  | .s1001,  .none => 3   | .s1001,  .notable => 7
  | .s5000,  .none => 2   | .s5000,  .notable => 8
  | .s5001,  .none => 2   | .s5001,  .notable => 8
  | .s10000, .none => 1   | .s10000, .notable => 9
  | .s10001, .none => 1   | .s10001, .notable => 9

-- ============================================================================
-- Utterance Cost
-- ============================================================================

/-- Whether a price state is a round number (divisible by 10). -/
def PriceState.isRound : PriceState → Bool
  | .s50 | .s500 | .s1000 | .s5000 | .s10000 => true
  | .s51 | .s501 | .s1001 | .s5001 | .s10001 => false

/-- Utterance cost C(u).

C(u) = 1 for round numbers. The sharp/round cost ratio is a free
parameter fitted to data; best fit is 3.4 (p. 12007).
So C(sharp) = 3.4, C(round) = 1. -/
noncomputable def cost : PriceState → ℝ
  | u => if u.isRound then 1 else (17 : ℝ) / 5  -- 3.4 = 17/5

-- ============================================================================
-- Compositional Literal Semantics
-- ============================================================================

/-!
## Deriving "The X cost u dollars"

The utterances in this model are full sentences of the form:
  "The electric kettle cost 1000 dollars"

We derive this compositionally:

1. **X** (e.g., "the electric kettle") denotes an item in a price state
2. **"cost"** is a measure predicate: cost : PriceState → ℚ
3. **"u dollars"** is a degree phrase denoting degree u
4. **Composition**: ⟦The X cost u dollars⟧ = cost(X) = u

This is grounded in Semantics.Lexical.Numeral infrastructure.
-/

/-- The "cost" measure predicate: ⟦cost⟧ = λx. price(x). -/
def costPredicate : MeasurePredicate PriceState :=
  MeasurePredicate.fromHasDegree PriceState "price (USD)"

/-- Compositional literal semantics for "The X cost u dollars".
⟦The X cost u dollars⟧ = cost(X) = u -/
def literalCompositional (u : PriceState) (world : PriceState) : Bool :=
  measureSentence costPredicate world (DegreePhrase.ofRat u.value "dollars")

/-- Simple literal semantics (equivalent, for convenience). -/
def literal (u : PriceState) (world : PriceState) : Bool :=
  numeralExact u.value world

/-- **Grounding**: Compositional and simple semantics are equivalent. -/
theorem literal_eq_compositional (u world : PriceState) :
    literal u world = literalCompositional u world := rfl

/-- **Grounding**: Literal semantics decomposes into HasDegree. -/
theorem literal_uses_degree (u world : PriceState) :
    literal u world = (HasDegree.degree world == u.value) := rfl

/-- **Grounding**: The cost predicate IS the HasDegree instance. -/
theorem costPredicate_is_hasDegree :
    costPredicate.μ = HasDegree.degree := rfl

/-- **Grounding**: Cost equals the price state's dollar value. -/
theorem cost_is_price_value (s : PriceState) :
    costPredicate.μ s = s.value := rfl

-- ============================================================================
-- L0: Literal Listener (Eq. 9)
-- ============================================================================

/-- L0(s,a|u) = P_A(a|s) if s = u, 0 otherwise.

L0 is purely literal — it checks if the utterance matches the price state,
then distributes over affect using the affect prior P_A.
The QUD does NOT enter at L0. -/
def meaning (_q : Goal) (u : PriceState) (w : World) : ℝ :=
  if u == w.1 then affectPrior w.1 w.2 else 0

-- ============================================================================
-- QUD Projection (Eq. 6)
-- ============================================================================

/-- Round a price state to its nearest round neighbor. -/
def PriceState.round : PriceState → PriceState
  | .s50 | .s51 => .s50
  | .s500 | .s501 => .s500
  | .s1000 | .s1001 => .s1000
  | .s5000 | .s5001 => .s5000
  | .s10000 | .s10001 => .s10000

/-- QUD projection: L0(g(s,a)|u) = Σ_{g(s',a')=g(s,a)} L0(s',a'|u).

This is Eq. 6 from the paper. The projection sums L0 over all (s',a')
in the same equivalence class as (s,a) under goal g.

Implemented as explicit pattern matching for rsa_decide compatibility. -/
def qudProject : Goal → (World → ℝ) → World → ℝ
  | .price, f, (s, _) =>
      -- Same exact price, both affects
      f (s, .none) + f (s, .notable)
  | .valence, f, (_, a) =>
      -- Same affect, all prices
      f (.s50, a) + f (.s51, a) + f (.s500, a) + f (.s501, a) +
      f (.s1000, a) + f (.s1001, a) + f (.s5000, a) + f (.s5001, a) +
      f (.s10000, a) + f (.s10001, a)
  | .priceValence, f, w =>
      -- Same exact price AND affect (identity projection)
      f w
  | .approxPrice, f, (s, _) =>
      -- Same rounded price, both affects
      let r := s.round
      f (r, .none) + f (r, .notable) +
      (if r == s then 0 else f (s, .none) + f (s, .notable))
  | .approxPriceValence, f, (s, a) =>
      -- Same rounded price AND same affect
      let r := s.round
      f (r, a) + (if r == s then 0 else f (s, a))

-- ============================================================================
-- RSAConfig (Eqs. 5, 7, 9, 10)
-- ============================================================================

/-- The Kao et al. (2014) hyperbole RSA model.

Item-parametric: different items have different price priors P_S,
leading to different hyperbole patterns.

S1 score follows the paper's Eqs. 5 and 7:

    S1(u|s,a,g) ∝ exp(α · [ln L0(g(s,a)|u) - C(u)])

rsa_decide performs the analytic simplification at evaluation time. -/
noncomputable def cfg (item : Item) :
    RSA.RSAConfig PriceState World where
  Latent := Goal
  meaning := meaning
  meaning_nonneg := by
    intro q u ⟨s, a⟩; simp only [meaning]
    split <;> (try exact le_refl 0)
    cases s <;> cases a <;> simp [affectPrior]
  s1Score l0 α q w u :=
    exp (α * (log (qudProject q (l0 u) w) - cost u))
  s1Score_nonneg _ _ _ _ _ _ _ := le_of_lt (exp_pos _)
  α := 1
  α_pos := one_pos
  worldPrior := fun ⟨s, a⟩ => pricePrior item s * affectPrior s a
  latentPrior_nonneg _ := by positivity
  worldPrior_nonneg := by
    intro ⟨s, a⟩; apply mul_nonneg
    · cases item <;> cases s <;> simp [pricePrior]
    · cases s <;> cases a <;> simp [affectPrior]

-- ============================================================================
-- Theorems
-- ============================================================================

noncomputable abbrev kettleCfg := cfg .electricKettle

/-- Hyperbole: L1 hearing "$10,000" for a kettle infers notable affect
    over no affect, at the most likely price ($50). -/
theorem hyperbole_notable_affect :
    kettleCfg.L1 .s10000 (.s50, .notable) >
    kettleCfg.L1 .s10000 (.s50, .none) := by
  sorry -- rsa_decide

/-- Literal: L1 hearing "$50" infers $50 > $500 price. -/
theorem literal_infers_price :
    kettleCfg.L1 .s50 (.s50, .none) >
    kettleCfg.L1 .s50 (.s500, .none) := by
  sorry -- rsa_decide

/-- QUD inference: "$10,000" → valence QUD more likely than price QUD. -/
theorem hyperbole_valence_qud :
    kettleCfg.L1_latent .s10000 .valence >
    kettleCfg.L1_latent .s10000 .price := by
  sorry -- rsa_decide

/-- Pragmatic halo: sharp "$501" is interpreted more exactly than round "$500".
    Measured by comparing exact interpretation probability. -/
theorem halo_sharp_more_exact :
    kettleCfg.L1 .s501 (.s501, .none) + kettleCfg.L1 .s501 (.s501, .notable) >
    kettleCfg.L1 .s500 (.s500, .none) + kettleCfg.L1 .s500 (.s500, .notable) := by
  sorry -- rsa_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## How QUD-RSA Derives Hyperbole

1. **Standard RSA** (without QUDs):
   - L0 assigns 0 probability to literally false utterances
   - S1 never chooses hyperbolic utterances (log 0 = -∞)
   - Hyperbole can't emerge

2. **QUD-RSA** (this model):
   - S1 optimizes informativity w.r.t. *projected* meaning under QUD
   - Under QUD "valence", meanings with same affect are equivalent
   - L0(g(s,a)|u) sums over the equivalence class, so even literally
     false utterances can have positive projected L0 if they share the
     affect dimension with true meanings
   - S1 can rationally choose "10,000" to communicate "notable affect"

3. **L1 Inference**:
   - Listener marginalizes over possible QUDs (uniform P_G)
   - Hearing "10,000" for a kettle → infers speaker probably had
     "valence" QUD (not "price", since $10,000 kettle is implausible)
   - Correctly recovers high-affect meaning despite literal falsity

## How Differential Cost Derives Pragmatic Halo

- Round numbers: C(round) = 1 (easy to produce)
- Sharp numbers: C(sharp) = 3.4 (costly to produce)
- Under approxPrice QUD, "500" and "501" convey the same information
- But "501" is costlier, so a speaker choosing "501" must have the
  exact price QUD → listener interprets "501" more precisely than "500"
-/

end RSA.KaoEtAl2014_Hyperbole
