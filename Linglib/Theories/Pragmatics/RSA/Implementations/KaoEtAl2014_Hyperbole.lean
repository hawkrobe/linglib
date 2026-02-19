import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Linglib.Theories.Semantics.Lexical.Numeral.Precision
import Linglib.Tactics.RSADecide
import Linglib.Core.Interval.PadeExp
import Linglib.Core.Interval.LogInterval

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
   C(round) = 0 < C(sharp) = 1.

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

Electric kettle values from the fitted empirical distribution (Kao et al. 2014,
Materials and Methods). Unnormalized (sum ≈ 10001 for electric kettle). -/
def pricePrior (item : Item) : PriceState → ℝ
  | .s50    => match item with | .electricKettle => 4205 | .laptop => 1 | .watch => 3
  | .s51    => match item with | .electricKettle => 3865 | .laptop => 1 | .watch => 3
  | .s500   => match item with | .electricKettle => 533  | .laptop => 6 | .watch => 4
  | .s501   => match item with | .electricKettle => 538  | .laptop => 6 | .watch => 4
  | .s1000  => match item with | .electricKettle => 223  | .laptop => 4 | .watch => 3
  | .s1001  => match item with | .electricKettle => 211  | .laptop => 4 | .watch => 3
  | .s5000  => match item with | .electricKettle => 112  | .laptop => 3 | .watch => 3
  | .s5001  => match item with | .electricKettle => 111  | .laptop => 3 | .watch => 3
  | .s10000 => match item with | .electricKettle => 83   | .laptop => 2 | .watch => 3
  | .s10001 => match item with | .electricKettle => 120  | .laptop => 2 | .watch => 3

/-- Affect prior P_A(a|s) from Experiment 3b.

The probability of having affect a given price state s, from the fitted
logistic function (Kao et al. 2014, Materials and Methods, p. 12006).
Higher prices → more likely to have negative affect ("too expensive").

Values are P_A(notable|s) × 10000 and P_A(none|s) × 10000, so each
pair sums to 10000 (unnormalized weights proportional to probabilities).

Key ratios:
- $50: notable/none ≈ 0.46 (mild negative affect)
- $10,000: notable/none ≈ 72.5 (strong negative affect)

This asymmetry is what drives hyperbole: the S1 advantage under the
valence QUD (72.5:1 at $10,000) overwhelms the world prior disadvantage
(2.15:1 at $50), making L1 infer notable affect. -/
def affectPrior : PriceState → Affect → ℝ
  | .s50,    .none => 6827 | .s50,    .notable => 3173
  | .s51,    .none => 6827 | .s51,    .notable => 3173
  | .s500,   .none => 2080 | .s500,   .notable => 7920
  | .s501,   .none => 2080 | .s501,   .notable => 7920
  | .s1000,  .none => 1067 | .s1000,  .notable => 8933
  | .s1001,  .none => 1067 | .s1001,  .notable => 8933
  | .s5000,  .none => 476  | .s5000,  .notable => 9524
  | .s5001,  .none => 476  | .s5001,  .notable => 9524
  | .s10000, .none => 136  | .s10000, .notable => 9864
  | .s10001, .none => 136  | .s10001, .notable => 9864

-- ============================================================================
-- Utterance Cost
-- ============================================================================

/-- Whether a price state is a round number (divisible by 10). -/
def PriceState.isRound : PriceState → Bool
  | .s50 | .s500 | .s1000 | .s5000 | .s10000 => true
  | .s51 | .s501 | .s1001 | .s5001 | .s10001 => false

/-- Utterance cost C(u).

C(round) = 0, C(sharp) = 1. Only the cost *difference* affects S1
(absolute costs cancel under normalization). This matches the reference
implementation; the paper's fitted ratio of 3.4 uses C(round) = 1,
C(sharp) = 3.4, which is equivalent to C(round) = 0, C(sharp) = 2.4
for the S1 policy. -/
noncomputable def cost : PriceState → ℝ
  | u => if u.isRound then 0 else 1

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
    -- Guard: when L0 projected probability is 0, score is 0 (= exp(-∞) in the paper).
    -- Without this, Real.log 0 = 0 (Lean convention) gives incorrect positive scores.
    let projected := qudProject q (l0 u) w
    if projected = 0 then 0
    else exp (α * (log projected - cost u))
  s1Score_nonneg _ _ _ _ _ _ _ := by
    simp only; split
    · exact le_refl 0
    · exact le_of_lt (exp_pos _)
  α := 1
  α_pos := one_pos
  worldPrior := fun ⟨s, a⟩ => pricePrior item s * affectPrior s a
  latentPrior_nonneg _ := by positivity
  worldPrior_nonneg := by
    intro ⟨s, a⟩; apply mul_nonneg
    · cases item <;> cases s <;> simp [pricePrior]
    · cases s <;> cases a <;> simp [affectPrior]

-- ============================================================================
-- Computable Interval Evaluator
-- ============================================================================

/-! All RSA computations use ℝ (noncomputable). To prove comparisons via
`native_decide`, we mirror the computation using computable `QInterval`
arithmetic. The `native_decide` kernel proof is just one `Decidable` check
on ℚ values — no Nat.cast reductions, no whnf expansion. -/

open Linglib.Interval Linglib.Interval.QInterval

/-- ℚ version of affectPrior. -/
def affectPrior_q : PriceState → Affect → ℚ
  | .s50,    .none => 6827 | .s50,    .notable => 3173
  | .s51,    .none => 6827 | .s51,    .notable => 3173
  | .s500,   .none => 2080 | .s500,   .notable => 7920
  | .s501,   .none => 2080 | .s501,   .notable => 7920
  | .s1000,  .none => 1067 | .s1000,  .notable => 8933
  | .s1001,  .none => 1067 | .s1001,  .notable => 8933
  | .s5000,  .none => 476  | .s5000,  .notable => 9524
  | .s5001,  .none => 476  | .s5001,  .notable => 9524
  | .s10000, .none => 136  | .s10000, .notable => 9864
  | .s10001, .none => 136  | .s10001, .notable => 9864

/-- ℚ version of pricePrior. -/
def pricePrior_q (item : Item) : PriceState → ℚ
  | .s50    => match item with | .electricKettle => 4205 | .laptop => 1 | .watch => 3
  | .s51    => match item with | .electricKettle => 3865 | .laptop => 1 | .watch => 3
  | .s500   => match item with | .electricKettle => 533  | .laptop => 6 | .watch => 4
  | .s501   => match item with | .electricKettle => 538  | .laptop => 6 | .watch => 4
  | .s1000  => match item with | .electricKettle => 223  | .laptop => 4 | .watch => 3
  | .s1001  => match item with | .electricKettle => 211  | .laptop => 4 | .watch => 3
  | .s5000  => match item with | .electricKettle => 112  | .laptop => 3 | .watch => 3
  | .s5001  => match item with | .electricKettle => 111  | .laptop => 3 | .watch => 3
  | .s10000 => match item with | .electricKettle => 83   | .laptop => 2 | .watch => 3
  | .s10001 => match item with | .electricKettle => 120  | .laptop => 2 | .watch => 3

/-- ℚ version of cost. -/
def cost_q : PriceState → ℚ
  | u => if u.isRound then 0 else 1

/-- ℚ literal semantics: meaning(q, u, w) = if u == w.1 then affectPrior(w) else 0. -/
def meaning_q (_q : Goal) (u : PriceState) (w : World) : ℚ :=
  if u == w.1 then affectPrior_q w.1 w.2 else 0

private def allWorlds : List World :=
  do let s ← [PriceState.s50, .s51, .s500, .s501, .s1000, .s1001, .s5000, .s5001, .s10000, .s10001]
     let a ← [Affect.none, .notable]
     return (s, a)

private def allUtterances : List PriceState :=
  [.s50, .s51, .s500, .s501, .s1000, .s1001, .s5000, .s5001, .s10000, .s10001]

private def allGoals : List Goal :=
  [.price, .valence, .priceValence, .approxPrice, .approxPriceValence]

/-- L0 policy (exact ℚ): meaning / Σ_w' meaning. -/
def L0_policy_q (q : Goal) (u : PriceState) (w : World) : ℚ :=
  let total := allWorlds.foldl (fun acc w' => acc + meaning_q q u w') 0
  if total == 0 then 0 else meaning_q q u w / total

/-- QUD projection (ℚ version). -/
def qudProject_q : Goal → (World → ℚ) → World → ℚ
  | .price, f, (s, _) => f (s, .none) + f (s, .notable)
  | .valence, f, (_, a) =>
      f (.s50, a) + f (.s51, a) + f (.s500, a) + f (.s501, a) +
      f (.s1000, a) + f (.s1001, a) + f (.s5000, a) + f (.s5001, a) +
      f (.s10000, a) + f (.s10001, a)
  | .priceValence, f, w => f w
  | .approxPrice, f, (s, _) =>
      let r := s.round
      f (r, .none) + f (r, .notable) +
      (if r == s then 0 else f (s, .none) + f (s, .notable))
  | .approxPriceValence, f, (s, a) =>
      let r := s.round
      f (r, a) + (if r == s then 0 else f (s, a))

/-- S1 score as QInterval: exp(α · (log(projected) - cost(u))). -/
def S1_score_qi (q : Goal) (w : World) (u : PriceState) : QInterval :=
  let projected := qudProject_q q (fun w' => L0_policy_q q u w') w
  if projected == 0 then QInterval.exact 0
  else if h : (0 : ℚ) < projected then
    let proj_qi : QInterval := QInterval.exact projected
    let log_proj := Linglib.Interval.logInterval proj_qi h
    let cost_qi := QInterval.exact (cost_q u)
    -- α = 1, so score = exp(log(projected) - cost(u))
    Linglib.Interval.expInterval (log_proj.sub cost_qi)
  else QInterval.exact 0  -- unreachable: projected > 0 when nonzero

/-- L1 score as QInterval: worldPrior(w) · Σ_q latentPrior(q) · S1(q, w, u) / Σ_u' S1(q, w, u'). -/
def L1_score_qi (item : Item) (u_obs : PriceState) (w : World) : QInterval :=
  let wp := pricePrior_q item w.1 * affectPrior_q w.1 w.2
  let wp_qi := QInterval.exact wp
  -- Σ_q [ 1 · S1_policy(q, w, u_obs) ] where latentPrior = 1 for all goals
  let s1_sum := allGoals.foldl (fun acc q =>
    let s1_u := S1_score_qi q w u_obs
    let s1_total := allUtterances.foldl (fun acc' u' => acc'.add (S1_score_qi q w u')) (QInterval.exact 0)
    -- S1_policy = s1_score / s1_total
    let s1_policy :=
      if h₁ : 0 ≤ s1_u.lo then
        if h₂ : (0 : ℚ) < s1_total.lo then s1_u.divPos s1_total h₁ h₂
        else ⟨0, 1, by norm_num⟩
      else ⟨0, 1, by norm_num⟩
    acc.add s1_policy) (QInterval.exact 0)
  wp_qi.mul s1_sum

/-- Soundness: L1_score_qi bounds the real L1 score.

    Proof outline: Each step of the QInterval computation mirrors the ℝ computation.
    The ℚ priors cast to the ℝ priors, L0 policy is exact (ℚ division), QUD projection
    is exact (ℚ sums), and exp/log are bounded by expInterval/logInterval containment.
    TODO: prove from containment properties of each interval operation. -/
axiom L1_score_qi_contains (item : Item) (u : PriceState) (w : World) :
    (L1_score_qi item u w).containsReal ((cfg item).L1agent.score u w)

/-- If interval bounds separate, L1 values are ordered. -/
theorem L1_gt_of_qi_sep (item : Item) (u : PriceState) (w₁ w₂ : World)
    (h : (L1_score_qi item u w₂).hi < (L1_score_qi item u w₁).lo) :
    (cfg item).L1 u w₁ > (cfg item).L1 u w₂ :=
  Core.RationalAction.policy_gt_of_score_gt (cfg item).L1agent u w₁ w₂
    (QInterval.gt_of_separated (L1_score_qi_contains item u w₁)
      (L1_score_qi_contains item u w₂) h)

-- ============================================================================
-- Extended Evaluator: Marginals, Latent, Policy
-- ============================================================================

/-- S1 policy as QInterval: S1_score / Σ_u' S1_score. -/
private def S1_policy_qi (q : Goal) (w : World) (u : PriceState) : QInterval :=
  let score := S1_score_qi q w u
  let total := allUtterances.foldl (fun acc u' =>
    acc.add (S1_score_qi q w u')) (QInterval.exact 0)
  if h₁ : 0 ≤ score.lo then
    if h₂ : (0 : ℚ) < total.lo then score.divPos total h₁ h₂
    else ⟨0, 1, by norm_num⟩
  else ⟨0, 1, by norm_num⟩

/-- Marginal L1 score: Σ_s L1_score(item, u, (s, a)).
    Proportional to P(a | u) since all terms share the L1 denominator. -/
def L1_marginal_score_qi (item : Item) (u : PriceState) (a : Affect) : QInterval :=
  allUtterances.foldl (fun acc s =>
    acc.add (L1_score_qi item u (s, a))) (QInterval.exact 0)

/-- Soundness: L1_marginal_score_qi bounds the real marginal L1 score.
    TODO: derive from L1_score_qi_contains + add_containsReal. -/
axiom L1_marginal_score_qi_contains (item : Item) (u : PriceState) (a : Affect) :
    (L1_marginal_score_qi item u a).containsReal
      (∑ s : PriceState, (cfg item).L1agent.score u (s, a))

/-- Marginal score separation → marginal affect ordering.
    Shared denominator: Σ_s L1(u,(s,a)) = (Σ_s score(u,(s,a))) / total(u),
    so score ordering implies policy ordering when total > 0.
    TODO: prove via Finset.sum_div + div_lt_div_of_pos_right. -/
theorem marginal_affect_gt_of_sep (item : Item) (u : PriceState) (a₁ a₂ : Affect)
    (h : (L1_marginal_score_qi item u a₂).hi < (L1_marginal_score_qi item u a₁).lo) :
    ∑ s : PriceState, (cfg item).L1 u (s, a₁) >
    ∑ s : PriceState, (cfg item).L1 u (s, a₂) := by
  have hscore : ∑ s, (cfg item).L1agent.score u (s, a₁) >
      ∑ s, (cfg item).L1agent.score u (s, a₂) :=
    QInterval.gt_of_separated
      (L1_marginal_score_qi_contains item u a₁)
      (L1_marginal_score_qi_contains item u a₂) h
  sorry -- shared denominator: score(a₁) > score(a₂) → policy(a₁) > policy(a₂)

/-- L1 latent score: Σ_w worldPrior(w) · S1_policy(q, w, u).
    With latentPrior = 1, this is proportional to P(QUD=q | u). -/
def L1_latent_score_qi (item : Item) (u : PriceState) (q : Goal) : QInterval :=
  allWorlds.foldl (fun acc w =>
    let wp := QInterval.exact (pricePrior_q item w.1 * affectPrior_q w.1 w.2)
    let s1p := S1_policy_qi q w u
    acc.add (wp.mul s1p)) (QInterval.exact 0)

/-- Soundness: L1_latent_score_qi bounds the real L1_latent numerator.
    TODO: derive from S1 containment + mul/add_containsReal. -/
axiom L1_latent_score_qi_contains (item : Item) (u : PriceState) (q : Goal) :
    (L1_latent_score_qi item u q).containsReal
      (∑ w : World, (cfg item).worldPrior w * (cfg item).S1 q w u)

/-- L1_latent as a RationalAction (for reusing policy_gt_of_score_gt). -/
private noncomputable def latentAgent (item : Item) :
    Core.RationalAction PriceState Goal where
  score u q := (cfg item).latentPrior q *
    ∑ w : World, (cfg item).worldPrior w * (cfg item).S1 q w u
  score_nonneg u q := mul_nonneg ((cfg item).latentPrior_nonneg q)
    (Finset.sum_nonneg fun w _ =>
      mul_nonneg ((cfg item).worldPrior_nonneg w) ((cfg item).S1_nonneg q w u))

/-- L1_latent equals latentAgent.policy (definitional). -/
private theorem L1_latent_eq_policy (item : Item) (u : PriceState) (q : Goal) :
    (cfg item).L1_latent u q = (latentAgent item).policy u q := rfl

/-- Latent score separation → L1_latent ordering. -/
theorem L1_latent_gt_of_sep (item : Item) (u : PriceState) (q₁ q₂ : Goal)
    (h : (L1_latent_score_qi item u q₂).hi < (L1_latent_score_qi item u q₁).lo) :
    (cfg item).L1_latent u q₁ > (cfg item).L1_latent u q₂ := by
  have hscore : ∑ w, (cfg item).worldPrior w * (cfg item).S1 q₁ w u >
      ∑ w, (cfg item).worldPrior w * (cfg item).S1 q₂ w u :=
    QInterval.gt_of_separated
      (L1_latent_score_qi_contains item u q₁)
      (L1_latent_score_qi_contains item u q₂) h
  rw [L1_latent_eq_policy, L1_latent_eq_policy]
  apply Core.RationalAction.policy_gt_of_score_gt
  show (latentAgent item).score u q₁ > (latentAgent item).score u q₂
  simp only [latentAgent, cfg, RSA.RSAConfig.latentPrior, one_mul]
  exact hscore

/-- L1 total score: Σ_w L1_score(item, u, w). -/
private def L1_total_qi (item : Item) (u : PriceState) : QInterval :=
  allWorlds.foldl (fun acc w =>
    acc.add (L1_score_qi item u w)) (QInterval.exact 0)

/-- L1 policy as QInterval: score / total. -/
private def L1_policy_qi (item : Item) (u : PriceState) (w : World) : QInterval :=
  let score := L1_score_qi item u w
  let total := L1_total_qi item u
  if h₁ : 0 ≤ score.lo then
    if h₂ : 0 < total.lo then score.divPos total h₁ h₂
    else ⟨0, 1, by norm_num⟩
  else ⟨0, 1, by norm_num⟩

/-- Exact-match probability interval: Σ_a L1_policy(item, u, (u, a)).
    Measures how precisely the listener interprets utterance u. -/
def L1_exact_match_qi (item : Item) (u : PriceState) : QInterval :=
  (L1_policy_qi item u (u, .none)).add (L1_policy_qi item u (u, .notable))

/-- Soundness: L1_exact_match_qi bounds the real exact-match probability.
    TODO: derive from L1 policy containment + add_containsReal. -/
axiom L1_exact_match_qi_contains (item : Item) (u : PriceState) :
    (L1_exact_match_qi item u).containsReal
      ((cfg item).L1 u (u, .none) + (cfg item).L1 u (u, .notable))

/-- Halo: exact-match separation → exact-match probability ordering. -/
theorem halo_gt_of_sep (item : Item) (u₁ u₂ : PriceState)
    (h : (L1_exact_match_qi item u₂).hi < (L1_exact_match_qi item u₁).lo) :
    (cfg item).L1 u₁ (u₁, .none) + (cfg item).L1 u₁ (u₁, .notable) >
    (cfg item).L1 u₂ (u₂, .none) + (cfg item).L1 u₂ (u₂, .notable) :=
  QInterval.gt_of_separated
    (L1_exact_match_qi_contains item u₁)
    (L1_exact_match_qi_contains item u₂) h

-- ============================================================================
-- Theorems
-- ============================================================================

noncomputable abbrev kettleCfg := cfg .electricKettle

/-- Hyperbole: L1 hearing "$10,000" for a kettle assigns higher marginal
    probability to notable affect than to no affect.
    P(notable | u=$10K) = Σ_s L1($10K, (s, notable)) > Σ_s L1($10K, (s, none)). -/
theorem hyperbole_notable_affect :
    ∑ s : PriceState, kettleCfg.L1 .s10000 (s, .notable) >
    ∑ s : PriceState, kettleCfg.L1 .s10000 (s, .none) :=
  marginal_affect_gt_of_sep .electricKettle .s10000 .notable .none (by native_decide)

/-- Literal: L1 hearing "$50" infers $50 > $500 price. -/
theorem literal_infers_price :
    kettleCfg.L1 .s50 (.s50, .none) >
    kettleCfg.L1 .s50 (.s500, .none) :=
  L1_gt_of_qi_sep .electricKettle .s50 (.s50, .none) (.s500, .none) (by native_decide)

/-- QUD inference: "$10,000" → valence QUD more likely than price QUD. -/
theorem hyperbole_valence_qud :
    kettleCfg.L1_latent .s10000 .valence >
    kettleCfg.L1_latent .s10000 .price :=
  L1_latent_gt_of_sep .electricKettle .s10000 .valence .price (by native_decide)

/-- Pragmatic halo: sharp "$501" is interpreted more exactly than round "$500".
    Measured by comparing exact interpretation probability. -/
theorem halo_sharp_more_exact :
    kettleCfg.L1 .s501 (.s501, .none) + kettleCfg.L1 .s501 (.s501, .notable) >
    kettleCfg.L1 .s500 (.s500, .none) + kettleCfg.L1 .s500 (.s500, .notable) :=
  halo_gt_of_sep .electricKettle .s501 .s500 (by native_decide)

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

- Round numbers: C(round) = 0 (easy to produce)
- Sharp numbers: C(sharp) = 1 (costly to produce)
- Under approxPrice QUD, "500" and "501" convey the same information
- But "501" is costlier, so a speaker choosing "501" must have the
  exact price QUD → listener interprets "501" more precisely than "500"
-/

end RSA.KaoEtAl2014_Hyperbole
