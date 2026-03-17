import Linglib.Core.Scales.Roundness
import Linglib.Phenomena.Numerals.Studies.WoodinEtAl2024
import Linglib.Theories.Semantics.Lexical.Numeral.Precision
import Linglib.Theories.Pragmatics.Implicature.Constraints.NumericalExpressions
import Linglib.Fragments.English.NumeralModifiers
import Linglib.Phenomena.Numerals.Studies.ClausWalch2024
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Order
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config

/-!
# Bridge Theorems: Numeral Salience across Frameworks
@cite{blok-2015} @cite{claus-walch-2024} @cite{cummins-2015} @cite{cummins-franke-2021} @cite{lasersohn-1999} @cite{woodin-etal-2023}

Connects the graded roundness model (k-ness) to ten existing modules:

1. **NSAL ↔ RSA cost**: OT NSAL violations as normalized RSA utterance cost
2. **Woodin frequency ↔ RSA prior**: weighted roundness as utterance prior
3. **k-ness ↔ PrecisionMode**: roundness score grounds Kao et al.'s binary switch
4. **k-ness ↔ NumeralModifiers**: tolerance modifiers pair with high roundness
5. **k-ness ↔ C&F enrichment**: wider enrichment for rounder numerals
6. **OT ↔ RSA parameter map**: constraint-to-parameter correspondence
7. **Evaluative valence ↔ framing**: @cite{claus-walch-2024} framing predictions
8. **maxMeaning ↔ HasDegree**: degree bridge theorems
9. **NumeralTheory ↔ RSA L1**: lower-bound semantics + RSA derives exact readings
10. **Kennedy alternatives ↔ RSA**: Class A/B competition via `RSAConfig` + `rsa_predict`

## Architecture

```
Phenomena.Gradability.Imprecision.Numerals (k-ness core)
    ↑ ↑ ↑
    |              |                |
Phenomena. NeoGricean. Semantics.Montague.
NumberUse. Constraints. Domain.Degree
WoodinEtAl2024 NumericalExprs (extended)
    ↑ ↑ ↑
    +--------------+-------+--------+
                           |
               Phenomena.Numerals.Compare (this file)
```

-/

namespace Phenomena.Numerals.Compare

open Core.Roundness
open Phenomena.Numerals.Studies.WoodinEtAl2024
open Implicature.Constraints.NumericalExpressions
open Semantics.Lexical.Numeral.Precision
open Core.Scale (HasDegree)

-- ============================================================================
-- Bridge 1: NSAL ↔ RSA cost
-- ============================================================================

/-!
### NSAL as RSA Utterance Cost

In RSA, `cost : U → ℚ` penalizes certain utterances. The OT constraint NSAL
provides a principled grounding: cost(u) = nsalViolations(u) / 6.

Round numerals (100, 1000) have cost ≈ 0; non-round (7, 99) have cost ≈ 1.
This connects @cite{cummins-2015}'s constraint-based account to the Bayesian RSA
framework via the `cost` field of `RSAScenario`.
-/

/-- Round numerals incur lower RSA cost than non-round ones. -/
theorem round_cheaper_in_rsa_bridge :
    nsalAsRSACost 100 < nsalAsRSACost 99 := by native_decide

/-- Maximally round numerals are free (zero cost). -/
theorem maximally_round_free :
    nsalAsRSACost 100 = 0 ∧ nsalAsRSACost 1000 = 0 := by
  constructor <;> native_decide

-- ============================================================================
-- Bridge 2: Woodin frequency ↔ RSA utterance prior
-- ============================================================================

/-!
### Weighted Roundness as Utterance Prior

In RSA, a uniform utterance prior is standard. But Woodin et al.'s frequency
data suggests round numerals are *a priori* more available to speakers.
`weightedRoundnessScore` provides an empirically-grounded utterance prior:
rounder numerals are more likely to be chosen, all else being equal.
-/

/-- Rounder numerals have higher prior weight. -/
theorem roundness_prior_monotone :
    weightedRoundnessScore 100 > weightedRoundnessScore 50 ∧
    weightedRoundnessScore 50 > weightedRoundnessScore 7 := by
  constructor <;> native_decide

-- ============================================================================
-- Bridge 3: k-ness ↔ PrecisionMode
-- ============================================================================

/-!
### Roundness Grounds Precision Mo@cite{kao-etal-2014-hyperbole} use a binary `PrecisionMode` (.exact/.approximate) with
`Goal.approxPrice` using fixed `base := 10`. The k-ness model provides a
principled threshold: score ≥ 2 → `.approximate`, else `.exact`.

This means:
- 100 (score 6) → approximate: "1000 dollars" allows ±100 slack
- 110 (score 2) → approximate: "110 dollars" allows some slack
- 99 (score 0) → exact: "99 dollars" requires precise reading
-/

/-- Precision mode agrees with Kao et al.'s implicit assumptions.
    Round numbers (multiples of 10) get approximate mode. -/
theorem roundness_grounds_precision_100 :
    inferPrecisionMode 100 = .approximate := by native_decide

theorem roundness_grounds_precision_7 :
    inferPrecisionMode 7 = .exact := by native_decide

/-- Fixed base-10 rounding and adaptive precision mode agree on round numbers:
    if n is round (divisible by 10), inferPrecisionMode gives.approximate. -/
theorem base10_round_implies_approximate (n : Nat) (h : n > 0)
    (hr : n % 10 = 0) :
    inferPrecisionMode n = .approximate := by
  unfold inferPrecisionMode
  have hs := Core.Roundness.score_ge_two_of_div10 n hr
  split
  · rfl
  · omega

-- ============================================================================
-- Bridge 4: k-ness ↔ NumeralModifiers
-- ============================================================================

/-!
### Roundness and Tolerance Modifiers

Numeral modifiers like "approximately" and "around" interact with roundness:
- `requiresRound = true` modifiers need a round numeral
- `requiresRound = false` modifiers tolerate non-round but sound marked

The k-ness model predicts this: tolerance modifiers combine naturally with
high-roundness numerals because the pragmatic halo is already wide.
-/

open Fragments.English.NumeralModifiers in
/-- "approximately" does not *require* roundness but pairs better with it.
    The requiresRound field is false, but naturalness correlates with score. -/
theorem approximately_tolerates_nonround :
    approximately.requiresRound = false := by native_decide

/-- Halo width is larger for round numerals, explaining modifier naturalness. -/
theorem round_wider_halo :
    haloWidth 100 > haloWidth 7 := by native_decide

-- ============================================================================
-- Bridge 5: k-ness ↔ C&F enrichment width
-- ============================================================================

/-!
### Roundness Predicts Enrichment Width

@cite{cummins-franke-2021} show that "more than M" undergoes pragmatic enrichment
to "between M and M+δ" for some δ. The enrichment width δ depends on the
roundness of M:

- "more than 100" (score 6): enriched to 101–120 (width 20)
- "more than 110" (score 2): enriched to 111–120 (width 10)

The wider enrichment for 100 admits more non-goal worlds, weakening its
argumentative strength — explaining C&F's pragmatic reversal.
-/

/-- 100 gets wider enrichment than 110, explaining the pragmatic reversal. -/
theorem enrichment_100_wider_than_110 :
    enrichmentWidth 100 > enrichmentWidth 110 := by native_decide

/-- Non-round numerals get minimal enrichment. -/
theorem nonround_minimal_enrichment :
    enrichmentWidth 7 = 4 := by native_decide

-- ============================================================================
-- Bridge 6: OT ↔ RSA parameter map
-- ============================================================================

/-!
### OT Constraint ↔ RSA Parameter Correspondence

| OT Constraint | RSA Parameter | Connection |
|---------------|---------------|------------|
| INFO          | φ (agreement) | Both measure truth-conditional informativeness |
| Granularity   | QUD / Goal    | Both encode contextual precision requirements |
| QSIMP         | cost (additive) | Modifier complexity as utterance cost |
| NSAL          | cost (roundness) | k-ness violations as utterance cost |

This mapping is not formal isomorphism but conceptual correspondence:
both frameworks explain the same empirical patterns (round number preference,
context-sensitivity) through different mechanisms.
-/

/-- The OT and RSA accounts agree on the key prediction:
    round numerals are preferred over non-round when informativeness is equal. -/
theorem ot_rsa_agree_round_preference :
    -- OT: fewer NSAL violations
    nsalViolations 100 < nsalViolations 99 ∧
    -- RSA: lower cost
    nsalAsRSACost 100 < nsalAsRSACost 99 := by
  constructor <;> native_decide

-- ============================================================================
-- Bridge 7: Evaluative Valence → Framing Prediction (@cite{claus-walch-2024})
-- ============================================================================

/-!
### Evaluative Valence Predicts Framing Direction

@cite{claus-walch-2024} show that "at most" and "up to" have the same truth
conditions but opposite framing effects. The `evaluativeValence` field in
`NumeralModifierEntry` predicts this:

| Modifier  | Valence  | Predicted framing | Observed framing |
|-----------|----------|-------------------|------------------|
| "at most" | negative | reversed          | reversed         |
| "up to"   | positive | standard          | standard         |

The prediction: negative valence → reversed framing, positive/neutral → standard.
-/

section Bridge7

open Fragments.English.NumeralModifiers
open Phenomena.Numerals.Studies.ClausWalch2024

/-- "at most" has negative evaluative valence, which predicts reversed framing.

The formal valence field aligns with C&W's experimental observation that
"at most" is endorsed more in negative contexts. -/
theorem atMost_negative_predicts_reversal :
    atMost.evaluativeValence = .negative ∧
    exp2_atMost_reversed.endorsementRate > exp2_atMost_standard.endorsementRate := by
  constructor <;> native_decide

/-- "up to" has positive evaluative valence, which predicts standard framing.

The formal valence field aligns with C&W's experimental observation that
"up to" is endorsed more in positive contexts. -/
theorem upTo_positive_predicts_standard :
    upTo.evaluativeValence = .positive ∧
    exp2_upTo_standard.endorsementRate > exp2_upTo_reversed.endorsementRate := by
  constructor <;> native_decide

/-- Valence divergence fully explains the framing divergence.

Despite identical truth conditions (both Class B upper-bound), "at most" and
"up to" show opposite framing because they differ in evaluative valence. -/
theorem valence_explains_framing_divergence :
    -- Same Kennedy class
    atMost.modClass = upTo.modClass ∧
    -- Same bound direction
    atMost.boundDir = upTo.boundDir ∧
    -- Different valence
    atMost.evaluativeValence ≠ upTo.evaluativeValence ∧
    -- Different framing (at most reversed, up to standard)
    exp2_atMost_reversed.endorsementRate > exp2_atMost_standard.endorsementRate ∧
    exp2_upTo_standard.endorsementRate > exp2_upTo_reversed.endorsementRate := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end Bridge7

-- ============================================================================
-- Bridge 8: maxMeaning ↔ HasDegree (moved from Semantics.lean)
-- ============================================================================

/-!
### Degree Bridge Theorems

Connect the pure-Nat `maxMeaning` comparisons to `HasDegree.degree` (ℚ-valued).
The `CardinalityDegree` instance maps `Nat` to `ℚ` via cast; these theorems
prove the two representations agree for all five `OrderingRel` variants.
-/

section Bridge8_Degree

open Semantics.Lexical.Numeral
open Semantics.Lexical.Numeral.Precision
open Core.Scale (HasDegree)

/-- A type with a natural-number cardinality measure. -/
instance CardinalityDegree : HasDegree Nat where
  degree := λ n => (n : ℚ)

theorem maxMeaning_gt_from_degree (m n : Nat) :
    moreThanMeaning m n = decide (HasDegree.degree n > (m : ℚ)) := by
  simp only [moreThanMeaning, maxMeaning, HasDegree.degree]
  congr 1
  exact propext (@Nat.cast_lt ℚ _ _ _ _).symm

theorem maxMeaning_ge_from_degree (m n : Nat) :
    atLeastMeaning m n = decide (HasDegree.degree n ≥ (m : ℚ)) := by
  simp only [atLeastMeaning, maxMeaning, HasDegree.degree]
  congr 1
  exact propext (@Nat.cast_le ℚ _ _ _ _).symm

/-- Exact bare numeral meaning equals degree equality (@cite{bylinina-nouwen-2020} §4). -/
theorem maxMeaning_eq_from_degree (m n : Nat) :
    bareMeaning m n = decide (HasDegree.degree n = (m : ℚ)) := by
  simp only [bareMeaning, maxMeaning, HasDegree.degree]
  by_cases h : n = m <;> simp [h, Nat.cast_inj]

/-- "Fewer than" bridges to strict degree inequality. -/
theorem maxMeaning_lt_from_degree (m n : Nat) :
    fewerThanMeaning m n = decide (HasDegree.degree n < (m : ℚ)) := by
  simp only [fewerThanMeaning, maxMeaning, HasDegree.degree]
  congr 1
  exact propext (@Nat.cast_lt ℚ _ _ _ _).symm

/-- "At most" bridges to degree ≤. -/
theorem maxMeaning_le_from_degree (m n : Nat) :
    atMostMeaning m n = decide (HasDegree.degree n ≤ (m : ℚ)) := by
  simp only [atMostMeaning, maxMeaning, HasDegree.degree]
  congr 1
  exact propext (@Nat.cast_le ℚ _ _ _ _).symm

end Bridge8_Degree

-- ============================================================================
-- Bridge 9: NumeralTheory ↔ RSA L1
-- ============================================================================

/-!
### Bridge 9: NumeralTheory ↔ RSA L1

Standard RSA (L0→S1→L1) with bare numeral utterances over a 0-3 cardinality
domain. Under lower-bound semantics (≥), RSA pragmatic reasoning derives the
exact reading as a scalar implicature:

- "two" literally means ≥2, but L1("two") peaks at w=2 (not w=3)
- "one" literally means ≥1, but L1("one") peaks at w=1

Reimplements `NumeralTheory.runL1` using `RSAConfig` + `rsa_predict`.
-/

section Bridge9

open Semantics.Lexical.Numeral

/-- Finite cardinality type (worlds 0-3). -/
inductive NCard where
  | c0 | c1 | c2 | c3
  deriving DecidableEq, BEq, Repr, Fintype

def NCard.toNat : NCard → Nat
  | .c0 => 0 | .c1 => 1 | .c2 => 2 | .c3 => 3

/-- Utterance type for standard numeral words. -/
inductive NUtt where
  | one | two | three
  deriving DecidableEq, BEq, Repr, Fintype

def NUtt.toBareNumeral : NUtt → BareNumeral
  | .one => .one | .two => .two | .three => .three

/-- Lower-bound meaning: "one" = ≥1, "two" = ≥2, "three" = ≥3.
    Inlined for `rsa_predict` reification (avoids `maxMeaning` indirection). -/
def lbNuttMeaning : NUtt → NCard → Bool
  | .one,   w => w.toNat ≥ 1
  | .two,   w => w.toNat ≥ 2
  | .three, w => w.toNat ≥ 3

open RSA Real in
/-- Lower-bound numeral RSA: bare numerals under ≥ semantics with
    belief-based S1 (score = L0^α). -/
noncomputable def lbNumeralCfg : RSAConfig NUtt NCard where
  Latent := Unit
  meaning _ _ u w := if lbNuttMeaning u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg l0 α _ _ u hl0 _ := rpow_nonneg (hl0 u _) α
  α := 1
  α_pos := one_pos
  worldPrior_nonneg _ := by positivity
  latentPrior_nonneg _ _ := by positivity

/-- Under lower-bound semantics, RSA strengthens "two" from ≥2 to the exact
    reading: L1 assigns more probability to w=2 than w=3. -/
theorem lb_rsa_strengthens_two :
    lbNumeralCfg.L1 .two .c2 > lbNumeralCfg.L1 .two .c3 := by rsa_predict

/-- RSA strengthens "one" analogously: L1("one", w=1) > L1("one", w=2). -/
theorem lb_rsa_strengthens_one :
    lbNumeralCfg.L1 .one .c1 > lbNumeralCfg.L1 .one .c2 := by rsa_predict

/-- "Three" trivially peaks at w=3 (only compatible world in the 0-3 range). -/
theorem lb_three_peaked :
    lbNumeralCfg.L1 .three .c3 > lbNumeralCfg.L1 .three .c2 := by rsa_predict

/-- The inlined meaning agrees with `LowerBound.meaning` (grounding). -/
theorem lbNuttMeaning_eq_lowerBound (u : NUtt) (w : NCard) :
    lbNuttMeaning u w = LowerBound.meaning u.toBareNumeral w.toNat := by
  cases u <;> cases w <;> native_decide

end Bridge9

-- ============================================================================
-- Bridge 10: Kennedy Alternative Sets ↔ RSA
-- ============================================================================

/-!
### Bridge 10: Kennedy Alternative Sets through RSA
@cite{kennedy-2015}

@cite{kennedy-2015}'s alternative sets for modified numerals through RSA L1.
Lower alternatives for n=3: {bare 3, more than 3, at least 3}.
Upper alternatives for n=3: {bare 3, fewer than 3, at most 3}.

Under bilateral (exact) bare-numeral semantics, RSA predicts:
- Class B (≥, ≤) modifiers trigger ignorance implicatures at the boundary
- Class A (>, <) modifiers exclude the boundary semantically
- Bare numerals retain peaked (exact) interpretations

Reimplements `kennedyLowerL1`, `kennedyUpperL1`, and all Kennedy
alternative set theorems using `RSAConfig` + `rsa_predict`.
-/

section Bridge10

open Semantics.Lexical.Numeral

/-- Wider cardinality range (0-5) for modified numeral competition. -/
inductive KCard where
  | c0 | c1 | c2 | c3 | c4 | c5
  deriving DecidableEq, BEq, Repr, Fintype

def KCard.toNat : KCard → Nat
  | .c0 => 0 | .c1 => 1 | .c2 => 2 | .c3 => 3 | .c4 => 4 | .c5 => 5

/-- Lower-bound Kennedy alternatives for n=3. -/
inductive KLowerUtt where
  | bare3 | moreThan3 | atLeast3
  deriving DecidableEq, BEq, Repr, Fintype

/-- Inlined meaning for reification (avoids `maxMeaning` indirection). -/
def kLowerMeaning : KLowerUtt → KCard → Bool
  | .bare3,     w => w.toNat == 3
  | .moreThan3, w => w.toNat > 3
  | .atLeast3,  w => w.toNat ≥ 3

/-- Upper-bound Kennedy alternatives for n=3. -/
inductive KUpperUtt where
  | bare3 | fewerThan3 | atMost3
  deriving DecidableEq, BEq, Repr, Fintype

/-- Inlined meaning for reification (avoids `maxMeaning` indirection). -/
def kUpperMeaning : KUpperUtt → KCard → Bool
  | .bare3,      w => w.toNat == 3
  | .fewerThan3, w => w.toNat < 3
  | .atMost3,    w => w.toNat ≤ 3

open RSA Real in
/-- Kennedy lower-bound alternatives through RSA L1 (bilateral bare semantics). -/
noncomputable def kennedyLowerCfg : RSAConfig KLowerUtt KCard where
  Latent := Unit
  meaning _ _ u w := if kLowerMeaning u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg l0 α _ _ u hl0 _ := rpow_nonneg (hl0 u _) α
  α := 1
  α_pos := one_pos
  worldPrior_nonneg _ := by positivity
  latentPrior_nonneg _ _ := by positivity

open RSA Real in
/-- Kennedy upper-bound alternatives through RSA L1 (bilateral bare semantics). -/
noncomputable def kennedyUpperCfg : RSAConfig KUpperUtt KCard where
  Latent := Unit
  meaning _ _ u w := if kUpperMeaning u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg l0 α _ _ u hl0 _ := rpow_nonneg (hl0 u _) α
  α := 1
  α_pos := one_pos
  worldPrior_nonneg _ := by positivity
  latentPrior_nonneg _ _ := by positivity

-- Lower-bound alternative set predictions

/-- Class B competition at boundary: at w=3, "bare 3" beats "at least 3" in L1.
    The speaker who knew exactly 3 would use "bare 3" (more informative), so
    a listener hearing "at least 3" infers w≥4 is more likely. -/
theorem classB_competition_at_boundary :
    kennedyLowerCfg.L1 .bare3 .c3 > kennedyLowerCfg.L1 .atLeast3 .c3 := by rsa_predict

/-- Class A excludes the boundary: "more than 3" is false at w=3, so
    L1(w=4 | "more than 3") > L1(w=3 | "more than 3"). -/
theorem classA_no_competition_at_boundary :
    kennedyLowerCfg.L1 .moreThan3 .c4 > kennedyLowerCfg.L1 .moreThan3 .c3 := by rsa_predict

/-- Bare numeral is peaked: L1("bare 3", w=3) > L1("bare 3", w=4).
    Under exact semantics, "bare 3" is only true at w=3. -/
theorem bare_peaked_with_kennedy_alternatives :
    kennedyLowerCfg.L1 .bare3 .c3 > kennedyLowerCfg.L1 .bare3 .c4 := by rsa_predict

/-- Class B strengthened above bare: L1("at least 3", w=4) > L1("at least 3", w=3).
    The pragmatic listener hearing "at least 3" infers the speaker didn't know
    exactly 3 (ignorance implicature pushes probability above the boundary). -/
theorem classB_strengthened_above_bare :
    kennedyLowerCfg.L1 .atLeast3 .c4 > kennedyLowerCfg.L1 .atLeast3 .c3 := by rsa_predict

-- Upper-bound alternative set predictions

/-- Upper Class B competition: at w=3, "bare 3" beats "at most 3" in L1. -/
theorem upper_classB_competition :
    kennedyUpperCfg.L1 .bare3 .c3 > kennedyUpperCfg.L1 .atMost3 .c3 := by rsa_predict

/-- Upper Class A excludes the boundary: "fewer than 3" is false at w=3. -/
theorem upper_classA_no_competition :
    kennedyUpperCfg.L1 .fewerThan3 .c2 > kennedyUpperCfg.L1 .fewerThan3 .c3 := by rsa_predict

/-- Upper Class B strengthened below bare: L1("at most 3", w=2) > L1("at most 3", w=3).
    Hearing "at most 3" pushes probability below the boundary (ignorance). -/
theorem upper_classB_strengthened_below_bare :
    kennedyUpperCfg.L1 .atMost3 .c2 > kennedyUpperCfg.L1 .atMost3 .c3 := by rsa_predict

-- Grounding: inlined meanings agree with maxMeaning

/-- Lower Kennedy meanings agree with `maxMeaning`. -/
theorem kLowerMeaning_eq_maxMeaning (u : KLowerUtt) (w : KCard) :
    kLowerMeaning u w = match u with
      | .bare3 => maxMeaning .eq 3 w.toNat
      | .moreThan3 => maxMeaning .gt 3 w.toNat
      | .atLeast3 => maxMeaning .ge 3 w.toNat := by
  cases u <;> cases w <;> native_decide

/-- Upper Kennedy meanings agree with `maxMeaning`. -/
theorem kUpperMeaning_eq_maxMeaning (u : KUpperUtt) (w : KCard) :
    kUpperMeaning u w = match u with
      | .bare3 => maxMeaning .eq 3 w.toNat
      | .fewerThan3 => maxMeaning .lt 3 w.toNat
      | .atMost3 => maxMeaning .le 3 w.toNat := by
  cases u <;> cases w <;> native_decide

end Bridge10

end Phenomena.Numerals.Compare
