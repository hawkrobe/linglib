import Linglib.Core.Roundness
import Linglib.Theories.RSA.Core.Eval
import Linglib.Phenomena.NumberUse.WoodinEtAl2024
import Linglib.Theories.TruthConditional.Numeral.Precision
import Linglib.Theories.NeoGricean.Constraints.NumericalExpressions
import Linglib.Fragments.English.NumeralModifiers
import Linglib.Phenomena.NumeralModification.ClausWalch2024
import Linglib.Theories.TruthConditional.Numeral.Semantics
import Mathlib.Data.Rat.Defs

/-!
# Bridge Theorems: Numeral Salience across Frameworks

Connects the graded roundness model (k-ness) to five existing modules:

1. **NSAL ↔ RSA cost**: OT NSAL violations as normalized RSA utterance cost
2. **Woodin frequency ↔ RSA prior**: weighted roundness as utterance prior
3. **k-ness ↔ PrecisionMode**: roundness score grounds Kao et al.'s binary switch
4. **k-ness ↔ NumeralModifiers**: tolerance modifiers pair with high roundness
5. **k-ness ↔ C&F enrichment**: wider enrichment for rounder numerals
6. **OT ↔ RSA parameter map**: constraint-to-parameter correspondence
7. **Evaluative valence ↔ framing**: Claus & Walch (2024) framing predictions

## Architecture

```
Phenomena.Imprecision.Numerals (k-ness core)
    ↑              ↑                ↑
    |              |                |
Phenomena.        NeoGricean.       TruthConditional.
NumberUse.        Constraints.      Domain.Degree
WoodinEtAl2024    NumericalExprs    (extended)
    ↑              ↑                ↑
    +--------------+-------+--------+
                           |
               Comparisons.NumeralSalience (this file)
```

## References

- Cummins (2015). Constraints on numerical expressions.
- Woodin, Winter & Bhatt (2024). Numeral frequency and roundness.
- Kao et al. (2014). Nonliteral understanding of number words.
- Cummins & Franke (2021). Approximate number word use.
- Lasersohn (1999). Pragmatic halos.
- Claus & Walch (2024). Evaluative valence distinguishes at most from up to.
- Blok (2015). The semantics and pragmatics of directional numeral modifiers.
-/

namespace Comparisons.NumeralSalience

open Core.Roundness
open Phenomena.NumberUse.WoodinEtAl2024
open NeoGricean.Constraints.NumericalExpressions
open TruthConditional.Numeral.Precision
open Core.Scale (HasDegree)

-- ============================================================================
-- Bridge 1: NSAL ↔ RSA cost
-- ============================================================================

/-!
### NSAL as RSA Utterance Cost

In RSA, `cost : U → ℚ` penalizes certain utterances. The OT constraint NSAL
provides a principled grounding: cost(u) = nsalViolations(u) / 6.

Round numerals (100, 1000) have cost ≈ 0; non-round (7, 99) have cost ≈ 1.
This connects Cummins (2015)'s constraint-based account to the Bayesian RSA
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
### Roundness Grounds Precision Mode

Kao et al. (2014) use a binary `PrecisionMode` (.exact/.approximate) with
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
    if n is round (divisible by 10), inferPrecisionMode gives .approximate. -/
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

Cummins & Franke (2021) show that "more than M" undergoes pragmatic enrichment
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
-- Bridge 7: Evaluative Valence → Framing Prediction (Claus & Walch 2024)
-- ============================================================================

/-!
### Evaluative Valence Predicts Framing Direction

Claus & Walch (2024) show that "at most" and "up to" have the same truth
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
open Phenomena.NumeralModification.ClausWalch2024

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

open TruthConditional.Numeral
open TruthConditional.Numeral.Precision
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

/-- Exact bare numeral meaning equals degree equality (Bylinina & Nouwen 2020 §4). -/
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
-- Bridge 9: NumeralTheory ↔ RSA L1 (moved from Semantics.lean)
-- ============================================================================

section Bridge9

open TruthConditional.Numeral

/-- Run L1 for a numeral theory using RSA.Eval.

This is the cross-theory bridge connecting truth-conditional numeral semantics
(`NumeralTheory.meaning`) to RSA pragmatic inference (`RSA.Eval.basicL1`). -/
def NumeralTheory.runL1 (T : NumeralTheory) (w : BareNumeral) : List (Nat × ℚ) :=
  RSA.Eval.basicL1 T.utterances T.worlds
    (λ u n => boolToRat (T.meaning u n)) (λ _ => 1) 1 (λ _ => 0) w

end Bridge9

-- ============================================================================
-- Bridge 10: Kennedy Alternative Sets ↔ RSA
-- ============================================================================

/-!
### Kennedy Alternatives through RSA

Kennedy (2015) argues that numeral alternatives are NOT the traditional Horn
scale ⟨1, 2, 3, ...⟩ but rather sets organized by modifier class:

- Lower alternatives for n: `{bare n, more than n, at least n}`
- Upper alternatives for n: `{bare n, fewer than n, at most n}`

Class A (strict: >, <) and Class B (non-strict: ≥, ≤) have different
pragmatic behavior because of their structural relationship to bare numerals:

- Class B overlaps with bare → competes → gets pragmatically strengthened
- Class A is disjoint from bare → complementary → no competition

We connect these alternatives directly to RSA, deriving the pragmatic
properties from `maxMeaning` rather than hand-rolled truth tables.
-/

section Bridge10

open TruthConditional.Numeral

/-- Extended worlds for modified numeral RSA (0 through 5). -/
def kennedyWorlds : List Nat := [0, 1, 2, 3, 4, 5]

/-- Run L1 over Kennedy's lower alternatives for numeral n.

Uses `NumeralAlternative.meaning` (derived from `maxMeaning`) as the
semantic function, with Kennedy's structured alternative set `{bare n, >n, ≥n}`. -/
def kennedyLowerL1 (n : Nat) (alt : NumeralAlternative) : List (Nat × ℚ) :=
  RSA.Eval.basicL1 (lowerAlternatives n) kennedyWorlds
    (λ u w => boolToRat (u.meaning w)) (λ _ => 1) 1 (λ _ => 0) alt

/-- Run L1 over Kennedy's upper alternatives for numeral n. -/
def kennedyUpperL1 (n : Nat) (alt : NumeralAlternative) : List (Nat × ℚ) :=
  RSA.Eval.basicL1 (upperAlternatives n) kennedyWorlds
    (λ u w => boolToRat (u.meaning w)) (λ _ => 1) 1 (λ _ => 0) alt

/-- Helper: extract the score for a specific world from an L1 distribution. -/
def scoreAt (dist : List (Nat × ℚ)) (w : Nat) : ℚ :=
  match dist.find? (·.1 == w) with
  | some (_, p) => p
  | none => 0

-- Class A vs Class B: the key asymmetry

/-- Class B "at least 3" competes with "bare 3" at world 3.

Both are true at w=3, so RSA pragmatic competition means L1 hearing "at least 3"
shifts probability AWAY from w=3 (because the speaker would have said "bare 3"
if they meant exactly 3). This is Kennedy's explanation of why "at least" implies
speaker uncertainty. -/
theorem classB_competition_at_boundary :
    -- L1 hearing "bare 3": assigns high probability to w=3
    scoreAt (kennedyLowerL1 3 (.bare 3)) 3 >
    -- L1 hearing "at least 3": assigns lower probability to w=3
    scoreAt (kennedyLowerL1 3 (.modified .ge 3)) 3 := by native_decide

/-- Class A "more than 3" does NOT compete with "bare 3" at w=3.

"More than 3" is false at w=3, so there's no competition with "bare 3".
L1 hearing "more than 3" distributes over {4, 5, ...} without needing to
consider the bare alternative at w=3. -/
theorem classA_no_competition_at_boundary :
    -- "more than 3" assigns 0 probability to w=3
    scoreAt (kennedyLowerL1 3 (.modified .gt 3)) 3 = 0 := by native_decide

/-- "Bare 3" through Kennedy alternatives: L1 assigns all mass to w=3.

With Kennedy alternatives (not just the numeral scale), the bare numeral
is maximally informative for its exact world. -/
theorem bare_peaked_with_kennedy_alternatives :
    scoreAt (kennedyLowerL1 3 (.bare 3)) 3 = 1 := by native_decide

/-- Class B "at least 3" gets pragmatically strengthened: L1 infers w > 3.

Because "bare 3" would have been used for w=3, L1 hearing "at least 3"
infers higher worlds. The probability of w=4 exceeds w=3. -/
theorem classB_strengthened_above_bare :
    scoreAt (kennedyLowerL1 3 (.modified .ge 3)) 4 >
    scoreAt (kennedyLowerL1 3 (.modified .ge 3)) 3 := by native_decide

-- Upper alternatives mirror

/-- Upper Class B "at most 3" competes with "bare 3" at boundary. -/
theorem upper_classB_competition :
    scoreAt (kennedyUpperL1 3 (.bare 3)) 3 >
    scoreAt (kennedyUpperL1 3 (.modified .le 3)) 3 := by native_decide

/-- Upper Class A "fewer than 3" assigns 0 to w=3. -/
theorem upper_classA_no_competition :
    scoreAt (kennedyUpperL1 3 (.modified .lt 3)) 3 = 0 := by native_decide

/-- Upper Class B "at most 3" strengthened below: L1 infers w < 3. -/
theorem upper_classB_strengthened_below_bare :
    scoreAt (kennedyUpperL1 3 (.modified .le 3)) 2 >
    scoreAt (kennedyUpperL1 3 (.modified .le 3)) 3 := by native_decide

end Bridge10

end Comparisons.NumeralSalience
