import Linglib.Theories.Phonology.HarmonicGrammar.OTLimit
import Linglib.Theories.Phonology.Constraints
import Linglib.Theories.Phonology.RuleBased.Defs
import Linglib.Fragments.English.Phonology

/-!
# @cite{hayes-wilson-2008}: A Maximum Entropy Model of Phonotactics
@cite{hayes-wilson-2008}

@cite{hayes-wilson-2008} propose that phonotactic well-formedness is
probability: a MaxEnt grammar assigns each surface form a score
`h(x) = Σ wⱼ · Cⱼ(x)`, and well-formedness is `P(x) = exp(−h(x)) / Z`.

Hayes & Wilson's "score" is the negation of `harmonyScore`:
`h(x) = −harmonyScore(x)`, so `P(x) ∝ exp(harmonyScore(x))`.
Higher harmony = higher probability = better well-formedness.
This is exactly `softmax(harmonyScoreR, 1)` on a finite candidate set.

## Key contribution: ganging

The central empirical prediction distinguishing MaxEnt from OT is
**ganging**: two individually weak constraints can jointly override
a stronger one. This is impossible with OT's strict ranking, which
corresponds to exponentially separated weights (`OTLimit.lean`).

The `Ganging` definition and anti-ganging theorems live in `OTLimit.lean`
alongside `ExponentiallySeparated`, since they are two sides of the same
coin.

## English onset data

We encode a subset of the learned grammar (Table (4)) and verify that
the model assigns higher harmony (= higher MaxEnt probability via
`exp_lt_exp`) to attested onsets than to unattested ones (§2).
-/

namespace Phenomena.Phonotactics.Studies.HayesWilson2008

open Theories.Phonology Theories.Phonology.HarmonicGrammar Theories.Phonology.Constraints
open Core Core.OT Finset Real

-- ============================================================================
-- § 1: English Onset Constraints (Table (4) subset)
-- ============================================================================

/-- An English onset: a list of consonants preceding the nucleus. -/
abbrev Onset := List Segment

-- Natural class patterns used in the learned grammar.

private def sonorant_pat : Segment :=
  Segment.ofSpecs [(Feature.sonorant, true)]

private def voice_pat : Segment :=
  Segment.ofSpecs [(Feature.voice, true)]

private def continuant_pat : Segment :=
  Segment.ofSpecs [(Feature.continuant, true)]

private def son_dors_pat : Segment :=
  Segment.ofSpecs [(Feature.sonorant, true), (Feature.dorsal, true)]

private def matchesPat (s : Segment) (p : Segment) : Bool :=
  s.matchesPattern p

/-- Constraint #1 from Table (4): *[+sonorant, +dorsal]. Weight 5.64. -/
def c1_star_son_dors : WeightedConstraint Onset :=
  mkMarkGradW "*[+son,+dors]" (fun onset => onset.countP (matchesPat · son_dors_pat)) (564/100)

/-- Constraint #4 from Table (4): *[ ][+continuant]. Weight 5.17. -/
def c4_star_blank_cont : WeightedConstraint Onset :=
  mkMarkW "*[ ][+cont]" (fun onset => match onset with
    | _ :: c₂ :: _ => matchesPat c₂ continuant_pat | _ => false) (517/100)

/-- Constraint #5 from Table (4): *[ ][+voice, −sonorant]. Weight 5.37. -/
def c5_star_blank_voice : WeightedConstraint Onset :=
  mkMarkW "*[ ][+voice]" (fun onset => match onset with
    | _ :: c₂ :: _ => matchesPat c₂ voice_pat && !matchesPat c₂ sonorant_pat
    | _ => false) (537/100)

/-- Constraint #6 from Table (4): *[+sonorant][ ]. Weight 6.66. -/
def c6_star_son_blank : WeightedConstraint Onset :=
  mkMarkW "*[+son][ ]" (fun onset => match onset with
    | c₁ :: _ :: _ => matchesPat c₁ sonorant_pat | _ => false) (666/100)

/-- The subset grammar: 4 constraints from Table (4). -/
def onsetGrammar : List (WeightedConstraint Onset) :=
  [c1_star_son_dors, c4_star_blank_cont, c5_star_blank_voice, c6_star_son_blank]

-- ============================================================================
-- § 2: Harmony Predictions (using harmonyScore from HarmonicGrammar.Basic)
-- ============================================================================

open Fragments.English.Phonology in
/-- Attested onset [k]: harmony = 0 (no violations). -/
theorem k_harmony : harmonyScore onsetGrammar [k] = 0 := by native_decide

open Fragments.English.Phonology in
/-- Unattested onset *[ŋ]: harmony = −5.64 (violates *[+son,+dors]). -/
theorem ŋ_harmony : harmonyScore onsetGrammar [ŋ] = -(564/100) := by native_decide

open Fragments.English.Phonology in
/-- Unattested onset *[rk]: harmony = −6.66 (violates *[+son][ ]). -/
theorem rk_harmony : harmonyScore onsetGrammar [r, k] = -(666/100) := by native_decide

open Fragments.English.Phonology in
/-- Attested [k] has higher harmony than unattested *[ŋ]. -/
theorem attested_higher_harmony_k_ŋ :
    harmonyScore onsetGrammar [ŋ] < harmonyScore onsetGrammar [k] := by native_decide

open Fragments.English.Phonology in
/-- Attested [br] has higher harmony than unattested *[rk]. -/
theorem attested_higher_harmony_br_rk :
    harmonyScore onsetGrammar [r, k] < harmonyScore onsetGrammar [b, r] := by native_decide

-- ============================================================================
-- § 3: MaxEnt Probability Ordering (using exp_lt_exp from Mathlib)
-- ============================================================================

section MaxEntProb
open Fragments.English.Phonology

/-- **MaxEnt probability ordering**: higher harmony ⟹ higher
    `exp(harmonyScore)` ⟹ higher MaxEnt probability.

    Applies `exp_lt_exp` (Mathlib) to `harmonyScoreR` (HarmonicGrammar.Basic). -/
theorem maxent_prob_k_gt_ŋ :
    exp (harmonyScoreR onsetGrammar [ŋ]) <
    exp (harmonyScoreR onsetGrammar [k]) := by
  apply exp_lt_exp.mpr
  show (harmonyScore onsetGrammar [ŋ] : ℝ) < (harmonyScore onsetGrammar [k] : ℝ)
  exact_mod_cast attested_higher_harmony_k_ŋ

/-- **Gradient well-formedness**: among unattested forms, *[ŋ]
    has higher MaxEnt probability than *[rk]. Uses `exp_lt_exp`. -/
theorem gradient_prob_ŋ_gt_rk :
    exp (harmonyScoreR onsetGrammar [r, k]) <
    exp (harmonyScoreR onsetGrammar [ŋ]) := by
  apply exp_lt_exp.mpr
  show (harmonyScore onsetGrammar [r, k] : ℝ) < (harmonyScore onsetGrammar [ŋ] : ℝ)
  exact_mod_cast (by native_decide : harmonyScore onsetGrammar [r, k] < harmonyScore onsetGrammar [ŋ])

end MaxEntProb

end Phenomena.Phonotactics.Studies.HayesWilson2008
