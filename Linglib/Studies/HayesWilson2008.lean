import Linglib.Phonology.HarmonicGrammar.OTLimit
import Linglib.Phonology.HarmonicGrammar.MaxEnt
import Linglib.Phonology.Constraints.Basic
import Linglib.Phonology.OptimalityTheory.Basic
import Linglib.Phonology.Subregular.LocalRewrite
import Linglib.Fragments.English.Phonology

/-!
# [hayes-wilson-2008]: A Maximum Entropy Model of Phonotactics
[hayes-wilson-2008]

[hayes-wilson-2008] propose that phonotactic well-formedness is
probability: a MaxEnt grammar assigns each surface form a score
`h(x) = Σ wⱼ · Cⱼ(x)`, and well-formedness is `P(x) = exp(−h(x)) / Z`.

Hayes & Wilson's "score" is the negation of `harmonyScore`:
`h(x) = −harmonyScore(x)`, so `P(x) ∝ exp(harmonyScore(x))`.
Higher harmony = higher probability = better well-formedness.
This is exactly `softmax(harmonyScore, 1)` on a finite candidate set.

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

namespace HayesWilson2008

open Phonology Core.Optimization Constraints HarmonicGrammar OptimalityTheory
open Core Core.Optimization Constraints OptimalityTheory Finset Real

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
noncomputable def c1_star_son_dors : Constraint.Weighted Onset :=
  { con := fun onset => onset.countP (matchesPat · son_dors_pat), weight := 564/100 }

/-- Bool helper for `c4_star_blank_cont`. -/
private def c4_violated : Onset → Bool
  | _ :: c₂ :: _ => matchesPat c₂ continuant_pat
  | _ => false

/-- Constraint #4 from Table (4): *[ ][+continuant]. Weight 5.17. -/
noncomputable def c4_star_blank_cont : Constraint.Weighted Onset :=
  Constraint.Weighted.binary (fun o => c4_violated o = true) (517/100)

/-- Bool helper for `c5_star_blank_voice`. -/
private def c5_violated : Onset → Bool
  | _ :: c₂ :: _ => matchesPat c₂ voice_pat && !matchesPat c₂ sonorant_pat
  | _ => false

/-- Constraint #5 from Table (4): *[ ][+voice, −sonorant]. Weight 5.37. -/
noncomputable def c5_star_blank_voice : Constraint.Weighted Onset :=
  Constraint.Weighted.binary (fun o => c5_violated o = true) (537/100)

/-- Bool helper for `c6_star_son_blank`. -/
private def c6_violated : Onset → Bool
  | c₁ :: _ :: _ => matchesPat c₁ sonorant_pat
  | _ => false

/-- Constraint #6 from Table (4): *[+sonorant][ ]. Weight 6.66. -/
noncomputable def c6_star_son_blank : Constraint.Weighted Onset :=
  Constraint.Weighted.binary (fun o => c6_violated o = true) (666/100)

/-- The subset grammar: 4 constraints from Table (4). -/
noncomputable def onsetGrammar : List (Constraint.Weighted Onset) :=
  [c1_star_son_dors, c4_star_blank_cont, c5_star_blank_voice, c6_star_son_blank]

-- ============================================================================
-- § 2: Harmony Predictions (using harmonyScore from Constraints.Defs)
-- ============================================================================

open English.Phonology in
/-- Attested [k] (no violations) has higher harmony than unattested *[ŋ]
    (violates *[+son,+dors], cost 5.64). The harmony *magnitude* is a weight
    artifact; the *ranking* is the empirical prediction. -/
theorem attested_higher_harmony_k_ŋ :
    harmonyScore onsetGrammar [ŋ] < harmonyScore onsetGrammar [k] := by
  rw [harmonyScore_eq_neg_sum, harmonyScore_eq_neg_sum, neg_lt_neg_iff]
  simp +decide only [onsetGrammar, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, c1_star_son_dors, c4_star_blank_cont, c5_star_blank_voice,
    c6_star_son_blank, Constraint.Weighted.binary, Constraint.binary, c4_violated,
    c5_violated, c6_violated, matchesPat, List.countP_cons, List.countP_nil]
  norm_num

open English.Phonology in
/-- Attested [br] has higher harmony than unattested *[rk] (violates *[+son][ ]). -/
theorem attested_higher_harmony_br_rk :
    harmonyScore onsetGrammar [r, k] < harmonyScore onsetGrammar [b, r] := by
  rw [harmonyScore_eq_neg_sum, harmonyScore_eq_neg_sum, neg_lt_neg_iff]
  simp +decide only [onsetGrammar, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, c1_star_son_dors, c4_star_blank_cont, c5_star_blank_voice,
    c6_star_son_blank, Constraint.Weighted.binary, Constraint.binary, c4_violated,
    c5_violated, c6_violated, matchesPat, List.countP_cons, List.countP_nil]
  norm_num

-- ============================================================================
-- § 3: MaxEnt Probability Ordering (using exp_lt_exp from Mathlib)
-- ============================================================================

section MaxEntProb
open English.Phonology

/-- Gradient: among unattested onsets, *[ŋ] has higher harmony than *[rk]. -/
theorem gradient_harmony_ŋ_rk :
    harmonyScore onsetGrammar [r, k] < harmonyScore onsetGrammar [ŋ] := by
  rw [harmonyScore_eq_neg_sum, harmonyScore_eq_neg_sum, neg_lt_neg_iff]
  simp +decide only [onsetGrammar, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, c1_star_son_dors, c4_star_blank_cont, c5_star_blank_voice,
    c6_star_son_blank, Constraint.Weighted.binary, Constraint.binary, c4_violated,
    c5_violated, c6_violated, matchesPat, List.countP_cons, List.countP_nil]
  norm_num

/-- **MaxEnt probability ordering**: higher harmony ⟹ higher `exp(harmonyScore)`
    ⟹ higher MaxEnt probability. Applies `exp_lt_exp` to `harmonyScore`. -/
theorem maxent_prob_k_gt_ŋ :
    exp (harmonyScore onsetGrammar [ŋ]) < exp (harmonyScore onsetGrammar [k]) :=
  exp_lt_exp.mpr attested_higher_harmony_k_ŋ

/-- **Gradient well-formedness**: among unattested forms, *[ŋ] has higher MaxEnt
    probability than *[rk]. -/
theorem gradient_prob_ŋ_gt_rk :
    exp (harmonyScore onsetGrammar [r, k]) < exp (harmonyScore onsetGrammar [ŋ]) :=
  exp_lt_exp.mpr gradient_harmony_ŋ_rk

end MaxEntProb

-- ============================================================================
-- § 4: Generic ConstraintSystem Predictions
-- ============================================================================

/-! Phonological MaxEnt is one instance of the framework-agnostic
`ConstraintSystem` abstraction in `Constraints.System`. The same
`maxEntSystem` constructor that scores phonological onsets here also
scores syntactic candidates in HG/MaxEnt syntax models, RSA utterances
in soft-max pragmatic listeners, etc. The decoder (`softmaxDecoder 1`)
is what makes this MaxEnt rather than HG (`argmaxDecoder`) or OT
(`argminDecoder` over a `LexProfile`).

This section eats the dog food: rather than comparing
`exp(harmonyScore ...)` directly (as in §3), we go through
`ConstraintSystem.predict`. -/

section PredictAPI
open English.Phonology

/-- The four onsets used as MaxEnt candidates: two attested ([k], [b,r])
    and two unattested (*[ŋ], *[r,k]). -/
def candidateOnsets : Finset Onset :=
  ({[k], [ŋ], [r, k], [b, r]} : Finset Onset)

/-- [hayes-wilson-2008]'s grammar realised as a generic
    `ConstraintSystem` over `candidateOnsets`, decoded by softmax at
    temperature 1. The score component is `harmonyScore onsetGrammar`
    (the canonical MaxEnt harmony function). -/
noncomputable def onsetSystem : ConstraintSystem Onset ℝ :=
  maxEntSystem candidateOnsets onsetGrammar

/-- The system literally predicts a higher MaxEnt probability for [k]
    than for *[ŋ]. Unlike `maxent_prob_k_gt_ŋ`, this is a comparison of
    actual softmax probabilities (numerator / partition function), not
    just exponentiated harmony scores — so the partition function over
    `candidateOnsets` is part of the claim. -/
theorem predict_k_gt_ŋ :
    onsetSystem.predict [ŋ] < onsetSystem.predict [k] :=
  ConstraintSystem.predict_softmax_lt_of_score_lt _ one_pos rfl
    (by decide) (by decide) attested_higher_harmony_k_ŋ

/-- The system also predicts a higher MaxEnt probability for *[ŋ] than
    for *[rk] — gradient well-formedness among unattested forms. -/
theorem predict_ŋ_gt_rk :
    onsetSystem.predict [r, k] < onsetSystem.predict [ŋ] :=
  ConstraintSystem.predict_softmax_lt_of_score_lt _ one_pos rfl
    (by decide) (by decide) gradient_harmony_ŋ_rk

/-- The MaxEnt softmax decoder is a probability decoder, so the system's
    predictions are non-negative and sum to 1 over the candidate set.
    Follows from `Decoder.IsProb.sum_eq_one` for `softmaxDecoder`. -/
theorem onsetSystem_isProb :
    ∑ c ∈ candidateOnsets, onsetSystem.predict c = 1 :=
  ConstraintSystem.predict_softmax_isProb _ rfl ⟨[k], by decide⟩

end PredictAPI

end HayesWilson2008
