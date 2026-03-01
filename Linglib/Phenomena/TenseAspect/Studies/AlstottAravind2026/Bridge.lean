import Linglib.Phenomena.TenseAspect.Studies.AlstottAravind2026.Data
import Linglib.Theories.Semantics.Tense.TemporalConnectives.Rett
import Linglib.Fragments.English.TemporalExpressions
import Linglib.Fragments.Tagalog.TemporalConnectives
import Linglib.Fragments.Serbian.TemporalConnectives

/-!
# Alstott & Aravind (2026): Bridge File
@cite{alstott-aravind-2026} @cite{rett-2020}

Connects the experimental data in `Data.lean` to Rett's (2020) INCHOAT/COMPLET
operators and the English/Tagalog/Serbian temporal connective fragments.

## Key Connections

1. **Exp 2** (before-clause + COMPLET): tests the coerced reading of English
   *before* — `before_.coercedReading = some .beforeFinish` — which requires
   COMPLET to extract the telos of a telic embedded event.

2. **Exp 4** (after-clause + INCHOAT): tests the coerced reading of English
   *after* — `after_.coercedReading = some .afterStart` — which requires
   INCHOAT to extract the onset of an atelic embedded event.

3. **Exp 1b** (at-modifier + COMPLET): tests COMPLET triggered by the
   temporal modifier *at* — `at_punct.triggeredCoercion = some "COMPLET"`.

4. **Cross-linguistic**: Tagalog PFV.NEUT/AIA and Serbian PFV/IMPF overtly
   mark the same distinction that English encodes covertly and Alstott &
   Aravind measure as processing cost.

-/

namespace Phenomena.TenseAspect.Studies.AlstottAravind2026

open Fragments.English.TemporalExpressions

-- ============================================================================
-- § 1: Fragment–Experiment Connection
-- ============================================================================

/-- Exp 2 tests *before*'s coerced reading: the COMPLET-derived before-finish
    interpretation. The experiment uses accomplishment EEs in before-clauses,
    which require COMPLET to yield the "before she finished climbing" reading. -/
theorem exp2_tests_before_coercion :
    exp2_rt.coercionType = .completive ∧
    before_.coercedReading = some .beforeFinish :=
  ⟨rfl, rfl⟩

/-- Exp 4 tests *after*'s coerced reading: the INCHOAT-derived after-start
    interpretation. The experiment uses stative/activity EEs in after-clauses,
    which require INCHOAT to yield the "after she started being president"
    reading. -/
theorem exp4_tests_after_coercion :
    exp4_rt.coercionType = .inchoative ∧
    after_.coercedReading = some .afterStart :=
  ⟨rfl, rfl⟩

/-- Exp 1b tests COMPLET triggered by the *at* temporal modifier.
    "At 7 o'clock" forces a punctual reading of an accomplishment VP,
    requiring COMPLET to extract the telos. -/
theorem exp1b_tests_at_modifier_coercion :
    exp1b_rt.coercionType = .completive ∧
    at_punct.triggeredCoercion = some "COMPLET" :=
  ⟨rfl, rfl⟩

/-- Exps 1a/3 test INCHOAT triggered by the *within* temporal modifier.
    These fail to replicate Brennan & Pylkkänen (2010). -/
theorem exp1a_tests_within_modifier_coercion :
    exp1a_rt.coercionType = .inchoative ∧
    within_.triggeredCoercion = some "INCHOAT" :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 2: Coercion–Cost Correspondence
-- ============================================================================

/-- All COMPLET experiments show significant processing cost.
    This is the strongest result: completive coercion is reliably costly
    across both connective (Exp 2) and modifier (Exp 1b) constructions. -/
theorem complet_consistently_costly :
    exp1b_rt.significant = true ∧
    exp2_rt.significant = true ∧
    exp1b_rt.coercionType = .completive ∧
    exp2_rt.coercionType = .completive :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- INCHOAT cost is construction-specific: significant in temporal connective
    contexts (Exp 4, after-clause) but null in modifier contexts
    (Exps 1a, 3, within-modifier).

    This dissociation suggests that INCHOAT processing cost depends on the
    syntactic environment, not just the semantic operation. -/
theorem inchoat_construction_specific :
    exp4_rt.significant = true ∧
    exp1a_rt.significant = false ∧
    exp3_rt.significant = false ∧
    exp4_rt.coercionType = .inchoative ∧
    exp1a_rt.coercionType = .inchoative ∧
    exp3_rt.coercionType = .inchoative :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The positive COMPLET RT effects are greater than the null INCHOAT effects.
    Exp 1b: β = 0.033 (COMPLET, significant)
    Exp 1a: β = -0.023 (INCHOAT, not significant)
    The COMPLET slowdown is numerically in the expected direction while the
    INCHOAT effect is actually negative (faster, not slower). -/
theorem complet_effect_exceeds_inchoat :
    exp1b_rt.effectBeta > exp1a_rt.effectBeta :=
  by native_decide

-- ============================================================================
-- § 3: Naturalness Convergence
-- ============================================================================

/-- RT and naturalness measures converge: all experiments that show significant
    RT effects also show significant naturalness decreases, and vice versa. -/
theorem rt_naturalness_converge :
    (exp1b_rt.significant = exp1b_naturalness.significant) ∧
    (exp2_rt.significant = exp2_naturalness.significant) ∧
    (exp4_rt.significant = exp4_naturalness.significant) ∧
    (exp1a_rt.significant = exp1a_naturalness.significant) ∧
    (exp3_rt.significant = exp3_naturalness.significant) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 4: Cross-Linguistic Evidence
-- ============================================================================

/-- Tagalog overtly marks the same COMPLET/INCHOAT distinction.
    AIA (culminating) corresponds to COMPLET; PFV.NEUT (non-culminating)
    corresponds to INCHOAT. The Tagalog morphological contrast directly
    supports Rett's positing of covert operators in English. -/
theorem tagalog_overt_coercion :
    Fragments.Tagalog.TemporalConnectives.bago_aia.culminating = true ∧
    Fragments.Tagalog.TemporalConnectives.bago_aia.reading = .beforeFinish ∧
    Fragments.Tagalog.TemporalConnectives.bago_neut.culminating = false ∧
    Fragments.Tagalog.TemporalConnectives.bago_neut.reading = .beforeStart :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Serbian PFV/IMPF marks the same distinction as Tagalog PFV.NEUT/AIA.
    Both languages provide morphological evidence for Rett's coercion operators;
    Alstott & Aravind's processing data provides psycholinguistic evidence. -/
theorem serbian_overt_coercion :
    Fragments.Serbian.TemporalConnectives.pre_pfv.culminating = true ∧
    Fragments.Serbian.TemporalConnectives.pre_pfv.reading = .beforeFinish ∧
    Fragments.Serbian.TemporalConnectives.pre_impf.culminating = false ∧
    Fragments.Serbian.TemporalConnectives.pre_impf.reading = .beforeStart :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Three independent evidence types converge on Rett's COMPLET operator:
    1. English processing cost (Exp 2: before-clause COMPLET is costly)
    2. Tagalog morphology (AIA marks COMPLET overtly)
    3. Serbian morphology (PFV marks COMPLET overtly) -/
theorem complet_triple_convergence :
    exp2_rt.significant = true ∧
    exp2_rt.coercionType = .completive ∧
    Fragments.Tagalog.TemporalConnectives.bago_aia.culminating = true ∧
    Fragments.Serbian.TemporalConnectives.pre_pfv.culminating = true :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 5: Spillover Patterns
-- ============================================================================

/-- Temporal connective coercion (Exps 2, 4) shows later spillover (verb+2)
    than modifier coercion (Exp 1b: verb+1). This may reflect the additional
    structural complexity of clausal vs NP complements. -/
theorem connective_later_spillover :
    exp2_rt.region = .verbPlus2 ∧
    exp4_rt.region = .verbPlus2 ∧
    exp1b_rt.region = .verbPlus1 :=
  ⟨rfl, rfl, rfl⟩

end Phenomena.TenseAspect.Studies.AlstottAravind2026
