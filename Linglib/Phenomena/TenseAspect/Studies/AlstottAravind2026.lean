import Linglib.Core.Empirical
import Linglib.Fragments.English.TemporalExpressions
import Linglib.Theories.Semantics.Tense.TemporalConnectives.Rett
import Linglib.Fragments.Tagalog.TemporalConnectives
import Linglib.Fragments.Serbian.TemporalConnectives

open Core.Empirical

/-!
# @cite{alstott-aravind-2026}: Aspectual Coercion in *before*/*after*-Clauses
@cite{alstott-aravind-2026} @cite{rett-2020}

Self-paced reading data from 4 experiments testing @cite{rett-2020}'s prediction
that aspectual coercion (INCHOAT, COMPLET) incurs measurable processing cost.

## Results Summary

| Exp | Coercion type | RT effect | Naturalness | Supports Rett? |
|-----|--------------|-----------|-------------|----------------|
| 1a  | INCHOAT (within-modifier) | null | null | No |
| 1b  | COMPLET (at-modifier) | **sig** verb+1 | **sig** lower | Yes |
| 2   | COMPLET (before-clause) | **sig** verb+2 | **sig** lower | Yes |
| 3   | INCHOAT (subj-experiencer) | null | null | No |
| 4   | INCHOAT (after-clause) | **sig** verb+2 | **sig** lower | Yes |

Key findings:
- Completive coercion consistently shows processing cost (Exps 1b, 2)
- Inchoative coercion in *after*-clauses shows delayed cost (Exp 4)
- Inchoative coercion in *within*-modifier contexts fails to replicate
  @cite{brennan-pylkkanen-2008} (Exps 1a, 3)
- Complement coercion (sanity check) replicates across all experiments

-/

namespace Phenomena.TenseAspect.Studies.AlstottAravind2026

open Phenomena

-- ============================================================================
-- § 1: Types
-- ============================================================================

/-- Experiment identifiers. Exp 1 has two sub-experiments (a and b). -/
inductive Experiment where
  | exp1a  -- within-modifier + activity (inchoative)
  | exp1b  -- at-modifier + accomplishment (completive)
  | exp2   -- before-clause + accomplishment (completive)
  | exp3   -- subject-experiencer verb (inchoative)
  | exp4   -- after-clause + stative (inchoative)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Types of aspectual coercion tested across experiments. -/
inductive CoercionType where
  | inchoative   -- INCHOAT: atelic → onset point (GLB)
  | completive   -- COMPLET: telic → telos point (LUB)
  | complement   -- Complement coercion (sanity check; @cite{traxler-etal-2002})
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Spillover region where an effect was measured. -/
inductive SpilloverRegion where
  | verb      -- at the critical verb
  | verbPlus1 -- one word after verb
  | verbPlus2 -- two words after verb
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Result from a self-paced reading experiment. -/
structure ExperimentResult where
  experiment : Experiment
  condition : String
  coercionType : CoercionType
  /-- Mixed-effects regression coefficient (log RT) -/
  effectBeta : Rat
  /-- Standard error of the coefficient -/
  se : Rat
  /-- p-value -/
  pValue : Rat
  /-- Spillover region where effect was measured -/
  region : SpilloverRegion
  /-- Whether the effect reached significance (p < 0.05) -/
  significant : Bool
  deriving Repr

/-- Naturalness rating result. -/
structure NaturalnessResult where
  experiment : Experiment
  coercionType : CoercionType
  /-- Regression coefficient for coercion vs control -/
  ratingBeta : Rat
  /-- p-value -/
  pValue : Rat
  /-- Significant difference? -/
  significant : Bool
  deriving Repr

-- ============================================================================
-- § 2: Experiment 1a — Inchoative (within-modifier)
-- ============================================================================

/-- Exp 1a: INCHOAT with *within*-modifier + activity verb.
    Fails to replicate @cite{brennan-pylkkanen-2008}.
    No significant RT slowdown; no naturalness difference. -/
def exp1a_rt : ExperimentResult :=
  { experiment := .exp1a
  , condition := "within-modifier + activity (inchoative coercion)"
  , coercionType := .inchoative
  , effectBeta := -23/1000   -- β = -0.023
  , se := 15/1000
  , pValue := 12/100         -- p = 0.12
  , region := .verbPlus1
  , significant := false }

def exp1a_naturalness : NaturalnessResult :=
  { experiment := .exp1a
  , coercionType := .inchoative
  , ratingBeta := -8/100     -- β = -0.08
  , pValue := 35/100
  , significant := false }

-- ============================================================================
-- § 3: Experiment 1b — Completive (at-modifier)
-- ============================================================================

/-- Exp 1b: COMPLET with *at*-modifier + accomplishment verb.
    Significant slowdown at verb+1; lower naturalness.
    Supports Rett's COMPLET operator. -/
def exp1b_rt : ExperimentResult :=
  { experiment := .exp1b
  , condition := "at-modifier + accomplishment (completive coercion)"
  , coercionType := .completive
  , effectBeta := 33/1000    -- β = 0.033
  , se := 13/1000
  , pValue := 1/100          -- p = 0.01
  , region := .verbPlus1
  , significant := true }

def exp1b_naturalness : NaturalnessResult :=
  { experiment := .exp1b
  , coercionType := .completive
  , ratingBeta := -53/100    -- β = -0.53
  , pValue := 1/10000        -- p < 0.0001
  , significant := true }

-- ============================================================================
-- § 4: Experiment 2 — Completive (before-clause)
-- ============================================================================

/-- Exp 2: COMPLET in *before*-clause with accomplishment EE.
    "John met Mary before she climbed the mountain" (before-finish reading).
    Significant slowdown at verb+2; lower naturalness.
    Delayed effect consistent with pragmatic (vs semantic) coercion. -/
def exp2_rt : ExperimentResult :=
  { experiment := .exp2
  , condition := "before-clause + accomplishment EE (completive coercion)"
  , coercionType := .completive
  , effectBeta := 6/100      -- β = 0.06
  , se := 2/100
  , pValue := 3/1000         -- p = 0.003
  , region := .verbPlus2
  , significant := true }

def exp2_naturalness : NaturalnessResult :=
  { experiment := .exp2
  , coercionType := .completive
  , ratingBeta := -72/100    -- β = -0.72
  , pValue := 1/1000         -- p = 0.001
  , significant := true }

-- ============================================================================
-- § 5: Experiment 3 — Inchoative (subject-experiencer)
-- ============================================================================

/-- Exp 3: INCHOAT with subject-experiencer verbs (stative reading).
    Second failure to replicate @cite{brennan-pylkkanen-2008}.
    No significant RT effect; no naturalness difference. -/
def exp3_rt : ExperimentResult :=
  { experiment := .exp3
  , condition := "subject-experiencer verb (inchoative coercion)"
  , coercionType := .inchoative
  , effectBeta := -11/1000   -- β = -0.011
  , se := 14/1000
  , pValue := 42/100         -- p = 0.42
  , region := .verbPlus1
  , significant := false }

def exp3_naturalness : NaturalnessResult :=
  { experiment := .exp3
  , coercionType := .inchoative
  , ratingBeta := -5/100     -- β = -0.05
  , pValue := 51/100
  , significant := false }

-- ============================================================================
-- § 6: Experiment 4 — Inchoative (after-clause)
-- ============================================================================

/-- Exp 4: INCHOAT in *after*-clause with stative/activity EE.
    "John met Mary after she was president" (after-start reading).
    Significant slowdown at verb+2; lower naturalness.
    INCHOAT cost detected in after-clauses but not within-modifier contexts. -/
def exp4_rt : ExperimentResult :=
  { experiment := .exp4
  , condition := "after-clause + stative EE (inchoative coercion)"
  , coercionType := .inchoative
  , effectBeta := 66/1000    -- β = 0.066
  , se := 25/1000
  , pValue := 8/1000         -- p = 0.008
  , region := .verbPlus2
  , significant := true }

def exp4_naturalness : NaturalnessResult :=
  { experiment := .exp4
  , coercionType := .inchoative
  , ratingBeta := -16/100    -- β = -0.16
  , pValue := 1/100          -- p = 0.01
  , significant := true }

-- ============================================================================
-- § 7: Complement Coercion Sanity Check
-- ============================================================================

/-- Complement coercion (e.g., "began the book") replicates across all experiments.
    This confirms the experimental paradigm is sensitive to coercion effects. -/
def complement_coercion_exp1 : ExperimentResult :=
  { experiment := .exp1a
  , condition := "complement coercion (sanity check)"
  , coercionType := .complement
  , effectBeta := 45/1000    -- β = 0.045
  , se := 12/1000
  , pValue := 2/10000        -- p = 0.0002
  , region := .verbPlus1
  , significant := true }

-- ============================================================================
-- § 8: Bridge Theorems
-- ============================================================================

/-- Rett's theory correctly predicts completive coercion costs where they occur.
    Both Exps 1b (at-modifier) and 2 (before-clause) show significant slowdowns. -/
theorem rett_predicts_completive_cost :
    exp1b_rt.significant = true ∧ exp2_rt.significant = true :=
  ⟨rfl, rfl⟩

/-- Rett's theory correctly predicts inchoative coercion cost in *after*-clauses.
    Exp 4 shows significant slowdown for after-start readings. -/
theorem rett_predicts_inchoative_in_after :
    exp4_rt.significant = true ∧ exp4_rt.coercionType = .inchoative :=
  ⟨rfl, rfl⟩

/-- Within-modifier INCHOAT fails to replicate: Exps 1a and 3 show null results.
    This dissociation (null in within-modifier, significant in after-clause)
    suggests INCHOAT cost is construction-specific, not universal. -/
theorem within_modifier_not_replicated :
    exp1a_rt.significant = false ∧ exp3_rt.significant = false :=
  ⟨rfl, rfl⟩

/-- Complement coercion sanity check passes — confirms paradigm sensitivity. -/
theorem complement_coercion_replicates :
    complement_coercion_exp1.significant = true := rfl

/-- Processing measure: all experiments use self-paced reading. -/
def processingMeasure : MeasureSpec :=
  { scale := .continuous
  , task := .selfPacedReading
  , unit := "log-transformed reading time (ms)" }

/-- Delayed effect in Exp 2: cost at verb+2 (not verb+1) is consistent with
    pragmatic coercion (contextual inference after semantic processing). -/
theorem pragmatic_vs_semantic_delay :
    exp2_rt.region = .verbPlus2 ∧ exp1b_rt.region = .verbPlus1 :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § Bridge: Fragment–Experiment and Cross-Linguistic Connections
-- ============================================================================

open Fragments.English.TemporalExpressions

theorem exp2_tests_before_coercion :
    exp2_rt.coercionType = .completive ∧
    before_.coercedReading = some .beforeFinish :=
  ⟨rfl, rfl⟩

theorem exp4_tests_after_coercion :
    exp4_rt.coercionType = .inchoative ∧
    after_.coercedReading = some .afterStart :=
  ⟨rfl, rfl⟩

theorem exp1b_tests_at_modifier_coercion :
    exp1b_rt.coercionType = .completive ∧
    at_punct.triggeredCoercion = some "COMPLET" :=
  ⟨rfl, rfl⟩

theorem exp1a_tests_within_modifier_coercion :
    exp1a_rt.coercionType = .inchoative ∧
    within_.triggeredCoercion = some "INCHOAT" :=
  ⟨rfl, rfl⟩

theorem complet_consistently_costly :
    exp1b_rt.significant = true ∧
    exp2_rt.significant = true ∧
    exp1b_rt.coercionType = .completive ∧
    exp2_rt.coercionType = .completive :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem inchoat_construction_specific :
    exp4_rt.significant = true ∧
    exp1a_rt.significant = false ∧
    exp3_rt.significant = false ∧
    exp4_rt.coercionType = .inchoative ∧
    exp1a_rt.coercionType = .inchoative ∧
    exp3_rt.coercionType = .inchoative :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem complet_effect_exceeds_inchoat :
    exp1b_rt.effectBeta > exp1a_rt.effectBeta :=
  by native_decide

theorem rt_naturalness_converge :
    (exp1b_rt.significant = exp1b_naturalness.significant) ∧
    (exp2_rt.significant = exp2_naturalness.significant) ∧
    (exp4_rt.significant = exp4_naturalness.significant) ∧
    (exp1a_rt.significant = exp1a_naturalness.significant) ∧
    (exp3_rt.significant = exp3_naturalness.significant) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tagalog_overt_coercion :
    Fragments.Tagalog.TemporalConnectives.bago_aia.culminating = true ∧
    Fragments.Tagalog.TemporalConnectives.bago_aia.reading = .beforeFinish ∧
    Fragments.Tagalog.TemporalConnectives.bago_neut.culminating = false ∧
    Fragments.Tagalog.TemporalConnectives.bago_neut.reading = .beforeStart :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem serbian_overt_coercion :
    Fragments.Serbian.TemporalConnectives.pre_pfv.culminating = true ∧
    Fragments.Serbian.TemporalConnectives.pre_pfv.reading = .beforeFinish ∧
    Fragments.Serbian.TemporalConnectives.pre_impf.culminating = false ∧
    Fragments.Serbian.TemporalConnectives.pre_impf.reading = .beforeStart :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem complet_triple_convergence :
    exp2_rt.significant = true ∧
    exp2_rt.coercionType = .completive ∧
    Fragments.Tagalog.TemporalConnectives.bago_aia.culminating = true ∧
    Fragments.Serbian.TemporalConnectives.pre_pfv.culminating = true :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem connective_later_spillover :
    exp2_rt.region = .verbPlus2 ∧
    exp4_rt.region = .verbPlus2 ∧
    exp1b_rt.region = .verbPlus1 :=
  ⟨rfl, rfl, rfl⟩

end Phenomena.TenseAspect.Studies.AlstottAravind2026
