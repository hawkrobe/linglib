import Linglib.Features.Acceptability
import Linglib.Fragments.English.TemporalExpressions
import Linglib.Phenomena.TemporalConnectives.Studies.Rett2020
import Linglib.Fragments.Tagalog.TemporalConnectives
import Linglib.Fragments.Slavic.Serbian.TemporalConnectives
import Linglib.Phenomena.TemporalConnectives.Compare
import Linglib.Paradigms.SelfPacedReading

open Features (Acceptability)
open Paradigms.SelfPacedReading (Region)

/-!
# @cite{alstott-aravind-2026}: On aspectual coercion in *before*- and *after*-clauses
@cite{alstott-aravind-2026} @cite{rett-2020}

Self-paced reading data from 4 experiments testing @cite{rett-2020}'s prediction
that aspectual coercion (INCHOAT, COMPLET) incurs measurable processing cost.
Under-specification theories (e.g. @cite{anscombe-1964}) do not predict such costs.

## Results Summary

| Exp | Coercion type | RT effect | Naturalness | Supports Rett? |
|-----|--------------|-----------|-------------|----------------|
| 1a  | INCHOAT (within-modifier) | null | null | No |
| 1b  | COMPLET (at-modifier) | **sig** verb+1 | **sig** lower | Yes |
| 2   | COMPLET (before-clause) | **sig** verb+2† | **sig** lower | Yes |
| 3   | INCHOAT (subj-experiencer) | null | null | No |
| 4   | INCHOAT (after-clause) | **sig** verb+2† | **sig** lower | Yes |

† = exploratory analysis (pre-registered verb/verb+1 regions were null)

Key findings:
- Completive coercion consistently shows processing cost (Exps 1b, 2)
- Inchoative coercion in *after*-clauses shows delayed cost (Exp 4)
- Inchoative coercion in *within*-modifier contexts shows no cost (Exps 1a, 3)
- Complement coercion (sanity check) replicates across all experiments
- Delayed spillover (verb+2) in connective contexts vs verb+1 in modifier contexts
  may reflect pragmatic vs semantic coercion (§5.3, §7.3)

-/

namespace AlstottAravind2026

open Phenomena

-- ============================================================================
-- § 1: Types
-- ============================================================================

/-- Experiment identifiers. Exp 1 has two sub-experiments (a and b). -/
inductive Experiment where
  | exp1a  -- within-modifier + be-stative (inchoative)
  | exp1b  -- at-modifier + accomplishment (completive)
  | exp2   -- before-clause + accomplishment (completive)
  | exp3   -- within-modifier + subject-experiencer (inchoative)
  | exp4   -- after-clause + subject-experiencer (inchoative)
  deriving DecidableEq, Repr, Inhabited

/-- Types of aspectual coercion tested across experiments. -/
inductive CoercionType where
  | inchoative   -- INCHOAT: atelic → onset point (GLB)
  | completive   -- COMPLET: telic → telos point (LUB)
  | complement   -- Complement coercion (sanity check)
  deriving DecidableEq, Repr, Inhabited

/-- Result from a self-paced reading experiment.

    Region uses `Paradigms.SelfPacedReading.Region` (offset from the
    designated critical region): `Region.critical` is the verb,
    `Region.spillover 1` is verb+1, `Region.spillover 2` is verb+2. -/
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
  /-- Region (offset from critical verb) where effect was measured -/
  region : Region
  /-- Whether the effect reached significance (Bonferroni-corrected α = 0.025) -/
  significant : Bool
  /-- Whether the analysis was exploratory (not pre-registered) -/
  exploratory : Bool := false
  deriving Repr

/-- Naturalness rating result (ordinal logistic regression). -/
structure NaturalnessResult where
  experiment : Experiment
  coercionType : CoercionType
  /-- Regression coefficient for coercion vs control -/
  ratingBeta : Rat
  /-- Standard error of the coefficient -/
  se : Rat
  /-- p-value -/
  pValue : Rat
  /-- Significant difference? -/
  significant : Bool
  deriving Repr

-- ============================================================================
-- § 2: Experiment 1a — Inchoative (within-modifier)
-- ============================================================================

/-- Exp 1a: INCHOAT with *within*-modifier + be-stative verb.
    E.g. "Within fifteen minutes Jessica was mad in office hours."
    No significant RT slowdown; no naturalness difference. -/
def exp1a_rt : ExperimentResult :=
  { experiment := .exp1a
  , condition := "within-modifier + be-stative (inchoative coercion)"
  , coercionType := .inchoative
  , effectBeta := -23/1000   -- β = -0.023
  , se := 1/100              -- SE = 0.01
  , pValue := 12/100         -- p = 0.12
  , region := .spillover 1
  , significant := false }

def exp1a_naturalness : NaturalnessResult :=
  { experiment := .exp1a
  , coercionType := .inchoative
  , ratingBeta := -6/100     -- β = -0.06
  , se := 8/100              -- SE = 0.08
  , pValue := 4/10           -- p = 0.4
  , significant := false }

-- ============================================================================
-- § 3: Experiment 1b — Completive (at-modifier)
-- ============================================================================

/-- Exp 1b: COMPLET with *at*-modifier + accomplishment verb.
    E.g. "At 9pm sharp Hector built the humble tent."
    Significant slowdown at verb+1; lower naturalness.
    Supports Rett's COMPLET operator. -/
def exp1b_rt : ExperimentResult :=
  { experiment := .exp1b
  , condition := "at-modifier + accomplishment (completive coercion)"
  , coercionType := .completive
  , effectBeta := 33/1000    -- β = 0.033
  , se := 13/1000
  , pValue := 1/100          -- p = 0.01
  , region := .spillover 1
  , significant := true }

def exp1b_naturalness : NaturalnessResult :=
  { experiment := .exp1b
  , coercionType := .completive
  , ratingBeta := -53/100    -- β = -0.53
  , se := 8/100              -- SE = 0.08
  , pValue := 1/10000        -- p < 0.0001
  , significant := true }

-- ============================================================================
-- § 4: Experiment 2 — Completive (before-clause)
-- ============================================================================

/-- Exp 2: COMPLET in *before*-clause with accomplishment EE.
    E.g. "Emma was irritable before Hector built the tent in the woods."
    Pre-registered regions (verb, verb+1) showed null effects.
    Exploratory verb+2 analysis found significant slowdown; lower naturalness.
    Delayed effect consistent with pragmatic (vs semantic) coercion. -/
def exp2_rt : ExperimentResult :=
  { experiment := .exp2
  , condition := "before-clause + accomplishment EE (completive coercion)"
  , coercionType := .completive
  , effectBeta := 6/100      -- β = 0.06
  , se := 2/100
  , pValue := 3/1000         -- p = 0.003
  , region := .spillover 2
  , significant := true
  , exploratory := true }

def exp2_naturalness : NaturalnessResult :=
  { experiment := .exp2
  , coercionType := .completive
  , ratingBeta := -72/100    -- β = -0.72
  , se := 23/100             -- SE = 0.23
  , pValue := 1/1000         -- p = 0.001
  , significant := true }

-- ============================================================================
-- § 5: Experiment 3 — Inchoative (subject-experiencer)
-- ============================================================================

/-- Exp 3: INCHOAT with subject-experiencer verbs in *within*-modifier context.
    E.g. "Within fifteen minutes Jessica tolerated the unhelpful professor."
    No significant RT effect; no naturalness difference. -/
def exp3_rt : ExperimentResult :=
  { experiment := .exp3
  , condition := "subject-experiencer verb (inchoative coercion)"
  , coercionType := .inchoative
  , effectBeta := -3/1000    -- β = -0.003
  , se := 13/1000            -- SE = 0.013
  , pValue := 78/100         -- p = 0.78
  , region := .spillover 1
  , significant := false }

def exp3_naturalness : NaturalnessResult :=
  { experiment := .exp3
  , coercionType := .inchoative
  , ratingBeta := -35/1000   -- β = -0.035
  , se := 7/100              -- SE = 0.07
  , pValue := 63/100         -- p = 0.63
  , significant := false }

-- ============================================================================
-- § 6: Experiment 4 — Inchoative (after-clause)
-- ============================================================================

/-- Exp 4: INCHOAT in *after*-clause with subject-experiencer EE.
    E.g. "Dave was regretful after Lara feared the large dog."
    Pre-registered regions (verb, verb+1) showed null effects.
    Exploratory verb+2 analysis found significant slowdown; lower naturalness.
    INCHOAT cost detected in after-clauses but not within-modifier contexts. -/
def exp4_rt : ExperimentResult :=
  { experiment := .exp4
  , condition := "after-clause + subject-experiencer EE (inchoative coercion)"
  , coercionType := .inchoative
  , effectBeta := 66/1000    -- β = 0.066
  , se := 24/1000            -- SE = 0.024
  , pValue := 8/1000         -- p = 0.008
  , region := .spillover 2
  , significant := true
  , exploratory := true }

def exp4_naturalness : NaturalnessResult :=
  { experiment := .exp4
  , coercionType := .inchoative
  , ratingBeta := -16/100    -- β = -0.16
  , se := 7/100              -- SE = 0.07
  , pValue := 1/100          -- p = 0.01
  , significant := true }

-- ============================================================================
-- § 7: Complement Coercion Sanity Check
-- ============================================================================

/-- Complement coercion (e.g., "continued his article") in Exp 1a at noun+1.
    This replicates across all experiments, confirming paradigm sensitivity. -/
def complement_coercion_exp1a : ExperimentResult :=
  { experiment := .exp1a
  , condition := "complement coercion (sanity check)"
  , coercionType := .complement
  , effectBeta := 38/1000    -- β = 0.038 (noun+1)
  , se := 15/1000            -- SE = 0.015
  , pValue := 1/100          -- p = 0.01
  , region := .spillover 1     -- noun+1 in complement trials
  , significant := true }

/-- Complement coercion in Exp 1b at noun+1. -/
def complement_coercion_exp1b : ExperimentResult :=
  { experiment := .exp1b
  , condition := "complement coercion (sanity check)"
  , coercionType := .complement
  , effectBeta := 35/1000    -- β = 0.035
  , se := 13/1000            -- SE = 0.013
  , pValue := 9/1000         -- p = 0.009
  , region := .spillover 1
  , significant := true }

/-- Complement coercion in Exp 3 at noun+1. -/
def complement_coercion_exp3 : ExperimentResult :=
  { experiment := .exp3
  , condition := "complement coercion (sanity check)"
  , coercionType := .complement
  , effectBeta := 35/1000    -- β = 0.035
  , se := 13/1000            -- SE = 0.013
  , pValue := 9/1000         -- p = 0.009
  , region := .spillover 1
  , significant := true }

-- ============================================================================
-- § 8: Bridge Theorems — Experiment × Fragment × Theory
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

/-- Within-modifier INCHOAT shows no cost: Exps 1a and 3 show null results.
    This dissociation (null in within-modifier, significant in after-clause)
    suggests INCHOAT cost is construction-specific, not universal.
    The paper's §8.2 proposes a non-coercive, Krifka-style scalar implicature
    analysis for atelic *within*-modifier sentences. -/
theorem within_modifier_not_replicated :
    exp1a_rt.significant = false ∧ exp3_rt.significant = false :=
  ⟨rfl, rfl⟩

/-- Complement coercion sanity check passes in both sub-experiments. -/
theorem complement_coercion_replicates :
    complement_coercion_exp1a.significant = true ∧
    complement_coercion_exp1b.significant = true ∧
    complement_coercion_exp3.significant = true :=
  ⟨rfl, rfl, rfl⟩

/-! Processing measure: all experiments use self-paced reading; the dependent
    variable is log-transformed reading time (ms). -/

/-- Delayed effect in connective contexts: cost at verb+2 (not verb+1).
    Both connective experiments (2, 4) show verb+2 spillover, while the
    modifier experiment (1b) shows verb+1. Consistent with pragmatic
    coercion in connectives being slower to detect than semantic coercion
    in modifier contexts. Both connective results are exploratory. -/
theorem connective_vs_modifier_spillover :
    exp2_rt.region = .spillover 2 ∧ exp2_rt.exploratory = true ∧
    exp4_rt.region = .spillover 2 ∧ exp4_rt.exploratory = true ∧
    exp1b_rt.region = .spillover 1 ∧ exp1b_rt.exploratory = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 9: Fragment–Experiment Connections
-- ============================================================================

open Fragments.English.TemporalExpressions

/-- Exp 2 tests the Fragment's `coercedReading` for *before*:
    COMPLET triggers the before-finish reading. -/
theorem exp2_tests_before_coercion :
    exp2_rt.coercionType = .completive ∧
    before_.coercedReading = some .beforeFinish :=
  ⟨rfl, rfl⟩

/-- Exp 4 tests the Fragment's `coercedReading` for *after*:
    INCHOAT triggers the after-start reading. -/
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

/-- COMPLET is consistently costly across both completive experiments. -/
theorem complet_consistently_costly :
    exp1b_rt.significant = true ∧
    exp2_rt.significant = true ∧
    exp1b_rt.coercionType = .completive ∧
    exp2_rt.coercionType = .completive :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- INCHOAT cost is construction-specific: present in after-clauses (Exp 4),
    absent in within-modifier contexts (Exps 1a, 3). -/
theorem inchoat_construction_specific :
    exp4_rt.significant = true ∧
    exp1a_rt.significant = false ∧
    exp3_rt.significant = false ∧
    exp4_rt.coercionType = .inchoative ∧
    exp1a_rt.coercionType = .inchoative ∧
    exp3_rt.coercionType = .inchoative :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Completive effect size exceeds inchoative in modifier contexts. -/
theorem complet_effect_exceeds_inchoat :
    exp1b_rt.effectBeta > exp1a_rt.effectBeta :=
  by native_decide

/-- RT significance and naturalness significance converge in all 5 experiments:
    every experiment that shows an RT effect also shows a naturalness effect,
    and every null RT result has a null naturalness result. -/
theorem rt_naturalness_converge :
    (exp1b_rt.significant = exp1b_naturalness.significant) ∧
    (exp2_rt.significant = exp2_naturalness.significant) ∧
    (exp4_rt.significant = exp4_naturalness.significant) ∧
    (exp1a_rt.significant = exp1a_naturalness.significant) ∧
    (exp3_rt.significant = exp3_naturalness.significant) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 10: Cross-Linguistic Connections
-- ============================================================================

/-- Tagalog overtly marks what English coerces covertly:
    PFV.AIA (ability/involuntary action) → before-finish (COMPLET);
    PFV.NEUT (neutral) → before-start (no coercion). -/
theorem tagalog_overt_coercion :
    Fragments.Tagalog.TemporalConnectives.bago_aia.culminating = true ∧
    Fragments.Tagalog.TemporalConnectives.bago_aia.reading = .beforeFinish ∧
    Fragments.Tagalog.TemporalConnectives.bago_neut.culminating = false ∧
    Fragments.Tagalog.TemporalConnectives.bago_neut.reading = .beforeStart :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Serbian overtly marks what English coerces covertly:
    perfective → before-finish (COMPLET);
    imperfective → before-start (no coercion). -/
theorem serbian_overt_coercion :
    Fragments.Slavic.Serbian.TemporalConnectives.pre_pfv.culminating = true ∧
    Fragments.Slavic.Serbian.TemporalConnectives.pre_pfv.reading = .beforeFinish ∧
    Fragments.Slavic.Serbian.TemporalConnectives.pre_impf.culminating = false ∧
    Fragments.Slavic.Serbian.TemporalConnectives.pre_impf.reading = .beforeStart :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Triple convergence: English processing data (Exp 2), Tagalog morphology,
    and Serbian morphology all independently support covert COMPLET. -/
theorem complet_triple_convergence :
    exp2_rt.significant = true ∧
    exp2_rt.coercionType = .completive ∧
    Fragments.Tagalog.TemporalConnectives.bago_aia.culminating = true ∧
    Fragments.Slavic.Serbian.TemporalConnectives.pre_pfv.culminating = true :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 11: Theory Comparison — Rett vs Under-specification
-- ============================================================================

open Phenomena.TemporalConnectives.Compare

/-- The paper's central finding: Rett's ambiguity theory predicts processing
    asymmetries between readings, and this prediction is confirmed by the data.
    Under-specification theories (Anscombe, B&C, O&ST) do not predict such costs. -/
theorem rett_uniquely_predicts_processing_cost :
    rettProfile.predictsProcessingCost = true ∧
    anscombeProfile.predictsProcessingCost = false ∧
    ostProfile.predictsProcessingCost = false ∧
    bcProfile.predictsProcessingCost = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The data confirms the prediction: significant processing costs exist
    for coerced readings (Exps 1b, 2, 4). The only theory that predicts
    this is Rett's, which posits covert coercion operators. -/
theorem data_supports_rett :
    rettProfile.positsCoercion = true ∧
    exp1b_rt.significant = true ∧
    exp2_rt.significant = true ∧
    exp4_rt.significant = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Rett's coercion operators have overt cross-linguistic reflexes:
    the theory posits coercion, and languages like Tagalog and Serbian
    realize it morphologically. -/
theorem coercion_has_crosslinguistic_reflexes :
    rettProfile.positsCoercion = true ∧
    Fragments.Tagalog.TemporalConnectives.bago_aia.culminating = true ∧
    Fragments.Slavic.Serbian.TemporalConnectives.pre_pfv.culminating = true :=
  ⟨rfl, rfl, rfl⟩

end AlstottAravind2026
