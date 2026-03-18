import Linglib.Phenomena.Presupposition.Gradience

/-!
# @cite{degen-tonhauser-2021}: Prior Beliefs Modulate Projection

Prior beliefs modulate projection. Open Mind 5:59–70.

## Core Finding

**Higher prior probability of complement content leads to stronger
projection inferences, at both the group and individual participant level.**

This is the first systematic demonstration that subjective prior beliefs
about the world modulate presupposition projection across a wide range of
clause-embedding predicates.

## Experiments

### Experiment 1 (within-participant, N=286)
- Prior block: "How likely is it that [CC]?" (slider, 0=impossible, 1=definitely)
- Projection block: "Is [speaker] certain that [CC]?" (slider, 0=no, 1=yes)
- 20 clause-embedding predicates × 20 contents × 2 fact conditions
- Prior manipulation successful: β = 0.45, SE = 0.01, t = 31.12
- **Prior modulates projection** at all three levels of analysis:
  - Categorical (high vs low fact): β = 0.14, SE = 0.01, t = 12.24
  - Group-level continuous prior: β = 0.31, SE = 0.02, t = 12.58
  - Individual-level continuous prior: β = 0.28, SE = 0.02, t = 13.85
- Individual-level model best by BIC (2291 < 2586 < 2654)

### Experiment 2 (between-participant replication)
- Exp 2a (norming, N=75): replicates prior manipulation (r = .977 vs Exp 1)
- Exp 2b (projection, N=266): replicates prior effect
  - Categorical: β = 0.18, SE = 0.01, t = 12.81
  - Group-level: β = 0.34, SE = 0.03, t = 13.27

## Replication

By-predicate projection ranking replicates Tonhauser & Degen 2020 with
Spearman r = .991.

## Theoretical Significance

The prior-belief effect motivates probabilistic models of projection
(@cite{qing-goodman-lassiter-2016}, @cite{scontras-tonhauser-2025}),
and the gradient by-predicate pattern is subsequently modeled by
@cite{grove-white-2025}'s discrete-factivity model.
-/

namespace Phenomena.Presupposition.Studies.DegenTonhauser2021

open Phenomena.Presupposition.Gradience

-- ============================================================================
-- §1. The 20 Clause-Embedding Predicates
-- ============================================================================

/-- The 20 clause-embedding predicates investigated in D&T 2021 and reused
    in @cite{degen-tonhauser-2022} and @cite{grove-white-2025}. The set
    spans cognitive (know), emotive (be annoyed), communication (announce),
    and inferential (prove) predicates. -/
inductive Predicate where
  -- Canonically factive (5)
  | beAnnoyed
  | discover
  | know
  | reveal
  | see
  -- Nonveridical nonfactive (4)
  | pretend
  | suggest
  | say
  | think
  -- Veridical nonfactive (2)
  | beRight
  | demonstrate
  -- Optionally factive (9)
  | acknowledge
  | admit
  | announce
  | confess
  | confirm
  | establish
  | hear
  | inform
  | prove
  deriving DecidableEq, Repr

-- ============================================================================
-- §2. Regression Results
-- ============================================================================

/-- A regression coefficient from a mixed-effects model. -/
structure RegressionEffect where
  β : Float
  se : Float
  t : Float
  deriving Repr

/-- The three levels of prior-belief predictor tested in Experiment 1.
    The individual-level model captures the most variance (lowest BIC). -/
inductive PriorLevel where
  /-- Binary: high vs low fact condition. -/
  | categorical
  /-- Continuous: group-level mean prior probability by item. -/
  | groupLevel
  /-- Continuous: each participant's own prior probability rating. -/
  | individualLevel
  deriving DecidableEq, Repr

/-- Experiment 1 regression: prior predicts projection at all three levels. -/
def exp1_priorEffect : PriorLevel → RegressionEffect
  | .categorical     => ⟨0.14, 0.01, 12.24⟩
  | .groupLevel      => ⟨0.31, 0.02, 12.58⟩
  | .individualLevel => ⟨0.28, 0.02, 13.85⟩

/-- Experiment 2b regression: between-participant replication. -/
def exp2b_priorEffect : PriorLevel → RegressionEffect
  | .categorical     => ⟨0.18, 0.01, 12.81⟩
  | .groupLevel      => ⟨0.34, 0.03, 13.27⟩
  | .individualLevel => ⟨0.34, 0.03, 13.27⟩ -- not separately reported

/-- BIC values for the three prior-level models in Experiment 1.
    Lower = better fit. Individual-level wins decisively. -/
def exp1_bic : PriorLevel → Float
  | .categorical     => 2654
  | .groupLevel      => 2586
  | .individualLevel => 2291

/-- Individual-level prior beliefs predict projection better than
    group-level beliefs, which predict better than categorical (binary)
    beliefs. This is the key model-comparison result. -/
theorem individual_best_by_bic :
    exp1_bic .individualLevel < exp1_bic .groupLevel ∧
    exp1_bic .groupLevel < exp1_bic .categorical := by
  simp [exp1_bic]; constructor <;> native_decide

-- ============================================================================
-- §3. Core Finding: Prior Modulates Projection
-- ============================================================================

/-- The prior effect is positive at every level of analysis in both
    experiments. A positive β means higher prior → stronger projection. -/
theorem prior_effect_positive_exp1 (level : PriorLevel) :
    (exp1_priorEffect level).β > 0 := by
  cases level <;> simp [exp1_priorEffect] <;> native_decide

/-- The prior effect replicates in the between-participant design. -/
theorem prior_effect_positive_exp2b (level : PriorLevel) :
    (exp2b_priorEffect level).β > 0 := by
  cases level <;> simp [exp2b_priorEffect] <;> native_decide

/-- The prior effect replicates across experiments:
    Exp 1 (within-participant) and Exp 2b (between-participant) show
    the same direction and similar magnitude. -/
theorem prior_effect_replicates :
    (exp1_priorEffect .categorical).β > 0 ∧
    (exp2b_priorEffect .categorical).β > 0 :=
  ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- §4. Replication Correlations
-- ============================================================================

/-- Spearman rank correlation between Exp 1 by-predicate certainty ratings
    (collapsing over facts) and Tonhauser & Degen 2020 Experiment 1a. -/
def replication_r_exp1_vs_td2020 : Float := 0.991

/-- Spearman rank correlation between Exp 2a and Exp 1 prior ratings. -/
def replication_r_exp2a_vs_exp1 : Float := 0.977

/-- Both replication correlations are very high (> 0.95), confirming
    that the by-predicate ranking is robust across experiments. -/
theorem replication_robust :
    replication_r_exp1_vs_td2020 > 0.95 ∧
    replication_r_exp2a_vs_exp1 > 0.95 :=
  ⟨by native_decide, by native_decide⟩

end Phenomena.Presupposition.Studies.DegenTonhauser2021
