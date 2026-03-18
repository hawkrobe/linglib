import Linglib.Phenomena.Presupposition.Gradience
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Copular

/-!
# @cite{degen-tonhauser-2021}: Prior Beliefs Modulate Projection
@cite{qing-goodman-lassiter-2016}

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
  - Individual-level NOT tested (between-participant: no individual priors)

## Replication

By-predicate projection ranking replicates Tonhauser & Degen 2020 with
Spearman r = .991.

## Theoretical Significance

The prior-belief effect motivates probabilistic models of projection
(e.g., @cite{qing-goodman-lassiter-2016}). Both existing probabilistic
projection models (Qing et al. 2016, Stevens et al. 2017) are couched
within the RSA framework, which standardly assumes utterance interpretation
is modulated by listeners' prior beliefs.
-/

namespace Phenomena.Presupposition.Studies.DegenTonhauser2021

open Phenomena.Presupposition.Gradience

-- ============================================================================
-- §1. The 20 Clause-Embedding Predicates
-- ============================================================================

/-- The 20 clause-embedding predicates investigated in D&T 2021, listed
    alphabetically as in Figure 1C. The set spans cognitive (know), emotive
    (be annoyed), communication (announce), and inferential (prove) predicates.
    For the traditional factive/nonfactive classification of these predicates,
    see `DegenTonhauser2022.traditionalClass`. -/
inductive Predicate where
  | acknowledge
  | admit
  | announce
  | beAnnoyed
  | beRight
  | confess
  | confirm
  | demonstrate
  | discover
  | establish
  | hear
  | inform
  | know
  | pretend
  | prove
  | reveal
  | say
  | see
  | suggest
  | think
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
    The individual-level model captures the most variance (lowest BIC).
    Experiment 2 is between-participant, so only categorical and group-level
    are tested there (individual priors unavailable). -/
inductive PriorLevel where
  /-- Binary: high vs low fact condition. -/
  | categorical
  /-- Continuous: group-level mean prior probability by item. -/
  | groupLevel
  /-- Continuous: each participant's own prior probability rating.
      Only available in within-participant designs (Experiment 1). -/
  | individualLevel
  deriving DecidableEq, Repr

/-- Experiment 1: prior manipulation was successful.
    Higher-probability facts yielded higher prior ratings than
    lower-probability facts (β = 0.45, SE = 0.01, t = 31.12). -/
def exp1_priorManipulation : RegressionEffect := ⟨0.45, 0.01, 31.12⟩

/-- Experiment 1 regression: prior predicts projection at all three levels. -/
def exp1_priorEffect : PriorLevel → RegressionEffect
  | .categorical     => ⟨0.14, 0.01, 12.24⟩
  | .groupLevel      => ⟨0.31, 0.02, 12.58⟩
  | .individualLevel => ⟨0.28, 0.02, 13.85⟩

/-- Experiment 2b regression: between-participant replication.
    Only categorical and group-level predictors are available —
    Exp 2 is between-participant, so individual priors are not measured
    alongside projection. -/
def exp2b_priorEffect : PriorLevel → Option RegressionEffect
  | .categorical     => some ⟨0.18, 0.01, 12.81⟩
  | .groupLevel      => some ⟨0.34, 0.03, 13.27⟩
  | .individualLevel => none  -- between-participant: not applicable

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

/-- The prior manipulation was successful: β > 0. -/
theorem prior_manipulation_successful :
    exp1_priorManipulation.β > 0 := by native_decide

-- ============================================================================
-- §3. Core Finding: Prior Modulates Projection
-- ============================================================================

/-- The prior effect is positive at every level of analysis in Experiment 1.
    A positive β means higher prior → stronger projection. -/
theorem prior_effect_positive_exp1 (level : PriorLevel) :
    (exp1_priorEffect level).β > 0 := by
  cases level <;> simp [exp1_priorEffect] <;> native_decide

/-- The prior effect replicates in the between-participant design
    at both applicable levels (categorical and group-level). -/
theorem prior_effect_positive_exp2b_cat :
    exp2b_priorEffect .categorical = some ⟨0.18, 0.01, 12.81⟩ := rfl

theorem prior_effect_positive_exp2b_grp :
    exp2b_priorEffect .groupLevel = some ⟨0.34, 0.03, 13.27⟩ := rfl

/-- Individual-level prior is not available in the between-participant design. -/
theorem exp2b_no_individual :
    exp2b_priorEffect .individualLevel = none := rfl

/-- The prior effect replicates across experiments:
    Exp 1 (within-participant) and Exp 2b (between-participant) show
    the same direction at the categorical level. -/
theorem prior_effect_replicates :
    (exp1_priorEffect .categorical).β > 0 ∧
    exp2b_priorEffect .categorical = some ⟨0.18, 0.01, 12.81⟩ :=
  ⟨by native_decide, rfl⟩

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

-- ============================================================================
-- §5. Projection Profiles (Gradience Integration)
-- ============================================================================

/-- Mean certainty ratings by predicate and fact condition from Experiment 1.
    Values computed from the data at
    github.com/judith-tonhauser/projective-probability (results/9-prior-projection),
    rounded to 2 decimal places. Ordered by overall projection strength
    (Figure 3 x-axis). -/
def projectionProfile : Predicate → ProjectionProfile
  | .pretend     => ⟨0.31, 0.21⟩
  | .beRight     => ⟨0.34, 0.20⟩
  | .suggest     => ⟨0.32, 0.24⟩
  | .say         => ⟨0.38, 0.22⟩
  | .think       => ⟨0.40, 0.20⟩
  | .confirm     => ⟨0.37, 0.28⟩
  | .prove       => ⟨0.41, 0.25⟩
  | .establish   => ⟨0.43, 0.27⟩
  | .demonstrate => ⟨0.48, 0.33⟩
  | .announce    => ⟨0.53, 0.41⟩
  | .admit       => ⟨0.60, 0.43⟩
  | .confess     => ⟨0.58, 0.45⟩
  | .reveal      => ⟨0.62, 0.47⟩
  | .acknowledge => ⟨0.65, 0.49⟩
  | .discover    => ⟨0.69, 0.55⟩
  | .hear        => ⟨0.72, 0.57⟩
  | .see         => ⟨0.69, 0.60⟩
  | .inform      => ⟨0.76, 0.57⟩
  | .know        => ⟨0.74, 0.68⟩
  | .beAnnoyed   => ⟨0.80, 0.68⟩

/-- The core finding: prior beliefs modulate projection for EVERY predicate.
    High-prior content projects more strongly than low-prior content across
    all 20 predicates. -/
theorem prior_modulates_all (p : Predicate) :
    priorBeliefModulatesProjection (projectionProfile p) := by
  cases p <;> simp [projectionProfile, priorBeliefModulatesProjection] <;> native_decide

-- ============================================================================
-- §6. Fragment Bridge
-- ============================================================================

section FragmentBridge

open Fragments.English.Predicates.Verbal
open Fragments.English.Predicates.Copular

/-- Map each D&T predicate to its Fragment verb entry (18 of 20).
    "be annoyed" and "be right" are copular — use `toPredicateCore` for
    full coverage. -/
def toVerbEntry : Predicate → Option VerbEntry
  | .know => some know
  | .think => some think
  | .discover => some discover
  | .see => some see
  | .say => some say
  | .hear => some hear
  | .reveal => some reveal
  | .acknowledge => some acknowledge
  | .admit => some admit
  | .announce => some announce
  | .confess => some confess
  | .inform => some inform
  | .suggest => some suggest
  | .pretend => some pretend
  | .confirm => some confirm
  | .demonstrate => some demonstrate
  | .establish => some establish
  | .prove => some prove
  | .beAnnoyed => none
  | .beRight => none

/-- Map each D&T predicate to its `VerbCore` — the semantic spine shared by
    verbal and copular entries. Covers all 20 predicates.
    Copular entries go through `ClauseEmbeddingAdj.toVerbCore` (English-specific
    realization: copula + adjective). -/
def toPredicateCore : Predicate → VerbCore
  | .know => know.toVerbCore
  | .think => think.toVerbCore
  | .discover => discover.toVerbCore
  | .see => see.toVerbCore
  | .say => say.toVerbCore
  | .hear => hear.toVerbCore
  | .reveal => reveal.toVerbCore
  | .acknowledge => acknowledge.toVerbCore
  | .admit => admit.toVerbCore
  | .announce => announce.toVerbCore
  | .confess => confess.toVerbCore
  | .inform => inform.toVerbCore
  | .suggest => suggest.toVerbCore
  | .pretend => pretend.toVerbCore
  | .confirm => confirm.toVerbCore
  | .demonstrate => demonstrate.toVerbCore
  | .establish => establish.toVerbCore
  | .prove => prove.toVerbCore
  | .beAnnoyed => beAnnoyed.toVerbCore
  | .beRight => beRight.toVerbCore

/-- All 20 D&T predicates (alphabetical). -/
def allPredicates : List Predicate :=
  [.acknowledge, .admit, .announce, .beAnnoyed, .beRight,
   .confess, .confirm, .demonstrate, .discover, .establish,
   .hear, .inform, .know, .pretend, .prove,
   .reveal, .say, .see, .suggest, .think]

/-- All 20 predicates have Fragment entries via `toPredicateCore`. -/
theorem full_coverage :
    allPredicates.length = 20 := by native_decide

/-- 18 of 20 predicates have `VerbEntry` entries (all except copular
    "be annoyed" and "be right"). -/
theorem verbEntry_coverage :
    (allPredicates.filter (fun p => (toVerbEntry p).isSome)).length = 18 := by
  native_decide

/-- Every predicate takes a finite clause complement (as primary or alternate
    frame), matching D&T's experimental design. -/
theorem all_predicates_take_clause_complement (p : Predicate) :
    (toPredicateCore p).complementType = .finiteClause ∨
    (toPredicateCore p).altComplementType = some .finiteClause := by
  cases p <;>
    simp [toPredicateCore, Semantics.Lexical.Adjective.ClauseEmbeddingAdj.toVerbCore,
          beAnnoyed, beRight] <;>
    first | left; rfl | right; rfl

end FragmentBridge

end Phenomena.Presupposition.Studies.DegenTonhauser2021
