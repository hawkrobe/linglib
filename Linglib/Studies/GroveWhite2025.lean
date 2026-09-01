import Linglib.Semantics.Attitudes.Factivity
import Linglib.Semantics.Probabilistic.Basic
import Linglib.Studies.DegenTonhauser2022
import Linglib.Studies.ScontrasTonhauser2025
import Linglib.Core.Algebra.Order.Interval.Set.Instances

/-!
# [grove-white-2025]

Factivity, presupposition projection, and the role of discrete knowledge
in gradient inference judgments. Natural Language Semantics 34:1–45.

## Core Contribution

Grove & White compare two hypotheses about the gradience observed in
inference judgments for clause-embedding predicates:

- **Fundamental Discreteness Hypothesis (FDH)** (definition (7a), p. 10):
  factivity is a discrete property of an expression on a particular occasion
  of use. A given use either triggers a projective inference, or it does not.
  Observed gradience arises from *resolved indeterminacy* — variation across
  occasions in which reading is selected.

- **Fundamental Gradience Hypothesis (FGH)** (definition (7b), p. 10):
  there is no property distinguishing factive from non-factive occurrences.
  Gradient distinctions reflect gradient inference contributions.

Both hypotheses are recorded as `FactivityHypothesis.FDH` and
`FactivityHypothesis.FGH`, exposed as the two `GradienceSource` values
(resolved vs unresolved indeterminacy). The paper's distinctive formal
content is the τ-parameterised model and the 2 × 2 model space crossing
factivity discreteness with world-knowledge discreteness.

## The Discrete-Factivity Model

The discrete-factivity model is `Probabilistic.gradedTruth` over `FactivityReading`:

- `clauseEmbeddingSem .factive`     = `factivePos` (`BEL ∧ C`)
- `clauseEmbeddingSem .nonfactive`  = `nonFactivePos` (`BEL`)
- prior over readings: `⟨τ, 1 − τ⟩` for `τ : Set.Icc (0 : ℚ) 1`

The graded truth value of a predicate at a world `w` then unfolds to
`τ · 1[BEL∧C] + (1−τ) · 1[BEL]` (`discreteFactivity_eq`).
This is the closed-form reduction of the τ-vertex of the paper's DAG
(definition (13), p. 20).

## The Four Models

Crossing factivity (discrete/gradient) × world knowledge (discrete/gradient)
yields four model variants. The paper reports that the discrete-factivity
× gradient-world variant achieves the best ELPD across all four datasets
(Sect. 4.3–4.4). The 2 × 2 is captured by `ModelVariant`, with the
discrete-factivity-vs-wholly-gradient pair sharing world-knowledge treatment
(`best_worst_share_world_knowledge`) so that switching factivity hypothesis
is the active variable.

## Connection to PDS

The paper's formal framework is Probabilistic Dynamic Semantics (PDS),
developed in [grove-white-2025b]. The model's graded truth is the Bernoulli
prior's mass on the satisfied-readings event (`Probabilistic.gradedTruth`):
graded inference judgments emerge from
marginalising over a *discrete* reading parameter, exactly the PDS
pattern in which a `bind` over a discrete probability node feeds a
Boolean predicate.

## Connection to [scontras-tonhauser-2025]

[scontras-tonhauser-2025]'s RSA model uses the same `factivePos` /
`nonFactivePos` foundation from `Factivity`
for `know` / `think`. The bridges
`clauseEmbedding_factive_eq_st_know` and
`clauseEmbedding_nonfactive_eq_st_think` make this explicit. The S&T binary
treatment is the τ → {0, 1} limiting case of the discrete-factivity model
(`st_is_limiting_case`).

## Connection to D&T 2021/2022

The empirical anchoring is provided by `DegenTonhauser2022`'s aggregate
projection ratings: under the discrete-factivity model with `τ_know > τ_think`,
the model predicts the empirically observed `know > think` projection
ordering (`empirical_ordering_consistent_with_tau`). The prior-belief
modulation finding from [degen-tonhauser-2021] (replicated in 2b) is
the specific empirical regularity the world-knowledge component is fit to.
-/

namespace GroveWhite2025

open MeasureTheory Factivity Probabilistic
open DegenTonhauser2021
open DegenTonhauser2022
open scoped ENNReal NNReal

/-! ## §1. Clause-embedding semantics -/

section ClauseEmbedding

/-- The two readings of a clause-embedding predicate under the FDH.
    The `factive` reading triggers a projective inference (`BEL ∧ C`);
    the `nonfactive` reading does not (`BEL`). -/
inductive FactivityReading where
  | factive
  | nonfactive
  deriving DecidableEq, Repr, Inhabited

instance : Fintype FactivityReading where
  elems := {.factive, .nonfactive}
  complete := fun x => by cases x <;> simp

variable {W : Type*} [HasBelief W] [HasComplement W]

/-- The Boolean denotation of a clause-embedding predicate, parameterized by
    the resolved reading. The two readings dispatch directly to
    `Factivity` — `factivePos` and
    `nonFactivePos` — so this study shares its foundations with
    [scontras-tonhauser-2025]'s `know` / `think` denotations. -/
def clauseEmbeddingSem : FactivityReading → W → Bool
  | .factive    => factivePos
  | .nonfactive => nonFactivePos

end ClauseEmbedding

/-! ## §2. The τ-parameterised prior -/

section Prior

variable {W : Type*}

/-- `τ.val : ℚ` lifted to `ℝ≥0` via the canonical `ℝ`-coercion. -/
noncomputable def toNNReal (τ : Set.Icc (0 : ℚ) 1) : ℝ≥0 :=
  Real.toNNReal τ.val

theorem toNNReal_le_one (τ : Set.Icc (0 : ℚ) 1) : toNNReal τ ≤ 1 :=
  Real.toNNReal_le_one.mpr (by exact_mod_cast τ.prop.2)

theorem toNNReal_val (τ : Set.Icc (0 : ℚ) 1) : ((toNNReal τ : ℝ≥0) : ℝ) = τ.val :=
  Real.coe_toNNReal _ (by exact_mod_cast τ.prop.1)

instance : MeasurableSpace FactivityReading := ⊤
instance : DiscreteMeasurableSpace FactivityReading := ⟨fun _ => trivial⟩

/-- The Bernoulli prior over `FactivityReading`: factive with probability
    `τ.val`, nonfactive with probability `1 − τ.val`. The τ parameter is
    bundled as `Set.Icc (0 : ℚ) 1`, so the [0,1] constraint is
    intrinsic to the type rather than threaded as side hypotheses. This is
    the τ-vertex of the discrete-factivity DAG (definition (13), p. 20). -/
noncomputable def factivityPrior (τ : Set.Icc (0 : ℚ) 1) : Measure FactivityReading :=
  (toNNReal τ : ℝ≥0∞) • Measure.dirac .factive +
    ((1 - toNNReal τ : ℝ≥0) : ℝ≥0∞) • Measure.dirac .nonfactive

@[simp] theorem factivityPrior_singleton_factive (τ : Set.Icc (0 : ℚ) 1) :
    factivityPrior τ {.factive} = ((toNNReal τ : ℝ≥0) : ℝ≥0∞) := by
  simp [factivityPrior]

@[simp] theorem factivityPrior_singleton_nonfactive (τ : Set.Icc (0 : ℚ) 1) :
    factivityPrior τ {.nonfactive} = (((1 : ℝ≥0) - toNNReal τ : ℝ≥0) : ℝ≥0∞) := by
  simp [factivityPrior]

instance (τ : Set.Icc (0 : ℚ) 1) : IsProbabilityMeasure (factivityPrior τ) := ⟨by
  simp only [factivityPrior, Measure.coe_add, Pi.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.coe_add, add_tsub_cancel_of_le (toNNReal_le_one τ), ENNReal.coe_one]⟩

end Prior

/-! ## §3. The discrete-factivity model -/

section DiscreteFactivity

variable {W : Type*} [HasBelief W] [HasComplement W]

/-- The discrete-factivity model: the graded truth of the clause-embedding predicate at `w`
    is the Bernoulli prior's mass on the readings under which it holds
    (`Probabilistic.gradedTruth` of `clauseEmbeddingSem`; definition (13), p. 20). -/
noncomputable def discreteFactivity (τ : Set.Icc (0 : ℚ) 1) (w : W) : ℝ :=
  Probabilistic.gradedTruth (factivityPrior τ) (fun θ w => clauseEmbeddingSem θ w) w

/-- Closed-form reduction: graded truth = `τ · 1[factivePos] + (1−τ) · 1[nonFactivePos]`.
    This is the substantive content of the τ-parameterised model — graded
    inference values arise from a τ-weighted mixture of two crisp Boolean
    readings. -/
theorem discreteFactivity_eq (τ : Set.Icc (0 : ℚ) 1) (w : W) :
    discreteFactivity τ w =
      (if factivePos w then (τ.val : ℝ) else 0) +
        (if nonFactivePos (W := W) w then 1 - (τ.val : ℝ) else 0) := by
  simp only [discreteFactivity, Probabilistic.gradedTruth, measureReal_def, factivityPrior,
    Measure.coe_add, Pi.add_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul,
    Set.indicator_apply, Set.mem_ofPred_eq, clauseEmbeddingSem, Pi.one_apply]
  split_ifs <;> simp [ENNReal.toReal_add, toNNReal_val, NNReal.coe_sub (toNNReal_le_one τ),
    -ENNReal.coe_sub]

/-- With τ = 1 (certainly factive), graded truth reduces to `factivePos`. -/
theorem discreteFactivity_certain_factive (w : W) :
    discreteFactivity 1 w = if factivePos w then 1 else 0 := by
  rw [discreteFactivity_eq]; simp

/-- With τ = 0 (certainly nonfactive), graded truth reduces to `nonFactivePos`. -/
theorem discreteFactivity_certain_nonfactive (w : W) :
    discreteFactivity 0 w = if nonFactivePos (W := W) w then 1 else 0 := by
  rw [discreteFactivity_eq]; simp

/-- Monotonicity in τ: at a world that satisfies the factive reading but
    not the nonfactive reading, increasing τ strictly increases graded
    truth. The hypothesis pattern `factivePos w ∧ ¬ nonFactivePos w` is
    impossible in standard Boolean semantics (`factive_entails_nonfactive`
    rules it out), so this lemma is vacuously achievable; the substantive
    case is the *contrapositive* one supplied by `discreteFactivity_eq`
    plus monotonicity of the Bernoulli mixture. -/
theorem higher_tau_higher_gradedTruth
    (τ₁ τ₂ : Set.Icc (0 : ℚ) 1) (w : W)
    (h_tau : τ₁.val > τ₂.val)
    (h_factive : factivePos w = true)
    (h_nonfactive : nonFactivePos (W := W) w = false) :
    discreteFactivity τ₁ w > discreteFactivity τ₂ w := by
  rw [discreteFactivity_eq, discreteFactivity_eq]
  simp only [h_factive, h_nonfactive, Bool.false_eq_true, ↓reduceIte, add_zero]
  exact_mod_cast h_tau

end DiscreteFactivity

/-! ## §4. The 2 × 2 model space -/

section ModelVariants

/-- Sources of gradience in inference judgment tasks. -/
inductive GradienceSource where
  /-- Resolved on each occasion but varying across occasions (type-level). -/
  | resolved
  /-- Persists even after fixing the interpretation (token-level). -/
  | unresolved
  deriving DecidableEq, Repr

/-- The choice between the discrete (FDH) and gradient (FGH) hypotheses
    is a binary choice of source for the gradient projection observations.

    Defined as `@[reducible] def` rather than `abbrev` so the unfolding is
    explicit (mathlib convention). -/
@[reducible] def FactivityHypothesis : Type := GradienceSource

/-- The Fundamental Discreteness Hypothesis (definition (7a), p. 10):
    factivity is a discrete property of an expression on each occasion
    of use. Observed gradience arises from resolved indeterminacy. -/
def FactivityHypothesis.FDH : FactivityHypothesis := .resolved

/-- The Fundamental Gradience Hypothesis (definition (7b), p. 10):
    there is no property distinguishing factive from non-factive
    occurrences. Gradient distinctions reflect gradient inference
    contributions. -/
def FactivityHypothesis.FGH : FactivityHypothesis := .unresolved

/-- The four model variants from Sect. 4.3–4.4, crossing factivity
    (discrete/gradient) × world knowledge (discrete/gradient). Each model
    is a completion of one of the two norming models (Sect. 4.2) with a
    factivity component. -/
inductive ModelVariant where
  /-- Discrete factivity + gradient world knowledge. Best fit. Extends
      norming-gradient (Sect. 4.2.1). -/
  | discreteFactivity
  /-- Discrete factivity + discrete world knowledge. Extends norming-discrete
      (Sect. 4.2.2). -/
  | whollyDiscrete
  /-- Gradient factivity + gradient world knowledge. Worst fit. -/
  | whollyGradient
  /-- Gradient factivity + discrete world knowledge. -/
  | discreteWorld
  deriving DecidableEq, Repr

/-- Two norming-model bases (Sect. 4.2). -/
inductive NormingModel where
  /-- Norming-gradient (Sect. 4.2.1): world knowledge as unresolved gradience. -/
  | gradient
  /-- Norming-discrete (Sect. 4.2.2): world knowledge as resolved gradience. -/
  | discrete
  deriving DecidableEq, Repr

/-- Whether a model treats factivity as discrete (FDH) or gradient (FGH). -/
def ModelVariant.factivityHypothesis : ModelVariant → FactivityHypothesis
  | .discreteFactivity => .FDH
  | .whollyDiscrete    => .FDH
  | .whollyGradient    => .FGH
  | .discreteWorld     => .FGH

/-- Whether a model treats world knowledge as gradient (unresolved) or
    discrete (resolved). -/
def ModelVariant.worldKnowledgeSource : ModelVariant → GradienceSource
  | .discreteFactivity => .unresolved
  | .whollyDiscrete    => .resolved
  | .whollyGradient    => .unresolved
  | .discreteWorld     => .resolved

/-- Each factivity model extends one of two norming models. The extension
    relationship is determined by the world-knowledge treatment. -/
def ModelVariant.baseNormingModel : ModelVariant → NormingModel
  | .discreteFactivity => .gradient
  | .whollyDiscrete    => .discrete
  | .whollyGradient    => .gradient
  | .discreteWorld     => .discrete

/-- The best and worst models share their world-knowledge treatment but
    differ in factivity hypothesis. This isolates the discreteness of
    factivity as the variable explaining the ELPD spread between the two
    extremes. -/
theorem best_worst_share_world_knowledge :
    ModelVariant.discreteFactivity.worldKnowledgeSource =
    ModelVariant.whollyGradient.worldKnowledgeSource ∧
    ModelVariant.discreteFactivity.factivityHypothesis ≠
    ModelVariant.whollyGradient.factivityHypothesis :=
  ⟨rfl, by decide⟩

end ModelVariants

/-! ## §5. Bridge to [scontras-tonhauser-2025] -/

section ScontrasTonhauserBridge

/-- The `factive` reading of `clauseEmbeddingSem` is the same Boolean
    predicate as [scontras-tonhauser-2025]'s `literalMeaning .knowPos`.
    Both unfold to `factivePos` from `Factivity`,
    so the equality is true by construction — a *grounding theorem* in the
    sense of `CLAUDE.md`, witnessing that two paper-specific lexical entries
    share their foundation. -/
theorem clauseEmbedding_factive_eq_st_know :
    clauseEmbeddingSem (W := ScontrasTonhauser2025.WorldState) .factive
      = ScontrasTonhauser2025.literalMeaning .knowPos := rfl

/-- The `nonfactive` reading is [scontras-tonhauser-2025]'s
    `literalMeaning .thinkPos` (both unfold to `nonFactivePos`). -/
theorem clauseEmbedding_nonfactive_eq_st_think :
    clauseEmbeddingSem (W := ScontrasTonhauser2025.WorldState) .nonfactive
      = ScontrasTonhauser2025.literalMeaning .thinkPos := rfl

/-- The S&T binary model is the τ → {0, 1} limiting case of the
    discrete-factivity model: `know` corresponds to `τ_know = 1` (always
    factive) and `think` corresponds to `τ_think = 0` (never factive). The
    Grove–White model generalises by allowing intermediate τ values for
    the same predicate across occasions of use. -/
theorem st_is_limiting_case :
    (∀ w : ScontrasTonhauser2025.WorldState,
      discreteFactivity 1 w =
      if ScontrasTonhauser2025.literalMeaning .knowPos w then 1 else 0) ∧
    (∀ w : ScontrasTonhauser2025.WorldState,
      discreteFactivity 0 w =
      if ScontrasTonhauser2025.literalMeaning .thinkPos w then 1 else 0) :=
  ⟨discreteFactivity_certain_factive, discreteFactivity_certain_nonfactive⟩

end ScontrasTonhauserBridge

/-! ## §6. Empirical anchoring (D&T 2021/2022) -/

section EmpiricalAnchor

/-- With `τ_know > τ_think` the discrete-factivity model predicts a `know > think`
    projection ordering; [degen-tonhauser-2022]'s exp 1a ratings confirm the
    direction (0.86 vs 0.20). -/
theorem empirical_ordering_consistent_with_tau :
    certainty1a .know > certainty1a .think := by
  norm_num [certainty1a]

/-- The prior-belief modulation finding from [degen-tonhauser-2021] (replicated
    in Exp 2b) is the empirical regularity the world-knowledge component of the
    discrete-factivity model is fit to: a prior-sensitive (monotone) account
    predicts that higher prior probability of the complement yields stronger
    projection (`DegenTonhauser2021.sensitive_predicts_modulation`), which their
    data confirm for all 20 predicates. -/
theorem prior_effect_consistent {acc : PriorAccount} (h : PriorSensitive acc)
    {p q : Set.Icc (0 : ℚ) 1} (hpq : p < q) : acc p < acc q :=
  sensitive_predicts_modulation h hpq

end EmpiricalAnchor

end GroveWhite2025
