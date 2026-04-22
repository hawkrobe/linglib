import Linglib.Theories.Semantics.Attitudes.Factivity
import Linglib.Theories.Semantics.Probabilistic.ParamPred
import Linglib.Phenomena.Presupposition.Gradience
import Linglib.Phenomena.Presupposition.Studies.DegenTonhauser2022
import Linglib.Phenomena.Presupposition.Studies.ScontrasTonhauser2025
import Linglib.Core.Scales.Scale

/-!
# @cite{grove-white-2025}

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
`FactivityHypothesis.FGH` in `Phenomena.Presupposition.Gradience`,
where they are exposed as the two `GradienceSource` values. The paper's
distinctive content is encoded *here*: the τ-parameterised model and the
2 × 2 model space crossing factivity discreteness with world-knowledge
discreteness.

## The Discrete-Factivity Model

The discrete-factivity model is a `ParamPred` over `FactivityReading`:

- `clauseEmbeddingSem .factive`     = `factivePos` (`BEL ∧ C`)
- `clauseEmbeddingSem .nonfactive`  = `nonFactivePos` (`BEL`)
- prior over readings: `⟨τ, 1 − τ⟩` for `τ : Rat01`

The graded truth value of a predicate at a world `w` then unfolds to
`τ · 1[BEL∧C] + (1−τ) · 1[BEL]` (`discreteFactivity_gradedTruth`).
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
developed in @cite{grove-white-2025b}. The model's graded truth is the
`PMF.probOfSet` (= `toOuterMeasure`) of the satisfied-readings event
under the Bernoulli prior: graded inference judgments emerge from
marginalising over a *discrete* reading parameter, exactly the PDS
pattern in which a `bind` over a discrete probability node feeds a
Boolean predicate.

## Connection to @cite{scontras-tonhauser-2025}

@cite{scontras-tonhauser-2025}'s RSA model uses the same `factivePos` /
`nonFactivePos` foundation from `Theories.Semantics.Attitudes.Factivity`
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
modulation finding from @cite{degen-tonhauser-2021} (replicated in 2b) is
the specific empirical regularity the world-knowledge component is fit to.
-/

set_option autoImplicit false

namespace GroveWhite2025

open Semantics.Attitudes.Factivity
open Semantics.Probabilistic
open Phenomena.Presupposition.Gradience
open DegenTonhauser2021
open DegenTonhauser2022
open Core.Scale (Rat01)
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

/-- Sum over `FactivityReading.univ` reduces to a two-term sum. Used by
    `factivityPrior.mass_sum_one` and `discreteFactivity_gradedTruth` so the
    Fintype enumeration doesn't reappear inline at every call site. -/
theorem FactivityReading.sum_univ {α : Type*} [AddCommMonoid α]
    (f : FactivityReading → α) :
    ∑ x : FactivityReading, f x = f .factive + f .nonfactive := by
  rw [show (Finset.univ : Finset FactivityReading) = {.factive, .nonfactive} from rfl,
      Finset.sum_insert (by decide), Finset.sum_singleton]

variable {W : Type*} [HasBelief W] [HasComplement W]

/-- The Boolean denotation of a clause-embedding predicate, parameterized by
    the resolved reading. The two readings dispatch directly to
    `Theories.Semantics.Attitudes.Factivity` — `factivePos` and
    `nonFactivePos` — so this study shares its foundations with
    @cite{scontras-tonhauser-2025}'s `know` / `think` denotations. -/
def clauseEmbeddingSem : FactivityReading → W → Bool
  | .factive    => factivePos
  | .nonfactive => nonFactivePos

end ClauseEmbedding

/-! ## §2. The τ-parameterised prior -/

section Prior

variable {W : Type*}

/-- `τ.val : ℚ` lifted to `ℝ≥0` via the canonical `ℝ`-coercion. Lives
    outside the `Rat01` namespace because `Rat01` is an `abbrev` for
    a `Subtype`, so dot notation on `τ : Rat01` resolves through the
    underlying `Subtype` rather than the `Rat01` namespace. -/
noncomputable def Rat01.toNNReal (τ : Rat01) : ℝ≥0 :=
  Real.toNNReal τ.val

theorem Rat01.toNNReal_le_one (τ : Rat01) : Rat01.toNNReal τ ≤ 1 :=
  Real.toNNReal_le_one.mpr (by exact_mod_cast τ.prop.2)

theorem Rat01.toNNReal_val (τ : Rat01) : ((Rat01.toNNReal τ : ℝ≥0) : ℝ) = τ.val :=
  Real.coe_toNNReal _ (by exact_mod_cast τ.prop.1)

/-- The Bernoulli prior over `FactivityReading`: factive with probability
    `τ.val`, nonfactive with probability `1 − τ.val`. The τ parameter is
    bundled as `Rat01` (`↥(Set.Icc (0:ℚ) 1)`), so the [0,1] constraint is
    intrinsic to the type rather than threaded as side hypotheses. This is
    the τ-vertex of the discrete-factivity DAG (definition (13), p. 20).

    Built from mathlib's `PMF.bernoulli` (a `PMF Bool`) by relabeling
    `true ↦ .factive`, `false ↦ .nonfactive`. -/
noncomputable def factivityPrior (τ : Rat01) : PMF FactivityReading :=
  (PMF.bernoulli (Rat01.toNNReal τ) (Rat01.toNNReal_le_one τ)).map
    (fun b => bif b then .factive else .nonfactive)

@[simp] theorem factivityPrior_apply_factive (τ : Rat01) :
    (factivityPrior τ) FactivityReading.factive
      = ((Rat01.toNNReal τ : ℝ≥0) : ℝ≥0∞) := by
  unfold factivityPrior
  simp [PMF.map_apply, PMF.bernoulli_apply]

@[simp] theorem factivityPrior_apply_nonfactive (τ : Rat01) :
    (factivityPrior τ) FactivityReading.nonfactive
      = (((1 : ℝ≥0) - Rat01.toNNReal τ : ℝ≥0) : ℝ≥0∞) := by
  unfold factivityPrior
  simp [PMF.map_apply, PMF.bernoulli_apply]

end Prior

/-! ## §3. The discrete-factivity ParamPred -/

section DiscreteFactivity

variable {W : Type*} [HasBelief W] [HasComplement W]

/-- The discrete-factivity model packaged as a `ParamPred`: Boolean
    semantics dispatched on `FactivityReading`, with a Bernoulli prior over
    that reading. The graded truth value `gradedTruth` is then the
    `ℝ≥0∞`-valued probability mass on the satisfied-readings set —
    `PMF.probOfSet` of the "predicate satisfied at this world" event. -/
noncomputable def discreteFactivityPred (τ : Rat01) :
    ParamPred W FactivityReading where
  semantics := clauseEmbeddingSem
  prior     := factivityPrior τ

/-- Closed-form reduction: graded truth = `τ · 1[factivePos] + (1−τ) · 1[nonFactivePos]`.
    This is the substantive content of the τ-parameterised model — graded
    inference values arise from a τ-weighted mixture of two crisp Boolean
    readings. -/
theorem discreteFactivity_gradedTruth (τ : Rat01) (w : W) :
    (discreteFactivityPred τ).gradedTruth w =
    (if factivePos w then ((Rat01.toNNReal τ : ℝ≥0) : ℝ≥0∞) else 0) +
    (if nonFactivePos (W := W) w
      then (((1 : ℝ≥0) - Rat01.toNNReal τ : ℝ≥0) : ℝ≥0∞) else 0) := by
  classical
  show (factivityPrior τ).probOfSet
      {θ | clauseEmbeddingSem (W := W) θ w = true} = _
  rw [PMF.probOfSet_apply, FactivityReading.sum_univ]
  simp [clauseEmbeddingSem, factivityPrior_apply_factive, factivityPrior_apply_nonfactive,
        Set.mem_setOf_eq]

/-- With τ = 1 (certainly factive), graded truth reduces to `factivePos`. -/
theorem discreteFactivity_certain_factive (w : W) :
    (discreteFactivityPred (W := W) Rat01.one).gradedTruth w =
    if factivePos w then 1 else 0 := by
  rw [discreteFactivity_gradedTruth]
  have hτ : Rat01.toNNReal Rat01.one = 1 := by
    show Real.toNNReal ((1 : ℚ) : ℝ) = 1
    simp
  rw [hτ]
  simp

/-- With τ = 0 (certainly nonfactive), graded truth reduces to `nonFactivePos`. -/
theorem discreteFactivity_certain_nonfactive (w : W) :
    (discreteFactivityPred (W := W) Rat01.zero).gradedTruth w =
    if nonFactivePos (W := W) w then 1 else 0 := by
  rw [discreteFactivity_gradedTruth]
  have hτ : Rat01.toNNReal Rat01.zero = 0 := by
    show Real.toNNReal ((0 : ℚ) : ℝ) = 0
    simp
  rw [hτ]
  simp

/-- Monotonicity in τ: at a world that satisfies the factive reading but
    not the nonfactive reading, increasing τ strictly increases graded
    truth. The hypothesis pattern `factivePos w ∧ ¬ nonFactivePos w` is
    impossible in standard Boolean semantics (`factive_entails_nonfactive`
    rules it out), so this lemma is vacuously achievable; the substantive
    case is the *contrapositive* one supplied by `discreteFactivity_gradedTruth`
    plus monotonicity of the Bernoulli mixture. -/
theorem higher_tau_higher_gradedTruth
    (τ₁ τ₂ : Rat01) (w : W)
    (h_tau : τ₁.val > τ₂.val)
    (h_factive : factivePos w = true)
    (h_nonfactive : nonFactivePos (W := W) w = false) :
    (discreteFactivityPred τ₁).gradedTruth w >
    (discreteFactivityPred τ₂).gradedTruth w := by
  rw [discreteFactivity_gradedTruth, discreteFactivity_gradedTruth]
  simp only [h_factive, h_nonfactive, Bool.false_eq_true, ↓reduceIte, add_zero]
  have hlt : Rat01.toNNReal τ₂ < Rat01.toNNReal τ₁ := by
    have : ((Rat01.toNNReal τ₂ : ℝ≥0) : ℝ) < ((Rat01.toNNReal τ₁ : ℝ≥0) : ℝ) := by
      rw [Rat01.toNNReal_val, Rat01.toNNReal_val]
      exact_mod_cast h_tau
    exact_mod_cast this
  exact_mod_cast hlt

end DiscreteFactivity

/-! ## §4. The 2 × 2 model space -/

section ModelVariants

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

/-! ## §5. Bridge to @cite{scontras-tonhauser-2025} -/

section ScontrasTonhauserBridge

/-- The `factive` reading of `clauseEmbeddingSem` is the same Boolean
    predicate as @cite{scontras-tonhauser-2025}'s `literalMeaning .knowPos`.
    Both unfold to `factivePos` from `Theories.Semantics.Attitudes.Factivity`,
    so the equality is true by construction — a *grounding theorem* in the
    sense of `CLAUDE.md`, witnessing that two paper-specific lexical entries
    share their foundation. -/
theorem clauseEmbedding_factive_eq_st_know :
    clauseEmbeddingSem (W := ScontrasTonhauser2025.WorldState) .factive
      = ScontrasTonhauser2025.literalMeaning .knowPos := rfl

/-- The `nonfactive` reading is @cite{scontras-tonhauser-2025}'s
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
      (discreteFactivityPred Rat01.one).gradedTruth w =
      if ScontrasTonhauser2025.literalMeaning .knowPos w then 1 else 0) ∧
    (∀ w : ScontrasTonhauser2025.WorldState,
      (discreteFactivityPred Rat01.zero).gradedTruth w =
      if ScontrasTonhauser2025.literalMeaning .thinkPos w then 1 else 0) :=
  ⟨discreteFactivity_certain_factive, discreteFactivity_certain_nonfactive⟩

end ScontrasTonhauserBridge

/-! ## §6. Empirical anchoring (D&T 2021/2022) -/

section EmpiricalAnchor

/-- Under the discrete-factivity model with `τ_know > τ_think`, the model
    predicts a `know > think` projection ordering. The empirical ordering
    from @cite{degen-tonhauser-2022} (Exp 1a, sliding scale) confirms this
    direction: aggregate ratings for *know* exceed those for *think*.
    `norm_num` closes the literal comparison since ratings are `ℚ`-valued. -/
theorem empirical_ordering_consistent_with_tau :
    projectionRating_Exp1a .know > projectionRating_Exp1a .think := by
  simp only [projectionRating_Exp1a]; norm_num

/-- The prior-belief modulation finding from @cite{degen-tonhauser-2021},
    replicated in 2b, is the empirical regularity the world-knowledge
    component of the discrete-factivity model is fit to: higher prior
    probability of the complement → stronger projection. -/
theorem prior_effect_consistent :
    (exp1_priorEffect .categorical).β > 0 ∧
    exp2b_priorEffect .categorical = some ⟨0.18, 0.01, 12.81⟩ :=
  prior_effect_replicates

end EmpiricalAnchor

end GroveWhite2025
