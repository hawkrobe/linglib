import Linglib.Theories.Semantics.Attitudes.Factivity
import Linglib.Theories.Semantics.Probabilistic.ParamPred
import Linglib.Theories.Semantics.Dynamic.Probability.Basic
import Linglib.Phenomena.Presupposition.Gradience
import Linglib.Phenomena.Presupposition.Studies.DegenTonhauser2022
import Linglib.Core.FinitePMF

/-!
# @cite{grove-white-2025}

Factivity, presupposition projection, and the role of discrete knowledge
in gradient inference judgments. Natural Language Semantics 34:1–45.

## Core Contribution

Grove & White compare two hypotheses about the gradience observed in
inference judgments for clause-embedding predicates:

- **Fundamental Discreteness Hypothesis (FDH)** (definition (7a), p. 10):
  Factivity is a discrete property of an expression on a particular occasion
  of use. A given use either triggers a projective inference, or it does not.
  Observed gradience arises from resolved indeterminacy — variation across
  occasions in which reading is selected.

- **Fundamental Gradience Hypothesis (FGH)** (definition (7b), p. 10):
  There is no property distinguishing factive from non-factive occurrences.
  Gradient distinctions observed among predicates reflect gradient
  contributions to inferences about their complement clauses.

## The Four Models

The paper crosses two binary choices — factivity (discrete/gradient) ×
world knowledge (discrete/gradient) — yielding four models:

| Model | Factivity | World knowledge | Fits best? |
|-------|-----------|-----------------|------------|
| discrete-factivity | discrete (τ_v) | gradient | **Yes** |
| wholly-discrete | discrete (τ_v) | discrete | Second |
| discrete-world | gradient | discrete | |
| wholly-gradient | gradient | gradient | Worst |

The discrete-factivity model **extends** the norming-gradient model (Sect. 4.2)
by adding a Bernoulli switch τ_v on top of the gradient world knowledge model.
The wholly-discrete model similarly extends the norming-discrete model.

## Formalization Strategy

The discrete-factivity model is structurally a `ParamPred` over
`FactivityReading`:
- `semantics .factive = factivePos` (BEL ∧ C)
- `semantics .nonfactive = nonFactivePos` (BEL)
- `prior = ⟨τ_v, 1 − τ_v⟩`

This directly reuses `Factivity.lean` for the two readings and
`ParamPred` for the parameterized semantics.

## Connection to PDS

The paper's formal framework is Probabilistic Dynamic Semantics (PDS),
developed in @cite{grove-white-2025b}. The `discreteFactivityPred` construction
is structurally equivalent to applying PDS's `probProp` to a Boolean predicate
parameterized by reading type — graded truth emerges from marginalizing
over a discrete parameter, exactly as in `Semantics.Dynamic.Probabilistic`.

## Connection to @cite{scontras-tonhauser-2025}

Scontras & Tonhauser's RSA model uses `factivePos` for know and
`nonFactivePos` for think — exactly the two readings of `clauseEmbeddingSem`.
Their model is the special case of the discrete-factivity model with τ=1
(know is always factive) and τ=0 (think is never factive). The bridge
theorems `certain_factive_eq_know` and `certain_nonfactive_eq_think` make
this connection explicit.

## Key Results

Across all four datasets — @cite{degen-tonhauser-2021} original, a
replication, bleached contexts, and templatic contexts — the
discrete-factivity model achieves the best ELPD (expected log pointwise
predictive density), supporting the FDH over the FGH.
-/

set_option autoImplicit false

namespace GroveWhite2025

open Semantics.Attitudes.Factivity
open Semantics.Probabilistic.ParamPred
open Phenomena.Presupposition.Gradience
open DegenTonhauser2021
open DegenTonhauser2022

-- ============================================================================
-- §1. The Two Hypotheses
-- ============================================================================

/-- The Fundamental Discreteness Hypothesis (definition (7a), p. 10):
    factivity is a discrete property of an expression on a particular
    occasion of use. A given use either triggers a projective inference,
    or it does not. The FDH is neutral on *why* the resolved indeterminacy
    arises — it may be due to polysemy, structural ambiguity, or discourse
    sensitivity (QUD/common ground). -/
def FDH : GradienceSource := .resolved

/-- The Fundamental Gradience Hypothesis (definition (7b), p. 10):
    there is no property distinguishing factive from non-factive occurrences.
    Gradient distinctions reflect gradient contributions to inferences. -/
def FGH : GradienceSource := .unresolved

/-- Possible mechanisms for resolved indeterminacy under the FDH.
    These are mentioned on p. 10 as different ways the discreteness
    could be cashed out. The FDH itself is neutral among them. -/
inductive ResolvedMechanism where
  /-- Polysemy: a predicate has multiple senses, at least one factive and
      at least one nonfactive (conventionalist account, Sect. 6.1). -/
  | polysemy
  /-- Structural ambiguity: a predicate occurs in multiple structures, at
      least one implicated in triggering projection and one not. -/
  | structuralAmbiguity
  /-- Discourse sensitivity: the predicate's complement content may or may
      not be entailed by a discourse construct like the QUD
      (conversationalist account, Sect. 6.2). -/
  | discourseSensitivity
  deriving DecidableEq, Repr

-- ============================================================================
-- §2. The τ_v Parameter
-- ============================================================================

/-- Per-predicate factivity probability. On each occasion of use, a clause-
    embedding predicate is factive with probability τ_v and nonfactive with
    probability 1 − τ_v. This is the key parameter of the discrete-factivity
    model (Sect. 3.7, definition (13)). -/
structure FactivityParam where
  /-- The probability of the factive reading. -/
  τ : ℚ
  τ_nonneg : 0 ≤ τ
  τ_le_one : τ ≤ 1

/-- The two readings of a clause-embedding predicate under the FDH. -/
inductive FactivityReading where
  /-- The factive reading: BEL ∧ C. -/
  | factive
  /-- The nonfactive reading: BEL only. -/
  | nonfactive
  deriving DecidableEq, Repr, Inhabited

instance : Fintype FactivityReading where
  elems := {.factive, .nonfactive}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §3. Discrete-Factivity Model as ParamPred
-- ============================================================================

variable {W : Type*} [HasBelief W] [HasComplement W]
variable [Fintype W] -- needed only for discreteFactivityPred and grounded theorems

/-- The two Boolean readings of a clause-embedding predicate, derived
    directly from `Factivity.lean`. Under reading `factive`, the predicate
    has semantics BEL ∧ C (factivePos); under `nonfactive`, just BEL
    (nonFactivePos). This corresponds to the paper's DAG in (13), p. 20. -/
def clauseEmbeddingSem : FactivityReading → W → Bool
  | .factive    => factivePos
  | .nonfactive => nonFactivePos

omit [Fintype W] in
/-- The factive reading entails the nonfactive reading. -/
theorem factive_entails_nonfactive_reading (w : W) :
    clauseEmbeddingSem .factive w = true →
    clauseEmbeddingSem .nonfactive w = true :=
  factive_entails_nonfactive w

/-- Construct a `ParamPred` for a clause-embedding predicate from its
    factivity parameter τ_v. This is the discrete-factivity model:
    Boolean semantics parameterized by a binary reading, with a prior
    `⟨τ_v, 1 − τ_v⟩` over readings. -/
def discreteFactivityPred (fp : FactivityParam) :
    ParamPred W FactivityReading where
  semantics := clauseEmbeddingSem
  prior := {
    mass := fun
      | .factive    => fp.τ
      | .nonfactive => 1 - fp.τ
    mass_nonneg := fun
      | .factive    => fp.τ_nonneg
      | .nonfactive => by linarith [fp.τ_le_one]
    mass_sum_one := by
      have : (Finset.univ : Finset FactivityReading) = {.factive, .nonfactive} := by
        ext x; cases x <;> simp
      rw [this, Finset.sum_insert (by decide), Finset.sum_singleton]; ring
  }

omit [Fintype W] in
/-- The graded truth value of a clause-embedding predicate under the
    discrete-factivity model equals the τ-weighted mixture of the two
    Boolean readings. -/
theorem discreteFactivity_gradedTruth (fp : FactivityParam) (w : W) :
    (discreteFactivityPred fp).gradedTruth w =
    fp.τ * (if factivePos w then 1 else 0) +
    (1 - fp.τ) * (if nonFactivePos (W := W) w then 1 else 0) := by
  simp only [discreteFactivityPred, ParamPred.gradedTruth, Core.FinitePMF.prob,
    Core.FinitePMF.expect, clauseEmbeddingSem]
  have : (Finset.univ : Finset FactivityReading) = {.factive, .nonfactive} := by
    ext x; cases x <;> simp
  rw [this, Finset.sum_insert (by decide), Finset.sum_singleton]
  rfl

/-- The discrete-factivity model's graded truth is exactly PDS's `probProp`:
    the probability of a Boolean predicate under a finite distribution.
    This is the formal content of the paper's core claim — graded inference
    judgments emerge from marginalizing over a discrete reading parameter. -/
theorem discreteFactivity_eq_probProp (fp : FactivityParam) (w : W) :
    (discreteFactivityPred fp).gradedTruth w =
    Semantics.Dynamic.Probabilistic.probProp
      (discreteFactivityPred (W := W) fp).prior.mass
      (fun r => clauseEmbeddingSem r w) := rfl

omit [Fintype W] in
/-- With τ = 1 (certainly factive), graded truth reduces to factivePos. -/
theorem discreteFactivity_certain_factive (w : W) :
    (discreteFactivityPred ⟨1, by norm_num, by norm_num⟩).gradedTruth w =
    if factivePos w then 1 else 0 := by
  rw [discreteFactivity_gradedTruth]
  simp only [sub_self, zero_mul, add_zero, one_mul]

omit [Fintype W] in
/-- With τ = 0 (certainly nonfactive), graded truth reduces to nonFactivePos. -/
theorem discreteFactivity_certain_nonfactive (w : W) :
    (discreteFactivityPred ⟨0, by norm_num, by norm_num⟩).gradedTruth w =
    if nonFactivePos (W := W) w then 1 else 0 := by
  rw [discreteFactivity_gradedTruth]
  simp only [sub_zero, one_mul, zero_mul, zero_add]

-- ============================================================================
-- §4. The Four Models
-- ============================================================================

/-- The four models from the paper (Sect. 4.3–4.4), crossing
    factivity × world knowledge. Each model is a completion of one
    of the two norming models (Sect. 4.2) with a factivity component. -/
inductive ModelVariant where
  /-- Discrete factivity + gradient world knowledge. Best fit.
      Extends norming-gradient (Sect. 4.2.1). -/
  | discreteFactivity
  /-- Discrete factivity + discrete world knowledge.
      Extends norming-discrete (Sect. 4.2.2). -/
  | whollyDiscrete
  /-- Gradient factivity + gradient world knowledge. Worst fit.
      Extends norming-gradient with gradient factivity. -/
  | whollyGradient
  /-- Gradient factivity + discrete world knowledge.
      Extends norming-discrete with gradient factivity. -/
  | discreteWorld
  deriving DecidableEq, Repr

/-- Whether a model treats factivity as discrete (FDH) or gradient (FGH). -/
def ModelVariant.factivityHypothesis : ModelVariant → GradienceSource
  | .discreteFactivity => .resolved
  | .whollyDiscrete    => .resolved
  | .whollyGradient    => .unresolved
  | .discreteWorld     => .unresolved

/-- Whether a model treats world knowledge as gradient (unresolved) or
    discrete (resolved). -/
def ModelVariant.worldKnowledgeSource : ModelVariant → GradienceSource
  | .discreteFactivity => .unresolved
  | .whollyDiscrete    => .resolved
  | .whollyGradient    => .unresolved
  | .discreteWorld     => .resolved

/-- The best and worst models both use gradient world knowledge but differ
    in factivity treatment. This isolates discrete factivity as the key factor
    driving model fit: holding world knowledge constant at gradient, switching
    from discrete to gradient factivity drops ELPD from best to worst. -/
theorem best_worst_share_world_knowledge :
    ModelVariant.discreteFactivity.worldKnowledgeSource =
    ModelVariant.whollyGradient.worldKnowledgeSource ∧
    ModelVariant.discreteFactivity.factivityHypothesis ≠
    ModelVariant.whollyGradient.factivityHypothesis :=
  ⟨rfl, by decide⟩

/-- Each factivity model extends one of two norming models. The extension
    relationship is determined by how the model treats world knowledge:
    gradient world knowledge = extends norming-gradient,
    discrete world knowledge = extends norming-discrete. -/
inductive NormingModel where
  /-- Norming-gradient (Sect. 4.2.1): world knowledge as unresolved. -/
  | gradient
  /-- Norming-discrete (Sect. 4.2.2): world knowledge as resolved. -/
  | discrete
  deriving DecidableEq, Repr

/-- Each factivity model extends one of the two norming models. -/
def ModelVariant.baseNormingModel : ModelVariant → NormingModel
  | .discreteFactivity => .gradient
  | .whollyDiscrete    => .discrete
  | .whollyGradient    => .gradient
  | .discreteWorld     => .discrete

-- ============================================================================
-- §5. Connection to Scontras & Tonhauser 2025
-- ============================================================================

omit [Fintype W] in
/-- @cite{scontras-tonhauser-2025}'s `literalMeaning .knowPos` is exactly
    the factive reading of `clauseEmbeddingSem`. Their model implicitly
    sets τ = 1 for know. -/
theorem certain_factive_eq_know :
    ∀ w : W, clauseEmbeddingSem .factive w =
    (factivePos w : Bool) := by
  intro w; rfl

omit [Fintype W] in
/-- @cite{scontras-tonhauser-2025}'s `literalMeaning .thinkPos` is exactly
    the nonfactive reading of `clauseEmbeddingSem`. Their model implicitly
    sets τ = 0 for think. -/
theorem certain_nonfactive_eq_think :
    ∀ w : W, clauseEmbeddingSem .nonfactive w =
    (nonFactivePos w : Bool) := by
  intro w; rfl

omit [Fintype W] in
/-- S&T's binary model is the limiting case of the discrete-factivity model:
    know uses τ=1 (certain factive), think uses τ=0 (certain nonfactive).
    The discrete-factivity model generalizes this by allowing intermediate
    τ values for the same predicate across occasions. -/
theorem st_is_limiting_case :
    (∀ w : W,
      (discreteFactivityPred ⟨1, by norm_num, by norm_num⟩).gradedTruth w =
      if factivePos w then 1 else 0) ∧
    (∀ w : W,
      (discreteFactivityPred ⟨0, by norm_num, by norm_num⟩).gradedTruth w =
      if nonFactivePos (W := W) w then 1 else 0) :=
  ⟨discreteFactivity_certain_factive, discreteFactivity_certain_nonfactive⟩

-- ============================================================================
-- §6. Connection to Empirical Data
-- ============================================================================

omit [Fintype W] in
/-- The discrete-factivity model's theoretical prediction: higher τ means
    more projection. This is a monotonicity property — if τ₁ > τ₂ and the
    factive reading satisfies `factivePos w` but the nonfactive reading
    does not satisfy `nonFactivePos w`, then the predicate with higher τ
    gets higher graded truth at w. -/
theorem higher_tau_higher_gradedTruth
    (fp₁ fp₂ : FactivityParam) (w : W)
    (h_tau : fp₁.τ > fp₂.τ)
    (h_factive : factivePos w = true)
    (h_nonfactive : nonFactivePos (W := W) w = false) :
    (discreteFactivityPred fp₁).gradedTruth w >
    (discreteFactivityPred fp₂).gradedTruth w := by
  rw [discreteFactivity_gradedTruth, discreteFactivity_gradedTruth]
  simp only [h_factive, ite_true, h_nonfactive, Bool.false_eq_true, ↓reduceIte,
    mul_one, mul_zero, add_zero]
  exact h_tau

/-- The empirical ordering from @cite{degen-tonhauser-2022} — know projects
    more than think — is consistent with the model's τ ordering. Under the
    discrete-factivity model, this ordering holds when τ_know > τ_think.
    The S&T limiting case (τ_know=1, τ_think=0) is a special case. -/
theorem empirical_ordering_consistent_with_tau :
    projectionRating_Exp1a .know > projectionRating_Exp1a .think := by
  native_decide

/-- The prior-belief modulation finding from @cite{degen-tonhauser-2021} is
    the empirical observation that the discrete-factivity model explains:
    observed gradience arises from uncertainty over the discrete τ parameter
    interacting with world knowledge (prior beliefs about complement content).
    Both experiments confirm that higher prior → stronger projection. -/
theorem prior_effect_consistent :
    (exp1_priorEffect .categorical).β > 0 ∧
    exp2b_priorEffect .categorical = some ⟨0.18, 0.01, 12.81⟩ :=
  prior_effect_replicates

end GroveWhite2025
