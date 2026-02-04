import Linglib.Core.GradedProposition
import Linglib.Theories.Montague.BayesianSemantics
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Model
import Linglib.Theories.RSA.Core.Noise
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Fintype.Basic

/-! # Conjectures

Unproven theorems requiring further work. Once proven, these should migrate
to their proper homes in the library.
-/

namespace Conjectures

open Core.GradedProposition
open Theories.Montague.BayesianSemantics

/-! ## Graded Semantics

Conjectures about the relationship between graded/probabilistic semantics
and Boolean semantics with noise/uncertainty.
-/

section GradedSemantics

variable {E : Type*} [DecidableEq E]

/-- Graded predicate = expectation over Boolean predicates. -/
theorem graded_from_boolean_expectation
    {Θ : Type*} [Fintype Θ] [DecidableEq Θ]
    (prior : FinitePMF Θ) (P : Θ → E → Bool) (x : E) :
    (ParamPred.mk P prior).gradedTruth x =
    prior.expect (fun θ => if P θ x then 1 else 0) := rfl

/-- Threshold predicate = exceedance probability. -/
theorem threshold_is_exceedance_probability
    {Θ : Type*} [Fintype Θ] [DecidableEq Θ] [Preorder Θ]
    [DecidableRel (· < · : Θ → Θ → Prop)]
    (pred : ThresholdPred E Θ) (x : E) :
    pred.gradedTruth x =
    pred.thresholdPrior.prob (fun θ => pred.measure x > θ) := rfl

/-- Point mass prior (no uncertainty) gives Boolean semantics. -/
theorem no_uncertainty_is_boolean
    {Θ : Type*} [Fintype Θ] [DecidableEq Θ]
    (P : Θ → E → Bool) (θ₀ : Θ) (x : E) :
    (ParamPred.mk P (FinitePMF.pure θ₀)).gradedTruth x =
    if P θ₀ x then 1 else 0 := by
  simp only [ParamPred.gradedTruth, FinitePMF.prob, FinitePMF.expect_pure]

end GradedSemantics

/-! ## RSA Dynamics

The main RSA convergence conjectures are in `RSA.Core.Model`:
- `G_α_monotone_generic`: G_α is monotonically non-decreasing
- `RSA_converges_generic`: RSA converges to a fixed point
- `utility_can_decrease_generic`: Utility can decrease for α < 1
- `eventually_εConverged_generic`: RSA is eventually ε-converged

Additional conjectures about limiting behavior:
-/

section RSADynamics

open RSA

/-- At α → ∞, speaker becomes deterministic (assigns all prob to best utterance). -/
theorem high_rationality_deterministic
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (φ : U → W → ℚ) (prior : W → ℚ) :
    ∀ ε > 0, ∃ α₀ : ℚ, ∀ α > α₀, ∀ (w : W) (u : U),
      True := by  -- S_α(u|w) → 1[u = argmax]
  sorry

/-- At α = 0, speaker samples uniformly. -/
theorem zero_rationality_uniform
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    [Nonempty U]
    (φ : U → W → ℚ) (prior : W → ℚ) :
    ∀ (w : W) (u : U), True := by  -- S_0(u|w) = 1/|U|
  sorry

/-- RSA finds optimal rate-distortion trade-off (Zaslavsky main result). -/
theorem RSA_rate_distortion_optimal
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (α : ℝ) (hα : α > 0) :
    True := by  -- RSA fixed point minimizes H(U|W) + α·D(S)
  sorry

end RSADynamics

/-! ## Compositionality

Conjectures about how pragmatic inference interacts with compositional semantics.
-/

section Compositionality

/-- Different compositional derivations yielding same φ give same RSA predictions. -/
theorem grounded_equals_stipulated
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (φ₁ φ₂ : U → W → ℚ) (h : φ₁ = φ₂) (prior : W → ℚ) (α : ℚ) :
    -- RSA(φ₁, prior, α) = RSA(φ₂, prior, α)
    True := by
  sorry

/-- RSA does NOT preserve semantic entailment (counterexample: scalar implicature). -/
theorem RSA_breaks_entailment
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W] :
    ∃ (φ : U → W → ℚ) (prior : W → ℚ) (u₁ u₂ : U),
      (∀ w, φ u₁ w ≤ φ u₂ w) ∧  -- u₁ semantically entails u₂
      ∃ (w : W), True := by  -- but L₁(w|u₁) > L₁(w|u₂) for some w
  sorry

end Compositionality

/-! ## Theory Unification

Conjectures connecting different theoretical frameworks.
-/

section TheoryUnification

/-- RSA scalar implicature ≈ grammatical exhaustification. -/
theorem scalar_implicature_is_exhaustification
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (some_ all_ : U) (φ : U → W → ℚ) (prior : W → ℚ) :
    -- For Horn-scale items: L₁("some") ≈ ⟦Exh(some)⟧
    True := by
  sorry

/-- Lexical uncertainty = mixture over grammars/lexicons. -/
theorem lexical_uncertainty_is_mixture
    {U W Lex : Type*} [Fintype U] [Fintype W] [Fintype Lex]
    [DecidableEq U] [DecidableEq W] [DecidableEq Lex]
    (φ : Lex → U → W → ℚ) (lexPrior : Lex → ℚ) (prior : W → ℚ) :
    -- L₁_lexUnc(w|u) = E_lex[L₁_lex(w|u)]
    True := by
  sorry

end TheoryUnification

/-! ## Noise and Discrimination

Conjectures about noise channels and their effects on informativeness.
-/

section NoiseDiscrimination

open RSA.Noise

/-- Product discrimination is monotone in individual channel gaps. -/
theorem product_discrimination_monotone
    (match₁ mismatch₁ match₂ mismatch₂ : ℚ)
    (sizeMatch sizeMismatch : ℚ)
    (h_gap : match₁ - mismatch₁ ≥ match₂ - mismatch₂)
    (h_size_nonneg : sizeMatch ≥ 0 ∧ sizeMismatch ≥ 0)
    (h_size_order : sizeMatch ≥ sizeMismatch) :
    match₁ * sizeMatch - mismatch₁ * sizeMismatch ≥
    match₂ * sizeMatch - mismatch₂ * sizeMismatch := by
  sorry

end NoiseDiscrimination

end Conjectures
