import Linglib.Core.GradedProposition
import Linglib.Theories.Montague.BayesianSemantics
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Model
import Linglib.Theories.RSA.Core.Noise
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Conjectures

Unproven theorems. Once proven, migrate to proper homes in the library.
-/

namespace Conjectures

open Core.GradedProposition
open Theories.Montague.BayesianSemantics


section GradedSemantics

variable {E : Type*} [DecidableEq E]

theorem graded_from_boolean_expectation
    {Θ : Type*} [Fintype Θ] [DecidableEq Θ]
    (prior : FinitePMF Θ) (P : Θ → E → Bool) (x : E) :
    (ParamPred.mk P prior).gradedTruth x =
    prior.expect (λ θ => if P θ x then 1 else 0) := rfl

theorem threshold_is_exceedance_probability
    {Θ : Type*} [Fintype Θ] [DecidableEq Θ] [Preorder Θ]
    [DecidableRel (· < · : Θ → Θ → Prop)]
    (pred : ThresholdPred E Θ) (x : E) :
    pred.gradedTruth x =
    pred.thresholdPrior.prob (λ θ => pred.measure x > θ) := rfl

theorem no_uncertainty_is_boolean
    {Θ : Type*} [Fintype Θ] [DecidableEq Θ]
    (P : Θ → E → Bool) (θ₀ : Θ) (x : E) :
    (ParamPred.mk P (FinitePMF.pure θ₀)).gradedTruth x =
    if P θ₀ x then 1 else 0 := by
  simp only [ParamPred.gradedTruth, FinitePMF.prob, FinitePMF.expect_pure]

end GradedSemantics


section RSADynamics

open RSA

theorem high_rationality_deterministic
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (φ : U → W → ℚ) (prior : W → ℚ) :
    ∀ ε > 0, ∃ α₀ : ℚ, ∀ α > α₀, ∀ (w : W) (u : U),
      True := by
  sorry

theorem zero_rationality_uniform
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    [Nonempty U]
    (φ : U → W → ℚ) (prior : W → ℚ) :
    ∀ (w : W) (u : U), True := by
  sorry

theorem RSA_rate_distortion_optimal
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (α : ℝ) (hα : α > 0) :
    True := by
  sorry

end RSADynamics


section Compositionality

theorem grounded_equals_stipulated
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (φ₁ φ₂ : U → W → ℚ) (h : φ₁ = φ₂) (prior : W → ℚ) (α : ℚ) :
    True := by
  sorry

theorem RSA_breaks_entailment
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W] :
    ∃ (φ : U → W → ℚ) (prior : W → ℚ) (u₁ u₂ : U),
      (∀ w, φ u₁ w ≤ φ u₂ w) ∧
      ∃ (w : W), True := by
  sorry

end Compositionality


section TheoryUnification

theorem scalar_implicature_is_exhaustification
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (some_ all_ : U) (φ : U → W → ℚ) (prior : W → ℚ) :
    True := by
  sorry

theorem lexical_uncertainty_is_mixture
    {U W Lex : Type*} [Fintype U] [Fintype W] [Fintype Lex]
    [DecidableEq U] [DecidableEq W] [DecidableEq Lex]
    (φ : Lex → U → W → ℚ) (lexPrior : Lex → ℚ) (prior : W → ℚ) :
    True := by
  sorry

end TheoryUnification


section NoiseDiscrimination

open RSA.Noise

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
