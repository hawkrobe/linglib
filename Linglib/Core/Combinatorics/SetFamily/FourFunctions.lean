import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Negative correlation of antitone and monotone functions

[UPSTREAM] The Fortuin–Kasteleyn–Ginibre inequality (`fkg`) says that under a log-supermodular
weight two monotone functions are positively correlated. Replacing one of them by its
reflection gives the negative form: an antitone and a monotone function are negatively
correlated, so reweighting by an antitone factor lowers the mass of every upper set.
-/

open Finset

variable {α β : Type*} [DistribLattice α] [Fintype α] [CommRing β] [LinearOrder β]
  [IsStrictOrderedRing β] {μ f g : α → β}

/-- Under a log-supermodular weight, an antitone and a monotone function are negatively
correlated. -/
theorem fkg_antitone_monotone (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g) (hf : Antitone f)
    (hg : Monotone g) (hμ : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)) :
    (∑ a, μ a) * ∑ a, μ a * (f a * g a) ≤ (∑ a, μ a * f a) * ∑ a, μ a * g a := by
  have h := fkg (fun a => (∑ b, f b) - f a) g μ hμ₀
    (fun a => sub_nonneg.2 (single_le_sum (fun b _ => hf₀ b) (mem_univ a)))
    hg₀ (fun a b hab => sub_le_sub_left (hf hab) _) hg hμ
  have h₁ : ∑ a, μ a * ((∑ b, f b) - f a) = (∑ b, f b) * ∑ a, μ a - ∑ a, μ a * f a := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  have h₂ : ∑ a, μ a * (((∑ b, f b) - f a) * g a)
      = (∑ b, f b) * ∑ a, μ a * g a - ∑ a, μ a * (f a * g a) := by
    simp only [sub_mul, mul_sub, sum_sub_distrib, mul_left_comm _ (∑ b, f b), ← mul_sum]
  rw [h₁, h₂] at h
  nlinarith [h]
