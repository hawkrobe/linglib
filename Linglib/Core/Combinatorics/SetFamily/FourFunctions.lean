import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.Linarith

/-!
# Correlation inequalities for upper sets

[UPSTREAM] The Fortuin–Kasteleyn–Ginibre inequality (`fkg`) says that under a log-supermodular
weight two monotone functions are positively correlated. This file records its negative form,
obtained by reflecting one of the functions: an antitone and a monotone function are negatively
correlated. Specialising the monotone function to the indicator of an upper set gives the two
reweighting inequalities: under a log-supermodular weight, reweighting by a monotone factor
raises the share of every upper set and reweighting by an antitone factor lowers it.

## References

* [fortuin-kasteleyn-ginibre-1971]
-/

open Finset

variable {α β : Type*} [CommRing β] [LinearOrder β] [IsStrictOrderedRing β] {μ f g : α → β}
  {s : Finset α}

private theorem indicator_nonneg [DecidableEq α] :
    0 ≤ λ a => if a ∈ s then (1 : β) else 0 := λ a => by
  dsimp
  split_ifs <;> simp

private theorem indicator_monotone [Preorder α] [DecidableEq α] (hs : IsUpperSet (s : Set α)) :
    Monotone λ a => if a ∈ s then (1 : β) else 0 := λ a b hab => by
  dsimp
  split_ifs with ha hb
  · exact le_rfl
  · exact absurd (hs hab ha) hb
  · exact zero_le_one
  · exact le_rfl

variable [DistribLattice α] [Fintype α]

/-- Under a log-supermodular weight, an antitone and a monotone function are negatively
correlated. -/
theorem fkg_antitone_monotone (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g) (hf : Antitone f)
    (hg : Monotone g) (hμ : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)) :
    (∑ a, μ a) * ∑ a, μ a * (f a * g a) ≤ (∑ a, μ a * f a) * ∑ a, μ a * g a := by
  have h := fkg (λ a => (∑ b, f b) - f a) g μ hμ₀
    (λ a => sub_nonneg.2 (single_le_sum (λ b _ => hf₀ b) (mem_univ a)))
    hg₀ (λ a b hab => sub_le_sub_left (hf hab) _) hg hμ
  have h₁ : ∑ a, μ a * ((∑ b, f b) - f a) = (∑ b, f b) * ∑ a, μ a - ∑ a, μ a * f a := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  have h₂ : ∑ a, μ a * (((∑ b, f b) - f a) * g a)
      = (∑ b, f b) * ∑ a, μ a * g a - ∑ a, μ a * (f a * g a) := by
    simp only [sub_mul, mul_sub, sum_sub_distrib, mul_left_comm _ (∑ b, f b), ← mul_sum]
  rw [h₁, h₂] at h
  nlinarith [h]

/-- Under a log-supermodular weight, reweighting by a monotone factor raises the share of an
upper set. -/
theorem fkg_monotone_isUpperSet [DecidableEq α] (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f)
    (hf : Monotone f) (hs : IsUpperSet (s : Set α))
    (hμ : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)) :
    (∑ a, μ a * f a) * ∑ a ∈ s, μ a ≤ (∑ a, μ a) * ∑ a ∈ s, μ a * f a := by
  simpa [mul_ite, sum_ite_mem] using
    fkg f (λ a => if a ∈ s then (1 : β) else 0) μ hμ₀ hf₀ indicator_nonneg hf
      (indicator_monotone hs) hμ

/-- Under a log-supermodular weight, reweighting by an antitone factor lowers the share of an
upper set. -/
theorem fkg_antitone_isUpperSet [DecidableEq α] (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f)
    (hf : Antitone f) (hs : IsUpperSet (s : Set α))
    (hμ : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)) :
    (∑ a, μ a) * ∑ a ∈ s, μ a * f a ≤ (∑ a, μ a * f a) * ∑ a ∈ s, μ a := by
  simpa [mul_ite, sum_ite_mem] using
    fkg_antitone_monotone hμ₀ hf₀ indicator_nonneg hf (indicator_monotone hs) hμ
