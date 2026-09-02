/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Merge.MinimalYield
import Linglib.Core.Algebra.RotaBaxterLaurent

/-!
# The gradings of Minimal Yield and the polar part

Minimal Yield can be restated as a Birkhoff factorization in the ring of Laurent series
`DM[t⁻¹][[t]]` over the algebra of free Merge derivations, weighting a transformation `F → F'` of
workspaces by `tᵟ` for a grading `δ` read off the size measures of `MinimalYield.lean`. In this file
we define the three gradings

  `δb₀ F F' = b₀ F − b₀ F'`,  `δα F F' = α F' − α F`,  `δσ F F' = σ F' − σ F`,

with `δσ = δα − δb₀` since `σ = b₀ + α`, and show that Minimal Yield is exactly
`0 ≤ δb₀ ∧ 0 ≤ δα ∧ δσ = 1` (no divergence, no information loss, minimality of yield).

The grading meets the polar-part operator `R = LaurentSeries.polarHahn` through the monomial `tᵟ`,
which is nonpolar iff `0 ≤ δ` (`LaurentSeries.polarHahn_single_eq_zero_iff`). Hence a
transformation satisfies weak Minimal Yield iff its `δb₀`- and `δα`-monomials are both nonpolar
(`minimalYieldWeak_iff_polarHahn`): External and Internal Merge are nonpolar, while the divergent
forms of Sideward Merge, which raise `b₀`, are polar — the terms Birkhoff factorization removes.
Summing monomials over a family of transformations, as the intermediate-derivation character `ψt`
does, the polar part is the sum over the divergent ones (`LaurentSeries.polarHahn_sum_map_single`).

## Main definitions

* `Minimalist.Merge.δb₀`, `Minimalist.Merge.δα`, `Minimalist.Merge.δσ`: the signed gradings.

## Main results

* `Minimalist.Merge.minimalYield_iff`: Minimal Yield as sign conditions on the gradings.
* `Minimalist.Merge.minimalYieldWeak_iff_polarHahn`: weak Minimal Yield as nonpolarity.

## References

* [marcolli-chomsky-berwick-2025], §3.5.2.1–3.5.2.2
-/

namespace Minimalist.Merge

open RoseTree RoseTree.Nonplanar LaurentSeries

variable {α β A : Type*} [CommRing A] (F F' : Forest (Nonplanar (α ⊕ β)))

/-! ### The gradings -/

/-- `δb₀ F F' = b₀ F − b₀ F'`, nonnegative iff `F → F'` does not diverge. -/
def δb₀ : ℤ := (Forest.b₀ F : ℤ) - Forest.b₀ F'

/-- `δα F F' = α F' − α F`, nonnegative iff `F → F'` loses no information. -/
def δα : ℤ := (Forest.alpha F' : ℤ) - Forest.alpha F

/-- `δσ F F' = σ F' − σ F`, equal to `1` iff `F → F'` has minimal yield. -/
def δσ : ℤ := (Forest.sigma F' : ℤ) - Forest.sigma F

theorem δσ_eq : δσ F F' = δα F F' - δb₀ F F' := by
  simp only [δσ, δα, δb₀, Forest.sigma]; omega

/-! ### Minimal Yield as sign conditions -/

theorem minimalYieldWeak_iff : MinimalYieldWeak F F' ↔ 0 ≤ δb₀ F F' ∧ 0 ≤ δα F F' := by
  simp only [δb₀, δα, sub_nonneg, Nat.cast_le]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem minimalYield_iff :
    MinimalYield F F' ↔ 0 ≤ δb₀ F F' ∧ 0 ≤ δα F F' ∧ δσ F F' = 1 := by
  rw [← and_assoc, ← minimalYieldWeak_iff, δσ, sub_eq_iff_eq_add']
  exact ⟨fun h => ⟨h.1, by exact_mod_cast h.2⟩, fun h => ⟨h.1, by exact_mod_cast h.2⟩⟩

/-! ### Nonpolarity -/

/-- Weak Minimal Yield holds iff the `δb₀`- and `δα`-monomials of `F → F'` are both nonpolar. -/
theorem minimalYieldWeak_iff_polarHahn [Nontrivial A] :
    MinimalYieldWeak F F' ↔
      polarHahn (HahnSeries.single (δb₀ F F') (1 : A)) = 0 ∧
        polarHahn (HahnSeries.single (δα F F') (1 : A)) = 0 := by
  simp only [minimalYieldWeak_iff, polarHahn_single_eq_zero_iff one_ne_zero]

end Minimalist.Merge
