/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Merge.MinimalYield
import Linglib.Core.Algebra.RotaBaxterLaurent

/-!
# The δ-grading of Minimal Yield and the polar part (MCB §3.5.2.1)
[marcolli-chomsky-berwick-2025] §3.5.2.1, book p. 267

MCB's §3.5.2 recasts Minimal Yield (Def. 1.6.1) as a Birkhoff factorization in a ring of **Laurent
series** `DM[t⁻¹][[t]]` with coefficients in the algebra of free Merge derivations, weighting each
derivation `F → F'` by `tᵟ` for a **grading** `δ ∈ {δb₀, δα, δσ}`. This file is the grading layer
between `MinimalYield.lean`'s size measures `b₀/α/σ` and the polar-part Rota–Baxter operator
`LaurentSeries.polarHahn` of `RotaBaxterLaurent.lean` (MCB Prop. 3.5.2).

The signed deltas (MCB §3.5.2.1) of a transformation `F → F'`:

  `δb₀ = b₀ F − b₀ F'`,  `δα = α F' − α F`,  `δσ = σ F' − σ F`,

with `σ = b₀ + α` giving `δσ = δα − δb₀`. Minimal Yield (Def. 1.6.1) is exactly
`δb₀ ≥ 0 ∧ δα ≥ 0 ∧ δσ = 1` (no divergence / no information loss / minimality of yield).

The bridge to the polar projection: a derivation graded `tᵟ` lands in the **polar** part (`δ < 0`,
fixed by `R = polarHahn`, the divergent part Birkhoff factorization removes) iff its grading is
negative. Minimal-Yield-respecting steps (External/Internal Merge) have `δ ≥ 0`, hence **nonpolar**
(the per-merge shadow of MCB Lemma 3.5.5); the divergent Sideward Merge steps 3(a)/3(b) have
`δb₀ = −1 < 0`, hence **polar** — the derivations MCB Prop. 3.5.6's factorization eliminates.

## Main definitions

- `Minimalist.Merge.δb₀ / δα / δσ`: the signed `ℤ`-valued gradings.
- `Minimalist.Merge.gradeMonomial`: the Laurent monomial `tᵈ` whose polarity tracks `d`.

## References

[marcolli-chomsky-berwick-2025] (§3.5.2.1, Prop. 3.5.2, Lemma 3.5.5, Prop. 3.5.6)
-/

namespace Minimalist.Merge

open RoseTree RoseTree.Nonplanar LaurentSeries

variable {α β : Type*}

/-! ### The δ-grading (MCB §3.5.2.1) -/

/-- `δb₀ = b₀ F − b₀ F'` (MCB §3.5.2.1): divergence; `≥ 0` is "no divergence". -/
def δb₀ (F F' : Forest (Nonplanar (α ⊕ β))) : ℤ := (Forest.b₀ F : ℤ) - Forest.b₀ F'

/-- `δα = α F' − α F` (MCB §3.5.2.1): information gain; `≥ 0` is "no information loss". -/
def δα (F F' : Forest (Nonplanar (α ⊕ β))) : ℤ := (Forest.alpha F' : ℤ) - Forest.alpha F

/-- `δσ = σ F' − σ F` (MCB §3.5.2.1): yield; `= 1` is "minimality of yield". -/
def δσ (F F' : Forest (Nonplanar (α ⊕ β))) : ℤ := (Forest.sigma F' : ℤ) - Forest.sigma F

/-- The grading consistency relation `δσ = δα − δb₀`, from `σ = b₀ + α`. -/
theorem δσ_eq (F F' : Forest (Nonplanar (α ⊕ β))) : δσ F F' = δα F F' - δb₀ F F' := by
  simp only [δσ, δα, δb₀, Forest.sigma]; push_cast; ring

/-! ### Minimal Yield as the grading conditions (MCB §3.5.2.1) -/

/-- Weak Minimal Yield is exactly `δb₀ ≥ 0 ∧ δα ≥ 0` (MCB §3.5.2.1, "no divergence / no
    information loss"). -/
theorem minimalYieldWeak_iff (F F' : Forest (Nonplanar (α ⊕ β))) :
    MinimalYieldWeak F F' ↔ 0 ≤ δb₀ F F' ∧ 0 ≤ δα F F' := by
  simp only [δb₀, δα]
  constructor
  · rintro ⟨hb, ha⟩; exact ⟨by omega, by omega⟩
  · rintro ⟨hb, ha⟩; exact ⟨by omega, by omega⟩

/-- Minimal Yield is exactly `δb₀ ≥ 0 ∧ δα ≥ 0 ∧ δσ = 1` (MCB §3.5.2.1). -/
theorem minimalYield_iff (F F' : Forest (Nonplanar (α ⊕ β))) :
    MinimalYield F F' ↔ 0 ≤ δb₀ F F' ∧ 0 ≤ δα F F' ∧ δσ F F' = 1 := by
  constructor
  · intro h
    obtain ⟨hb, ha⟩ := (minimalYieldWeak_iff F F').mp h.toMinimalYieldWeak
    have hs := h.minimalYield
    exact ⟨hb, ha, by simp only [δσ]; omega⟩
  · rintro ⟨hb, ha, hs⟩
    refine ⟨(minimalYieldWeak_iff F F').mpr ⟨hb, ha⟩, ?_⟩
    simp only [δσ] at hs; omega

/-! ### The grading monomial and the polar part (bridge to MCB Prop. 3.5.2) -/

variable {A : Type*} [CommRing A]

/-- The Laurent grading monomial `tᵈ` (MCB eq. 3.5.6, coefficient `1`): a derivation graded by `d`
    contributes `tᵈ` to the Laurent-series character. -/
noncomputable def gradeMonomial (d : ℤ) : LaurentSeries A := HahnSeries.single d 1

/-- A graded monomial is **polar** (fixed by `R = polarHahn`) iff its grading is negative, and is
    annihilated by `R` otherwise — the divergent/convergent split of MCB Prop. 3.5.2. -/
theorem polarHahn_gradeMonomial (d : ℤ) :
    polarHahn (gradeMonomial (A := A) d) = if d < 0 then gradeMonomial d else 0 := by
  unfold gradeMonomial
  split_ifs with hd
  · exact polarHahn_eq_self _ fun i hi => HahnSeries.coeff_single_of_ne (by omega)
  · exact polarHahn_eq_zero _ fun i hi => HahnSeries.coeff_single_of_ne (by omega)

/-! ### Per-merge polarity: Minimal Yield is nonpolar, divergent Sideward is polar -/

/-- A weak-Minimal-Yield step is **nonpolar** in the `δb₀` grading: `R` annihilates its monomial
    (`δb₀ ≥ 0`). The External/Internal-Merge shadow of MCB Lemma 3.5.5. -/
theorem polarHahn_gradeMonomial_of_minimalYieldWeak
    (F F' : Forest (Nonplanar (α ⊕ β))) (h : MinimalYieldWeak F F') :
    polarHahn (gradeMonomial (A := A) (δb₀ F F')) = 0 := by
  rw [polarHahn_gradeMonomial, if_neg]
  obtain ⟨hb, _⟩ := (minimalYieldWeak_iff F F').mp h
  omega

/-- External Merge is nonpolar (MCB Lemma 3.5.5): `δb₀ = +1 ≥ 0`, so `R` annihilates its monomial. -/
theorem polarHahn_gradeMonomial_em (lbl : α) (S S' : Nonplanar (α ⊕ β)) :
    polarHahn (gradeMonomial (A := A)
        (δb₀ ({S, S'} : Forest (Nonplanar (α ⊕ β))) {Nonplanar.node (Sum.inl lbl) {S, S'}})) = 0 :=
  polarHahn_gradeMonomial_of_minimalYieldWeak _ _
    (em_pair_satisfiesMinimalYield lbl S S').toMinimalYieldWeak

/-- Sideward Merge 3(a) has divergent grading `δb₀ = −1` (`b₀` increases by one). -/
theorem δb₀_sideward_3a (T_i Tnode T_iq : Nonplanar (α ⊕ β)) :
    δb₀ ({T_i} : Forest (Nonplanar (α ⊕ β))) {Tnode, T_iq} = -1 := by
  simp only [δb₀, sideward_3a_b₀_increases T_i Tnode T_iq]; push_cast; ring

/-- Sideward Merge 3(b) has divergent grading `δb₀ = −1` (`b₀` increases by one). -/
theorem δb₀_sideward_3b (T_i T_j Tnode T_iq T_jq : Nonplanar (α ⊕ β)) :
    δb₀ ({T_i, T_j} : Forest (Nonplanar (α ⊕ β))) {Tnode, T_iq, T_jq} = -1 := by
  simp only [δb₀, sideward_3b_b₀_increases T_i T_j Tnode T_iq T_jq]; push_cast; ring

/-- Sideward Merge 3(a) is **polar** in the `δb₀` grading: `R` fixes its monomial (`δb₀ = −1 < 0`) —
    the divergent derivation MCB Prop. 3.5.6's Birkhoff factorization eliminates. -/
theorem polarHahn_gradeMonomial_sideward_3a (T_i Tnode T_iq : Nonplanar (α ⊕ β)) :
    polarHahn (gradeMonomial (A := A)
        (δb₀ ({T_i} : Forest (Nonplanar (α ⊕ β))) {Tnode, T_iq}))
      = gradeMonomial (δb₀ ({T_i} : Forest (Nonplanar (α ⊕ β))) {Tnode, T_iq}) := by
  rw [polarHahn_gradeMonomial, δb₀_sideward_3a, if_pos (by norm_num : (-1 : ℤ) < 0)]

/-- Sideward Merge 3(b) is **polar** in the `δb₀` grading (`δb₀ = −1 < 0`). -/
theorem polarHahn_gradeMonomial_sideward_3b (T_i T_j Tnode T_iq T_jq : Nonplanar (α ⊕ β)) :
    polarHahn (gradeMonomial (A := A)
        (δb₀ ({T_i, T_j} : Forest (Nonplanar (α ⊕ β))) {Tnode, T_iq, T_jq}))
      = gradeMonomial (δb₀ ({T_i, T_j} : Forest (Nonplanar (α ⊕ β))) {Tnode, T_iq, T_jq}) := by
  rw [polarHahn_gradeMonomial, δb₀_sideward_3b, if_pos (by norm_num : (-1 : ℤ) < 0)]

end Minimalist.Merge
