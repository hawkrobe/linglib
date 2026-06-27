/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Merge.MinimalYieldGrading

/-!
# The intermediate-derivation character ψt and Sideward detection (MCB Cor. 3.5.4)
[marcolli-chomsky-berwick-2025] §3.5.2.2, eq. (3.5.7)

The character `ϕt` of Prop. 3.5.3 only weights the *complete* construction `L(T) → T`, whose grading
is always `≥ 0` (MCB Lemma 3.5.5) — so `ϕt` is nonpolar and cannot detect Sideward Merge. Cor. 3.5.4
introduces

  `ψt(T) = Σ_{(F,F') ∈ FT} (F → F') · t^{δ(F→F')}`,

summing over **all intermediate derivation pairs** `(F, F')` in the construction of `T` (forests with
`L(F) = L(F') = L(T)` lying on some chain `L(T) → ⋯ → F → ⋯ → F' → ⋯ → T`). Since `δ` depends only on
the endpoints (`δb₀(F→F') = b₀ F − b₀ F'`, etc.), each segment contributes a single grading monomial.

This file is the **lean t-grading model** of `ψt`, parameterized by the multiset of intermediate
segments `S` (the full `FT`-enumeration engine — derivation reachability for a target — is deferred;
here `S` is the input). The essential content of Cor. 3.5.4 — and the reason `ψt` succeeds where `ϕt`
fails — is captured by `polarHahn_psiSeries`: **the polar (divergent) part of `ψt` is exactly the sum
over its Sideward-divergent segments** (`δb₀ < 0`, where `b₀` increases — MCB's Sideward types
3(a)/3(b)). A single Sideward segment already makes `ψt` polar (`polarHahn_psiSeries_sideward_3a`),
which the Birkhoff factorization then renormalizes away (`Core/Algebra/RootedTree/BirkhoffLaurent`).

## Main definitions

- `Minimalist.Merge.psiSeries`: `ψt` as a graded sum over a given segment multiset.

## References

[marcolli-chomsky-berwick-2025] (Cor. 3.5.4, eq. 3.5.7; Lemma 3.5.5; Prop. 3.5.6)
-/

namespace Minimalist.Merge

open RootedTree LaurentSeries

variable {α β : Type*} {R : Type*} [CommRing R]

/-- A workspace transformation (intermediate derivation segment) `F → F'`. -/
abbrev Segment (α β : Type*) :=
  Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β))

/-- **`ψt` in the lean t-grading model** (MCB eq. 3.5.7, `δ = δb₀`): a graded sum `Σ tᵟ` over the
    multiset `S` of intermediate derivation segments of a target. -/
noncomputable def psiSeries (S : Multiset (Segment α β)) : LaurentSeries R :=
  (S.map (fun p => gradeMonomial (δb₀ p.1 p.2))).sum

@[simp] theorem psiSeries_zero : psiSeries (R := R) (0 : Multiset (Segment α β)) = 0 := by
  simp [psiSeries]

@[simp] theorem psiSeries_cons (p : Segment α β) (S : Multiset (Segment α β)) :
    psiSeries (R := R) (p ::ₘ S) = gradeMonomial (δb₀ p.1 p.2) + psiSeries S := by
  simp [psiSeries]

@[simp] theorem psiSeries_singleton (p : Segment α β) :
    psiSeries (R := R) {p} = gradeMonomial (δb₀ p.1 p.2) := by simp [psiSeries]

@[simp] theorem psiSeries_add (S T : Multiset (Segment α β)) :
    psiSeries (R := R) (S + T) = psiSeries S + psiSeries T := by
  simp [psiSeries, Multiset.map_add, Multiset.sum_add]

/-! ### The polar part of ψt is exactly the divergent (Sideward) segments -/

/-- **The polar (divergent) part of `ψt`** (MCB §3.5.2.2): `R·ψt` is the sum of grading monomials
    over exactly the **Sideward-divergent** segments (`δb₀ < 0`, i.e. `b₀` increases). The polar part
    detects Sideward Merge — the property `ϕt` lacks (Lemma 3.5.5). -/
theorem polarHahn_psiSeries (S : Multiset (Segment α β)) :
    polarHahn (psiSeries (R := R) S) = psiSeries (S.filter (fun p => δb₀ p.1 p.2 < 0)) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons p S ih =>
    rw [psiSeries_cons, polarHahn_add, ih, polarHahn_gradeMonomial]
    by_cases h : δb₀ p.1 p.2 < 0 <;> simp [h]

/-- If every intermediate segment respects no-divergence (`δb₀ ≥ 0`), then `ψt` is **nonpolar** —
    the `ϕt`-like case (a construction using only External/Internal Merge). -/
theorem polarHahn_psiSeries_eq_zero (S : Multiset (Segment α β))
    (h : ∀ p ∈ S, 0 ≤ δb₀ p.1 p.2) : polarHahn (psiSeries (R := R) S) = 0 := by
  rw [polarHahn_psiSeries,
    Multiset.filter_eq_nil.mpr fun p hp => not_lt.mpr (h p hp), psiSeries_zero]

/-- **The nonpolar projection `(1 − R)·ψt` keeps exactly the non-divergent segments** (`δb₀ ≥ 0` —
    the External/Internal/Minimal-Yield-respecting derivations). At the level of a single target's
    series this projection already separates the good derivations from the Sideward-divergent ones;
    the subtlety MCB Prop. 3.5.6 addresses is that `1 − R` fails to do this on the *character* level
    (products of series), where the full Birkhoff factorization is needed because `R` is not an
    algebra homomorphism. -/
theorem psiSeries_sub_polarHahn (S : Multiset (Segment α β)) :
    psiSeries (R := R) S - polarHahn (psiSeries S)
      = psiSeries (S.filter (fun p => ¬ δb₀ p.1 p.2 < 0)) := by
  have hpart : psiSeries (R := R) S
      = psiSeries (S.filter (fun p => δb₀ p.1 p.2 < 0))
        + psiSeries (S.filter (fun p => ¬ δb₀ p.1 p.2 < 0)) := by
    rw [← psiSeries_add, Multiset.filter_add_not]
  rw [polarHahn_psiSeries, hpart]; abel

/-- **A single Sideward 3(a) segment already makes `ψt` polar** (`δb₀ = −1`): its whole value is the
    divergent monomial `t⁻¹`. This is the contrast with `ϕt` (always nonpolar) — `ψt` sees the
    Sideward Merge, which the Birkhoff factorization then removes. -/
theorem polarHahn_psiSeries_sideward_3a (T_i Tnode T_iq : Nonplanar (α ⊕ β)) :
    polarHahn (psiSeries (R := R)
        {(({T_i} : Forest (Nonplanar (α ⊕ β))), ({Tnode, T_iq} : Forest (Nonplanar (α ⊕ β))))})
      = gradeMonomial (-1 : ℤ) := by
  rw [psiSeries, Multiset.map_singleton, Multiset.sum_singleton, δb₀_sideward_3a,
    polarHahn_gradeMonomial, if_pos (by norm_num : (-1 : ℤ) < 0)]

end Minimalist.Merge
