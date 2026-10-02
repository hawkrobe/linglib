module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Affinely independent finsets in finite dimension

`[UPSTREAM]` An affinely independent finset of points in an affine space over a
finite-dimensional module of rank `n` has at most `n + 1` elements. This is the `Finset` form of
`AffineIndependent.card_le_finrank_succ`, with the ambient rank in place of the rank of the
`vectorSpan`, and the affine counterpart of `LinearIndependent.finset_card_le_finrank`.
-/

@[expose] public section

open Affine Finset Module

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]
  [FiniteDimensional k V]

/-- An affinely independent finset of points has at most `finrank k V + 1` elements. -/
theorem AffineIndependent.finset_card_le_finrank_succ {s : Finset P}
    (hs : AffineIndependent k ((↑) : s → P)) : #s ≤ finrank k V + 1 := by
  rw [← Fintype.card_coe]
  exact hs.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
