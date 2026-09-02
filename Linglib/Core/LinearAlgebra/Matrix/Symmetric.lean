import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Diagonals of symmetric idempotent matrices

A symmetric idempotent matrix `P` — an orthogonal projector — satisfies `P = PᵀP`, so each
diagonal entry is a sum of squares, `P i i = ∑ j, P i j ^ 2`, and over an ordered ring lies in
`[0, 1]`.

`[UPSTREAM]` candidate.
-/

namespace Matrix

variable {n R : Type*} [Fintype n]

theorem diag_eq_sum_sq_of_isSymm_of_isIdempotentElem [CommSemiring R] {P : Matrix n n R}
    (hs : P.IsSymm) (hp : IsIdempotentElem P) (i : n) : P i i = ∑ j, P i j ^ 2 := by
  conv_lhs => rw [← hp.eq]
  simp only [mul_apply, sq]
  exact Finset.sum_congr rfl fun j _ => by rw [hs.apply i j]

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {P : Matrix n n R}

theorem diag_nonneg_of_isSymm_of_isIdempotentElem (hs : P.IsSymm) (hp : IsIdempotentElem P)
    (i : n) : 0 ≤ P i i := by
  rw [diag_eq_sum_sq_of_isSymm_of_isIdempotentElem hs hp i]
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

theorem diag_le_one_of_isSymm_of_isIdempotentElem (hs : P.IsSymm) (hp : IsIdempotentElem P)
    (i : n) : P i i ≤ 1 := by
  have h : P i i ^ 2 ≤ P i i := by
    conv_rhs => rw [diag_eq_sum_sq_of_isSymm_of_isIdempotentElem hs hp i]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (P i j)) (Finset.mem_univ i)
  nlinarith [sq_nonneg (P i i - 1)]

end Matrix
