import Mathlib.Algebra.Polynomial.Laurent

/-!
# Laurent-polynomial scalars for cost-weighted Connes-Kreimer coproducts
@cite{marcolli-chomsky-berwick-2025} §1.5

Foundational scalar substrate for **Phase 7g** — the IM cost-survival
extension of `Merge.Basic`'s `mergeOp_eps`. Per @cite{marcolli-chomsky-berwick-2025}
Proposition 1.5.1 (book p. 60), the cost framework requires both:

- **Rule 1** (book p. 59): extracted accessible term `T_v ⊂ T` carries
  weight `ε^{d_v}` where `d_v = dist(v, root_T)` (positive exponent).
  Already implemented in `comulTreeDel_eps` via `R`-coefficients.
- **Rule 2** (book p. 59): the partner quotient `T/T_v` carries weight
  `ε^{-d_v}` (negative exponent). NOT representable in `R` for arbitrary
  `R` — requires `LaurentPolynomial R`.

The cancellation `ε^{d_v} · ε^{-d_v} = ε^0 = 1` is what mathematically
distinguishes Internal Merge (cost 0, weight 1) from Sideward Merge
(cost > 0, weight `ε^{d_v} → 0` as `ε → 0`) per Prop 1.5.1's proof.

## What this file provides

- Re-export of `LaurentPolynomial R` (= `R[T;T⁻¹]`) and the `T : ℤ → R[T;T⁻¹]`
  monomial constructor from mathlib.
- `ε := LaurentPolynomial.T 1` (the cost-tracking formal parameter).
- Cancellation lemma `T_pow_int_cancel`: `T n * T (-n) = 1` for any
  `n : ℤ`, packaged for cost-cancellation use.
- Symmetric form `T_pow_int_cancel'` (right-cancel).

## What this file does NOT provide

- The signed-weight coproduct `comulTreeDel_eps_signed` — needs operand
  origin tracking (Phase 7g.2).
- The signed-weight Merge `mergeOp_eps_signed` — needs cost rule 5
  applied at grafting (Phase 7g.2).
- IM cost-survival theorem (Phase 7g.3).

These are deferred until the operand-origin design is settled. This
foundational file unblocks downstream work without committing to the
substrate shape for the merge-side cost extraction.

## Why a separate file

Linglib's existing `Merge.Basic`'s `mergeOp_eps` correctly implements
rule 1 over `R`-coefficients (and is consumed by all current cost-
suppression theorems for Sideward). The signed-weight extension lives
in `R[T;T⁻¹]`-coefficients which is a distinct algebraic context.
Keeping LaurentPolynomial substrate separate avoids forcing all current
consumers to migrate to Laurent coefficients prematurely.
-/

namespace ConnesKreimer

open LaurentPolynomial

/-- The formal cost parameter `ε := T = T^1` in the Laurent polynomial
    ring `R[T;T⁻¹]`. Per @cite{marcolli-chomsky-berwick-2025} §1.5.2,
    the cost-weighted Merge operator depends on this parameter; the
    `ε → 0` limit is taken to extract leading-order terms. -/
noncomputable abbrev eps (R : Type*) [CommSemiring R] : LaurentPolynomial R :=
  LaurentPolynomial.T 1

/-- **Cost cancellation lemma** (left-cancel): `T n * T (-n) = 1` in
    `R[T;T⁻¹]`. This is the algebraic content of MCB's IM-cost-zero
    claim (Prop 1.5.1, book p. 60): `c(T_v) + c(T_i/T_v) = d_v + (-d_v) = 0`.
    Convenience wrapper around `LaurentPolynomial.T_add` + `T_zero`. -/
theorem T_pow_int_cancel {R : Type*} [CommSemiring R] (n : ℤ) :
    (LaurentPolynomial.T n : LaurentPolynomial R) *
        LaurentPolynomial.T (-n) = 1 := by
  rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

/-- **Cost cancellation lemma** (right-cancel): `T (-n) * T n = 1` in
    `R[T;T⁻¹]`. Symmetric form of `T_pow_int_cancel`. -/
theorem T_pow_int_cancel' {R : Type*} [CommSemiring R] (n : ℤ) :
    (LaurentPolynomial.T (-n) : LaurentPolynomial R) *
        LaurentPolynomial.T n = 1 := by
  rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

/-- For `n : ℕ`, the natural-power form `(T 1)^n = T (n : ℤ)` connects
    `Nat.pow` (used in `mergeOp_eps`'s rule-1 weighting via
    `ε ^ cutTotalDepth c`) to the Laurent monomial constructor `T`
    (which is what cost-cancellation lemmas operate on). -/
theorem eps_pow_nat_eq_T {R : Type*} [CommSemiring R] (n : ℕ) :
    (eps R) ^ n = LaurentPolynomial.T (n : ℤ) := by
  rw [eps]
  rw [LaurentPolynomial.T_pow, mul_one]

end ConnesKreimer
