/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Rota–Baxter operators  `[UPSTREAM]`

A **Rota–Baxter operator** of weight `λ` on a `k`-algebra `A` is a `k`-linear endomorphism `R`
satisfying `R a * R b = R (R a * b + a * R b + λ • (a * b))`. For `λ = -1` this is the operator
of [marcolli-chomsky-berwick-2025]'s Definition 3.1.1, written there as
`R(a) R(b) = R(a R(b)) + R(R(a) b) − R(a b)`; the prototype is the algebra of Laurent series with
`R` the projection onto the polar (divergent) part.

Rota–Baxter operators of weight `-1` are the algebraic substrate of Connes–Kreimer renormalization:
on a connected graded Hopf algebra they drive the **Birkhoff factorization** of a character (the
Bogolyubov recursion), which [marcolli-chomsky-berwick-2025] use to package semantic-consistency
checking "into a single map, which recursively modifies an initially chosen assignment of semantic
values so as to incorporate the consistency checking over all substructures."

## Main definitions

- `RotaBaxter k A lam`: a `k`-linear `R : A → A` with the weight-`lam` identity.
- `RotaBaxter.rangeMulClosed`: `R a * R b ∈ range R` — the range is closed under multiplication.
- `RotaBaxter.complement`: for weight `-1`, `1 - R` is again a weight-`-1` Rota–Baxter operator
  (the complementary projection that gives the splitting `A = range R ⊕ range (1 - R)`).
- `RotaBaxterSemiring ℛ`: the **weight `+1`** operator on a commutative semiring
  ([marcolli-chomsky-berwick-2025] Def. 3.1.2), for settings where addition is not invertible
  (tropical, Viterbi, Boolean parsing) — here the divergence term `op (a * b)` cannot be moved
  across the identity, so weight `+1` and weight `-1` are genuinely distinct.

## References

[marcolli-chomsky-berwick-2025] (Def. 3.1.1, Def. 3.1.2, Prop. 3.1.7)
-/

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]

/-- A **Rota–Baxter operator of weight `lam`** on the `k`-algebra `A`: a `k`-linear endomorphism
    `op` satisfying `op a * op b = op (op a * b + a * op b + lam • (a * b))`
    ([marcolli-chomsky-berwick-2025] Def. 3.1.1 is the `lam = -1` case). -/
structure RotaBaxter (lam : k) where
  /-- The underlying `k`-linear operator. -/
  op : A →ₗ[k] A
  /-- The Rota–Baxter identity of weight `lam`. -/
  rotaBaxter : ∀ a b : A, op a * op b = op (op a * b + a * op b + lam • (a * b))

namespace RotaBaxter

variable {k A} {lam : k}

theorem op_mul_op (R : RotaBaxter k A lam) (a b : A) :
    R.op a * R.op b = R.op (R.op a * b + a * R.op b + lam • (a * b)) := R.rotaBaxter a b

/-- The range of a Rota–Baxter operator is closed under multiplication: `R a * R b ∈ range R`.
    This is the algebraic heart of the splitting ([marcolli-chomsky-berwick-2025] Prop. 3.1.7,
    "these are subalgebras ... because of the Rota–Baxter identity satisfied by `R`"). -/
theorem rangeMulClosed (R : RotaBaxter k A lam) {a b : A}
    (ha : a ∈ LinearMap.range R.op) (hb : b ∈ LinearMap.range R.op) :
    a * b ∈ LinearMap.range R.op := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨R.op x * y + x * R.op y + lam • (x * y), (R.rotaBaxter x y).symm⟩

/-- **Identity is Rota–Baxter of weight `-1`** ([marcolli-chomsky-berwick-2025] Rem. 3.2.2:
    the scheme `R = id` used in the tropical/min-plus toy model). -/
def id : RotaBaxter k A (-1) where
  op := LinearMap.id
  rotaBaxter a b := by simp

/-- The zero operator is Rota–Baxter of every weight. -/
def zero : RotaBaxter k A lam where
  op := 0
  rotaBaxter a b := by simp

/-- **The complementary operator.** For a weight-`-1` Rota–Baxter operator `R`, the operator
    `1 - R` is again Rota–Baxter of weight `-1`. When `R` is idempotent this is the complementary
    projection, giving the splitting `A = range R ⊕ range (1 - R)` into the two subalgebras of the
    Birkhoff factorization ([marcolli-chomsky-berwick-2025] Prop. 3.1.7). -/
def complement (R : RotaBaxter k A (-1)) : RotaBaxter k A (-1) where
  op := LinearMap.id - R.op
  rotaBaxter a b := by
    -- Expand `R`'s weight-`-1` identity to atoms: `R a * R b = R(R a*b) + R(a*R b) − R(a*b)`.
    have hR : R.op a * R.op b = R.op (R.op a * b) + R.op (a * R.op b) - R.op (a * b) := by
      have h := R.rotaBaxter a b
      rw [neg_one_smul, map_add, map_add, map_neg] at h
      linear_combination h
    simp only [LinearMap.sub_apply, LinearMap.id_apply]
    -- The Merge argument collapses to `a*b − R a*b − a*R b`; push `R` through it by linearity.
    have e : (a - R.op a) * b + a * (b - R.op b) + (-1 : k) • (a * b)
           = a * b - R.op a * b - a * R.op b := by rw [neg_one_smul]; ring
    rw [e, map_sub, map_sub]
    linear_combination hR

end RotaBaxter

/-! ### Rota–Baxter operators on semirings -/

section Semiring

variable (ℛ : Type*) [CommSemiring ℛ]

/-- A **Rota–Baxter operator of weight `+1` on a commutative semiring**
    ([marcolli-chomsky-berwick-2025] Def. 3.1.2): an additive `op : ℛ → ℛ` satisfying
    `op a * op b = op (a * op b) + op (op a * b) + op (a * b)`. The semiring analogue of
    `RotaBaxter` (weight `-1`) for settings where addition is not invertible — tropical
    `(ℝ ∪ {−∞}, max, +)`, Viterbi, and Boolean parsing semirings. Because there is no subtraction,
    the divergence term `op (a * b)` cannot be moved across the identity, so the weight `+1` and
    weight `-1` semiring operators are genuinely different operators. -/
structure RotaBaxterSemiring where
  /-- The underlying additive operator. -/
  op : ℛ →+ ℛ
  /-- The weight-`+1` Rota–Baxter identity. -/
  rotaBaxter : ∀ a b : ℛ, op a * op b = op (a * op b) + op (op a * b) + op (a * b)

namespace RotaBaxterSemiring

variable {ℛ}

theorem op_mul_op (R : RotaBaxterSemiring ℛ) (a b : ℛ) :
    R.op a * R.op b = R.op (a * R.op b) + R.op (R.op a * b) + R.op (a * b) := R.rotaBaxter a b

/-- The range of a weight-`+1` Rota–Baxter semiring operator is closed under multiplication:
    `R a * R b ∈ range R`, since `R a * R b = R (a * R b + R a * b + a * b)`. The semiring analogue
    of `RotaBaxter.rangeMulClosed` — the algebraic heart of the splitting into "meaningful" and
    "meaningless" subsemirings. -/
theorem rangeMulClosed (R : RotaBaxterSemiring ℛ) {a b : ℛ}
    (ha : a ∈ Set.range R.op) (hb : b ∈ Set.range R.op) :
    a * b ∈ Set.range R.op := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x * R.op y + R.op x * y + x * y, by rw [map_add, map_add]; exact (R.rotaBaxter x y).symm⟩

end RotaBaxterSemiring

end Semiring
