/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Preorder.Finite

/-!
# Idempotent powers in finite monoids (`omegaPow`)

In any finite monoid `M`, the powers `x, x², x³, …` of an element `x`
must eventually repeat: pigeonhole on the infinite indexing of a finite
set forces some `x^i = x^j` with `i < j`. From this it follows that
some positive power `x^N` is **idempotent** (`x^N * x^N = x^N`). The
canonical such power is the *omega power* `x^ω`, the unique idempotent
in the cyclic subsemigroup `⟨x⟩`.

This file lands the basic substrate:

* `Monoid.exists_pow_eq_pow_of_finite` — pigeonhole.
* `Monoid.exists_pos_pow_isIdempotent` — idempotent power exists.
* `Monoid.omegaPow x` — the noncomputable choice of one such power.
* Basic lemmas: `omegaPow_isIdempotent`, `omegaPow_pow`,
  `omegaPow_mul_omegaPow`.

`omegaPow` is the substrate for the algebraic characterization of
subregular language classes ([pin-mfa]; [eilenberg-1976];
[lambert-2026] §6.2): definite languages are exactly those whose
syntactic monoid satisfies `s · x^ω = x^ω`, reverse-definite by
`x^ω · y = x^ω`, and so on. Until this file is in place, the algebraic
characterizations are stuck at finite-`k` forms that don't generalize
cleanly across the hierarchy.

## Mathlib promotion

This file is structured to be promotable to mathlib as a sibling of
`Mathlib.Algebra.Group.Idempotent`. The construction depends only on
`Monoid M`, `Finite M`, and `IsIdempotentElem` — no automata-theory
content. The choice of `noncomputable def` over a decidability-aware
`Fintype`-based search is the simplest one for the algebraic theorems;
a computable variant would be a natural follow-up.

## Implementation note

The `omegaPow` definition uses `Classical.choose` against
`exists_pos_pow_isIdempotent`, so it is `noncomputable`. For the
algebraic theorems this is fine — `omegaPow x` is determined up to
equality, not up to computation.
-/

namespace Monoid

variable {M : Type*} [Monoid M]

-- ============================================================================
-- §1. Periodicity helpers (no finiteness needed)
-- ============================================================================

/-- Multiplying both sides of a power equation by the same factor
preserves equality. -/
private lemma pow_add_step {x : M} {a b : ℕ} (h : x ^ a = x ^ b) (k : ℕ) :
    x ^ (a + k) = x ^ (b + k) := by
  rw [pow_add, pow_add, h]

/-- **Periodicity**: if `x^i = x^j` (with `i ≤ j`), then for any
`a` and any number of periods `m`, `x^(i + a) = x^(i + a + m·(j-i))`.
The cyclic submonoid `{x^k : k ≥ i}` has period dividing `j - i`. -/
private lemma pow_period {x : M} {i j : ℕ} (h_le : i ≤ j) (h_eq : x ^ i = x ^ j)
    (a m : ℕ) : x ^ (i + a) = x ^ (i + a + m * (j - i)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    -- Apply `pow_add_step h_eq` at offset `a + m·(j-i)`:
    --   x^(i + (a + m·(j-i))) = x^(j + (a + m·(j-i)))
    -- LHS reshapes (assoc) to x^(i+a + m·(j-i)).
    -- RHS reshapes (j = i + (j-i), polynomial expansion) to x^(i+a + (m+1)·(j-i)).
    -- Then chain with `ih`.
    have base := pow_add_step h_eq (a + m * (j - i))
    have lhs_eq : i + (a + m * (j - i)) = i + a + m * (j - i) := by
      rw [Nat.add_assoc]
    have rhs_eq : j + (a + m * (j - i)) = i + a + (m + 1) * (j - i) := by
      obtain ⟨p, rfl⟩ : ∃ p, j = i + p := ⟨j - i, by omega⟩
      simp only [Nat.add_sub_cancel_left]
      rw [Nat.succ_mul]
      generalize m * p = mp
      omega
    rw [lhs_eq, rhs_eq] at base
    exact ih.trans base

variable [Finite M]

-- ============================================================================
-- §2. Pigeonhole + existence of an idempotent power
-- ============================================================================

/-- **Pigeonhole on monoid powers**: in a finite monoid, the sequence
of powers `x^1, x^2, x^3, …` must repeat — there exist indices
`i < j` with `x^i = x^j`. -/
theorem exists_pow_eq_pow_of_finite (x : M) :
    ∃ i j : ℕ, i < j ∧ x ^ i = x ^ j := by
  obtain ⟨i, j, hij, h_eq⟩ :=
    Set.finite_univ.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => x ^ n) (fun _ => Set.mem_univ _)
  exact ⟨i, j, hij, h_eq⟩

/-- **Existence of an idempotent power**: in a finite monoid `M`,
every element `x : M` has a positive power `x^N` that is idempotent
(`x^N * x^N = x^N`).

Construction: pigeonhole gives `i < j` with `x^i = x^j`. Set the
period `p = j - i > 0` and pick `N = j · p`. Then `N` is positive, is
a multiple of `p`, and satisfies `N ≥ j > i` — so the periodicity
lemma `pow_period` (`x^N = x^(N + m·p)` for any `m`) instantiated at
`m = j` gives `x^N = x^(N + j·p) = x^(2N)`. -/
theorem exists_pos_pow_isIdempotent (x : M) :
    ∃ n > 0, IsIdempotentElem (x ^ n) := by
  obtain ⟨i, j, hij, h_eq⟩ := exists_pow_eq_pow_of_finite x
  have hp : 0 < j - i := Nat.sub_pos_of_lt hij
  have hj : 0 < j := lt_of_le_of_lt (Nat.zero_le i) hij
  refine ⟨j * (j - i), Nat.mul_pos hj hp, ?_⟩
  show x ^ (j * (j - i)) * x ^ (j * (j - i)) = x ^ (j * (j - i))
  rw [← pow_add]
  -- Goal: x^(j*(j-i) + j*(j-i)) = x^(j*(j-i)).
  -- Apply pow_period with i, j, m = j, a := j*(j-i) - i.
  have h_le_jp : i ≤ j * (j - i) := by
    have : j ≤ j * (j - i) := Nat.le_mul_of_pos_right j hp
    omega
  have key := pow_period (Nat.le_of_lt hij) h_eq (j * (j - i) - i) j
  -- After omega rewrites both occurrences of `i + (j*(j-i) - i)` to `j*(j-i)`,
  -- key reads `x^(j*(j-i)) = x^(j*(j-i) + j*(j-i))`.
  have e1 : i + (j * (j - i) - i) = j * (j - i) := by omega
  rw [e1] at key
  exact key.symm

-- ============================================================================
-- §3. `omegaPow`
-- ============================================================================

/-- The **omega power** `x^ω` of an element `x` in a finite monoid:
the choice of one positive power of `x` that is idempotent. Such a
power exists by `exists_pos_pow_isIdempotent`. The choice is via
`Classical.choose`, hence `noncomputable`; the algebraic content of
`omegaPow x` (its idempotence and stability under further powers) is
captured by the lemmas below. -/
noncomputable def omegaPow (x : M) : M :=
  x ^ (exists_pos_pow_isIdempotent x).choose

/-- The exponent witnessing `omegaPow x` (a positive natural number
such that `x` raised to it is idempotent). -/
noncomputable def omegaPowExponent (x : M) : ℕ :=
  (exists_pos_pow_isIdempotent x).choose

theorem omegaPow_eq_pow (x : M) : omegaPow x = x ^ omegaPowExponent x := rfl

theorem omegaPowExponent_pos (x : M) : 0 < omegaPowExponent x :=
  (exists_pos_pow_isIdempotent x).choose_spec.1

/-- The omega power of `x` is idempotent. -/
theorem omegaPow_isIdempotent (x : M) : IsIdempotentElem (omegaPow x) :=
  (exists_pos_pow_isIdempotent x).choose_spec.2

/-- The omega power of `x` is stable under any positive power: raising
`omegaPow x` to any `n ≥ 1` gives `omegaPow x` back. Direct
consequence of idempotence (`IsIdempotentElem.pow_eq` from mathlib). -/
theorem omegaPow_pow (x : M) {n : ℕ} (hn : n ≠ 0) :
    omegaPow x ^ n = omegaPow x :=
  (omegaPow_isIdempotent x).pow_eq hn

/-- Multiplying `omegaPow x` by itself yields `omegaPow x` —
restatement of idempotence in product form. -/
@[simp] theorem omegaPow_mul_omegaPow (x : M) :
    omegaPow x * omegaPow x = omegaPow x :=
  (omegaPow_isIdempotent x).eq

end Monoid
