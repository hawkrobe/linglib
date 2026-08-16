/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Preorder.Finite

/-!
# Idempotent powers in finite monoids and semigroups

In a finite monoid the powers `x, x², x³, …` must repeat, so some
positive power `x^N` is **idempotent**; any two idempotent positive
powers of `x` coincide, so the **omega power** `Monoid.omegaPow x` —
the unique idempotent in the cyclic subsemigroup `⟨x⟩` — is well
defined. The semigroup case follows by adjoining an identity
(`WithOne`).

`omegaPow` is the substrate for the algebraic characterization of
subregular language classes ([pin-mfa]; [eilenberg-1976];
[lambert-2026] §6.2): definite languages are exactly those whose
syntactic monoid satisfies `s · x^ω = x^ω`, reverse-definite ones
`x^ω · s = x^ω`, and so on (`Core/Computability/Variety/`).

## Main results

* `Monoid.exists_pos_pow_isIdempotent` — existence, by pigeonhole.
* `IsIdempotentElem.pow_eq_pow` — uniqueness: idempotent positive
  powers of the same element coincide (no finiteness needed).
* `Monoid.omegaPow` — the omega power `x^ω`, canonical by
  `Monoid.omegaPow_unique`; `IsIdempotentElem.omegaPow_eq`,
  `Monoid.omegaPow_pow`.
* `Semigroup.exists_isIdempotentElem`,
  `Semigroup.exists_isIdempotentElem_map_eq` — the semigroup
  transfers consumed by `Pseudovariety.lean`.

`omegaPow` is defined by `Classical.choose`, hence `noncomputable`;
`omegaPow_unique` makes it independent of the choice.

`[UPSTREAM]` candidate (`Mathlib.Algebra.Group.Idempotent` sibling).
-/

namespace Monoid

variable {M : Type*} [Monoid M]

/-! ### Periodicity of powers -/

/-- Multiplying both sides of a power equation by the same factor
preserves equality. -/
private lemma pow_add_step {x : M} {a b : ℕ} (h : x ^ a = x ^ b) (k : ℕ) :
    x ^ (a + k) = x ^ (b + k) := by
  rw [pow_add, pow_add, h]

/-- **Periodicity**: if `x^i = x^j` with `i ≤ j`, then above `i` the
powers of `x` are periodic with period dividing `j - i`. -/
private lemma pow_period {x : M} {i j : ℕ} (h_le : i ≤ j) (h_eq : x ^ i = x ^ j)
    {n : ℕ} (hn : i ≤ n) (m : ℕ) : x ^ n = x ^ (n + m * (j - i)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have step := pow_add_step h_eq (n - i + m * (j - i))
    rw [show i + (n - i + m * (j - i)) = n + m * (j - i) by omega,
        show j + (n - i + m * (j - i)) = n + m * (j - i) + (j - i) by omega] at step
    rw [Nat.succ_mul, ← Nat.add_assoc]
    exact ih.trans step

/-- Idempotent positive powers of the same element coincide — no
finiteness needed: `x^a = (x^a)^b = (x^b)^a = x^b`. This is what makes
the omega power canonical. -/
theorem _root_.IsIdempotentElem.pow_eq_pow {x : M} {a b : ℕ}
    (hxa : IsIdempotentElem (x ^ a)) (hxb : IsIdempotentElem (x ^ b))
    (ha : a ≠ 0) (hb : b ≠ 0) : x ^ a = x ^ b :=
  calc x ^ a = (x ^ a) ^ b := (hxa.pow_eq hb).symm
    _ = (x ^ b) ^ a := by rw [← pow_mul, mul_comm a b, pow_mul]
    _ = x ^ b := hxb.pow_eq ha

variable [Finite M]

/-! ### Existence of an idempotent power -/

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
every element `x : M` has a positive power `x^N` that is idempotent.
Pigeonhole gives `x^i = x^j` with `i < j`; `N = j·(j - i)` is a
positive multiple of the period at least `i`, so `x^N = x^(2N)` by
`pow_period`. -/
theorem exists_pos_pow_isIdempotent (x : M) :
    ∃ n > 0, IsIdempotentElem (x ^ n) := by
  obtain ⟨i, j, hij, h_eq⟩ := exists_pow_eq_pow_of_finite x
  have hp : 0 < j - i := Nat.sub_pos_of_lt hij
  have hj : 0 < j := (Nat.zero_le i).trans_lt hij
  refine ⟨j * (j - i), Nat.mul_pos hj hp, ?_⟩
  show x ^ (j * (j - i)) * x ^ (j * (j - i)) = x ^ (j * (j - i))
  rw [← pow_add]
  exact (pow_period hij.le h_eq (hij.le.trans (Nat.le_mul_of_pos_right j hp)) j).symm

/-! ### The omega power -/

/-- The **omega power** `x^ω` of an element `x` in a finite monoid:
the idempotent positive power of `x` (unique by `omegaPow_unique`),
realized via `Classical.choose` against `exists_pos_pow_isIdempotent`. -/
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

/-- Any idempotent positive power of `x` equals `omegaPow x`: the
omega power is canonical, independent of the chosen exponent. -/
theorem omegaPow_unique {x : M} {n : ℕ} (hn : n ≠ 0)
    (hxn : IsIdempotentElem (x ^ n)) : x ^ n = omegaPow x :=
  hxn.pow_eq_pow (omegaPow_isIdempotent x) hn (omegaPowExponent_pos x).ne'

/-- An idempotent element is its own omega power. -/
theorem _root_.IsIdempotentElem.omegaPow_eq {x : M}
    (hx : IsIdempotentElem x) : omegaPow x = x := by
  conv_rhs => rw [← pow_one x]
  exact (omegaPow_unique one_ne_zero (by rwa [pow_one])).symm

/-- The omega power is a projection. -/
@[simp] theorem omegaPow_omegaPow (x : M) :
    omegaPow (omegaPow x) = omegaPow x :=
  (omegaPow_isIdempotent x).omegaPow_eq

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

/-! ### Semigroups: transfer through `WithOne`

`WithOne S` is a finite monoid when `S` is a finite semigroup, positive
powers of a coerced element are themselves coerced, and `WithOne.coe_inj`
transfers idempotency back. The payoff is the structural fact behind the
equational description of semigroup pseudovarieties: a preimage of an
idempotent need not be idempotent, but an idempotent *power* of a
preimage is one and has the same image. -/

namespace WithOne

variable {S : Type*} [Semigroup S]

/-- `WithOne S` is `Option S`, so it inherits finiteness. -/
instance instFinite [Finite S] : Finite (WithOne S) := inferInstanceAs (Finite (Option S))

/-- Idempotency is detected by the coercion into `WithOne`. -/
@[simp] theorem isIdempotentElem_coe {e : S} :
    IsIdempotentElem ((e : WithOne S)) ↔ IsIdempotentElem e := by
  rw [IsIdempotentElem, ← WithOne.coe_mul, WithOne.coe_inj]; rfl

/-- A positive power of a coerced element of `WithOne S` is itself coerced. -/
theorem exists_coe_pow (x : S) : ∀ n : ℕ, 0 < n → ∃ y : S, (x : WithOne S) ^ n = y
  | 1, _ => ⟨x, pow_one _⟩
  | n + 2, _ => by
    obtain ⟨y, hy⟩ := exists_coe_pow x (n + 1) n.succ_pos
    exact ⟨x * y, by rw [pow_succ', hy, ← WithOne.coe_mul]⟩

end WithOne

namespace Semigroup

variable {S T : Type*} [Semigroup S] [Semigroup T] [Finite S]

/-- Every element has an idempotent positive power, with the exponent realized in `WithOne S`.
The `WithOne` shape is the proof device; `exists_isIdempotentElem` and
`exists_isIdempotentElem_map_eq` are the statements consumers want. -/
private theorem exists_pos_pow_isIdempotentElem_coe (x : S) :
    ∃ (n : ℕ) (e : S), 0 < n ∧ (x : WithOne S) ^ n = e ∧ IsIdempotentElem e := by
  obtain ⟨n, hn, hidem⟩ := Monoid.exists_pos_pow_isIdempotent (x : WithOne S)
  obtain ⟨e, he⟩ := WithOne.exists_coe_pow x n hn
  exact ⟨n, e, hn, he, WithOne.isIdempotentElem_coe.1 (he ▸ hidem)⟩

/-- **A finite nonempty semigroup contains an idempotent.** -/
theorem exists_isIdempotentElem [Nonempty S] : ∃ e : S, IsIdempotentElem e :=
  have ⟨x⟩ := ‹Nonempty S›
  have ⟨_, e, _, _, he⟩ := exists_pos_pow_isIdempotentElem_coe x
  ⟨e, he⟩

/-- A surjective homomorphism lifts an idempotent to an idempotent: replace a preimage by an
idempotent power of it, which the homomorphism still sends to the (idempotent) target. -/
theorem exists_isIdempotentElem_map_eq {f : S →ₙ* T} (hf : Function.Surjective f) {e' : T}
    (he' : IsIdempotentElem e') : ∃ e : S, IsIdempotentElem e ∧ f e = e' := by
  obtain ⟨x, rfl⟩ := hf e'
  obtain ⟨n, e, hn, he, hidem⟩ := exists_pos_pow_isIdempotentElem_coe x
  refine ⟨e, hidem, ?_⟩
  have hmap : (WithOne.mapMulHom f) ((x : WithOne S) ^ n) = ((f x : T) : WithOne T) ^ n := by
    rw [map_pow, WithOne.mapMulHom_coe]
  rw [he, WithOne.mapMulHom_coe] at hmap
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rwa [(WithOne.isIdempotentElem_coe.2 he').pow_succ_eq, WithOne.coe_inj] at hmap

end Semigroup
