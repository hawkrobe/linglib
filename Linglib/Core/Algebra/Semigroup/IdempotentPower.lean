/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.Semigroup.IdempotentPower`.
-/
import Linglib.Core.Algebra.IdempotentPower
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Data.Fintype.Option

/-!
# Idempotent powers in a finite semigroup

Every element of a finite semigroup has an idempotent positive power. This is the basic
structural fact behind the equational description of semigroup pseudovarieties: it is what makes
a homomorphic image of a member a member, since a preimage of an idempotent need not itself be
idempotent, but an idempotent *power* of a preimage is one and has the same image.

The monoid case is `Monoid.exists_pos_pow_isIdempotent`. The semigroup case is obtained from it by
adjoining an identity: `WithOne S` is a finite monoid, positive powers of a coerced element are
themselves coerced, and `WithOne.coe_inj` transfers idempotency back.

## Main results

* `Semigroup.exists_pos_pow_isIdempotent`: every element has an idempotent positive power, given
  as an element of `S` together with the exponent realizing it in `WithOne S`.
* `Semigroup.exists_isIdempotentElem_map_eq`: a surjective homomorphism onto a semigroup lifts an
  idempotent to an idempotent — the form the pseudovariety quotient-closure proof consumes.
-/

namespace WithOne

variable {S : Type*} [Semigroup S]

/-- `WithOne S` is `Option S`, so it inherits finiteness. -/
instance instFinite [Finite S] : Finite (WithOne S) := inferInstanceAs (Finite (Option S))

/-- Idempotency is detected by the coercion into `WithOne`. -/
@[simp] theorem isIdempotentElem_coe {e : S} :
    IsIdempotentElem ((e : WithOne S)) ↔ IsIdempotentElem e := by
  rw [IsIdempotentElem, ← WithOne.coe_mul, WithOne.coe_inj]; rfl

end WithOne

namespace Semigroup

variable {S T : Type*} [Semigroup S] [Semigroup T]

/-- A positive power of a coerced element of `WithOne S` is itself coerced. -/
theorem exists_coe_pow (x : S) : ∀ n : ℕ, 0 < n → ∃ y : S, (x : WithOne S) ^ n = y
  | 1, _ => ⟨x, pow_one _⟩
  | n + 2, _ => by
    obtain ⟨y, hy⟩ := exists_coe_pow x (n + 1) n.succ_pos
    exact ⟨x * y, by rw [pow_succ', hy, ← WithOne.coe_mul]⟩

variable [Finite S]

/-- **Every element of a finite semigroup has an idempotent positive power.** -/
theorem exists_pos_pow_isIdempotent (x : S) :
    ∃ (n : ℕ) (e : S), 0 < n ∧ (x : WithOne S) ^ n = e ∧ IsIdempotentElem e := by
  obtain ⟨n, hn, hidem⟩ := Monoid.exists_pos_pow_isIdempotent (x : WithOne S)
  obtain ⟨e, he⟩ := exists_coe_pow x n hn
  exact ⟨n, e, hn, he, WithOne.isIdempotentElem_coe.1 (he ▸ hidem)⟩

/-- A surjective homomorphism lifts an idempotent to an idempotent: replace a preimage by an
idempotent power of it, which the homomorphism still sends to the (idempotent) target. -/
theorem exists_isIdempotentElem_map_eq {f : S →ₙ* T} (hf : Function.Surjective f) {e' : T}
    (he' : IsIdempotentElem e') : ∃ e : S, IsIdempotentElem e ∧ f e = e' := by
  obtain ⟨x, rfl⟩ := hf e'
  obtain ⟨n, e, hn, he, hidem⟩ := exists_pos_pow_isIdempotent x
  refine ⟨e, hidem, ?_⟩
  have hmap : (WithOne.mapMulHom f) ((x : WithOne S) ^ n) = ((f x : T) : WithOne T) ^ n := by
    rw [map_pow, WithOne.mapMulHom_coe]
  rw [he, WithOne.mapMulHom_coe] at hmap
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rwa [(WithOne.isIdempotentElem_coe.2 he').pow_succ_eq, WithOne.coe_inj] at hmap

end Semigroup
