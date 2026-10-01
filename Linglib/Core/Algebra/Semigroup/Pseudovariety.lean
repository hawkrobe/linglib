/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.Semigroup.Pseudovariety`.
-/
module

public import Linglib.Core.Algebra.Group.IdempotentPower
public import Linglib.Core.GroupTheory.Congruence.Hom
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.PUnit

/-!
# Pseudovarieties of finite semigroups

This file defines pseudovarieties of finite semigroups and the three pseudovarieties **D**, **K**
and **LI**. A *pseudovariety* is a class of finite semigroups closed under subsemigroups,
quotients and finite direct products. It is the semigroup counterpart of `Monoid.Pseudovariety`,
and the two are not interchangeable: **D**, **K** and **LI** collapse over monoids, since their
defining conditions applied to the idempotent `1` force triviality.

Following Eilenberg, the conditions are stated on idempotents: a semigroup is in **D** when
`s * e = e`, in **K** when `e * s = e`, and in **LI** when `e * s * e = e`, for every idempotent `e`
and every `s`. Each is equivalent to an equation on all sufficiently long products.

## Main definitions

* `Semigroup.Pseudovariety`: a class of finite semigroups closed under subsemigroups, quotients
  and products.
* `Semigroup.IsDefinite`, `Semigroup.IsReverseDefinite`, `Semigroup.IsLocallyTrivial`: the
  conditions defining **D**, **K** and **LI**.
* `Semigroup.definiteVariety`, `Semigroup.reverseDefiniteVariety`,
  `Semigroup.locallyTrivialVariety`: the bundled pseudovarieties.

## Main results

* `Semigroup.IsDefinite.mul_map_eq`, `Semigroup.IsReverseDefinite.map_mul_eq`,
  `Semigroup.IsLocallyTrivial.map_mul_map_eq`: in a finite semigroup of the pseudovariety, every
  product of at least `|S|` elements is a right zero, a left zero, respectively absorbs anything
  placed between two copies of it.
* `Semigroup.IsDefinite.of_mul_map_eq` and its two mirrors: the converse, for any bound.

## Implementation notes

`mem` is a total predicate on `Type u` semigroups that implies finiteness, mirroring
`Monoid.Pseudovariety`, so the order on pseudovarieties is inclusion of classes of finite
semigroups. The pseudovariety **N** of nilpotent semigroups is the intersection of **D** and **K**
and is not bundled. The long-product characterizations are Propositions XI.4.15–XI.4.17 of
[pin-mfa].

## References

* [eilenberg-1976]
* [pin-mfa]
-/

@[expose] public section

universe u

namespace Semigroup

/-- A *pseudovariety of finite semigroups* is a class of finite semigroups closed under
subsemigroups, quotients and finite products, with closure phrased through injective and surjective
`MulHom`s. -/
structure Pseudovariety where
  /-- The semigroups belonging to the pseudovariety. -/
  mem : ∀ (S : Type u) [Semigroup S], Prop
  /-- Every member is finite. -/
  finite_of_mem : ∀ {S : Type u} [Semigroup S], mem S → Finite S
  /-- The domain of an injective homomorphism into a member is a member. -/
  sub : ∀ {S T : Type u} [Semigroup S] [Semigroup T] {f : S →ₙ* T},
    Function.Injective f → mem T → mem S
  /-- The codomain of a surjective homomorphism from a member is a member. -/
  quot : ∀ {S T : Type u} [Semigroup S] [Semigroup T] {f : S →ₙ* T},
    Function.Surjective f → mem S → mem T
  /-- The product of two members is a member. -/
  prod : ∀ {S T : Type u} [Semigroup S] [Semigroup T], mem S → mem T → mem (S × T)
  /-- The trivial semigroup is a member. -/
  memUnit : mem PUnit.{u + 1}

namespace Pseudovariety

variable (V : Pseudovariety.{u})

@[ext] theorem ext {V W : Pseudovariety.{u}}
    (h : ∀ (S : Type u) [Semigroup S], V.mem S ↔ W.mem S) : V = W := by
  obtain ⟨Vm, _, _, _, _, _⟩ := V
  obtain ⟨Wm, _, _, _, _, _⟩ := W
  obtain rfl : Vm = Wm := funext fun S ↦ funext fun _ ↦ propext (h S)
  rfl

instance : PartialOrder Pseudovariety.{u} where
  le V W := ∀ (S : Type u) [Semigroup S], V.mem S → W.mem S
  le_refl _ _ _ h := h
  le_trans _ _ _ h₁ h₂ S _ h := h₂ S (h₁ S h)
  le_antisymm _ _ h₁ h₂ := ext fun S _ ↦ ⟨h₁ S, h₂ S⟩

theorem mem_of_mulEquiv {S T : Type u} [Semigroup S] [Semigroup T] (e : S ≃* T) (h : V.mem S) :
    V.mem T :=
  V.quot (f := e.toMulHom) e.surjective h

/-- Membership of a quotient descends along a coarsening of congruences. -/
theorem mem_quotient_of_le {S : Type u} [Semigroup S] {c d : Con S} (h : c ≤ d)
    (hc : V.mem c.Quotient) : V.mem d.Quotient :=
  V.quot (Con.mapMulHom_surjective c d h) hc

/-- The quotient by the kernel of a homomorphism into a member is a member. -/
theorem mem_quotient_ker {S T : Type u} [Semigroup S] [Semigroup T] (f : S →ₙ* T)
    (h : V.mem T) : V.mem (Con.ker f).Quotient :=
  V.sub (Con.kerLiftMulHom_injective f) h

/-- The quotient by the meet of two congruences is a member when both quotients are. -/
theorem mem_quotient_inf {S : Type u} [Semigroup S] {c d : Con S} (hc : V.mem c.Quotient)
    (hd : V.mem d.Quotient) : V.mem (c ⊓ d).Quotient := by
  have h : Con.ker (c.mkMulHom.prod d.mkMulHom) ≤ c ⊓ d := by
    rw [Con.ker_prodMulHom, Con.ker_mkMulHom_eq, Con.ker_mkMulHom_eq]
  exact V.mem_quotient_of_le h (V.mem_quotient_ker _ (V.prod hc hd))

end Pseudovariety

variable {S T : Type*} [Semigroup S] [Semigroup T]

/-! ### The conditions defining `D`, `K` and `LI` -/

/-- A semigroup is *definite* when every idempotent `e` absorbs on the left, `s * e = e`. -/
def IsDefinite (S : Type*) [Semigroup S] : Prop :=
  ∀ e : S, IsIdempotentElem e → ∀ s : S, s * e = e

/-- A semigroup is *reverse definite* when every idempotent `e` absorbs on the right,
`e * s = e`. -/
def IsReverseDefinite (S : Type*) [Semigroup S] : Prop :=
  ∀ e : S, IsIdempotentElem e → ∀ s : S, e * s = e

/-- A semigroup is *locally trivial* when every idempotent `e` absorbs anything placed between two
copies of it, `e * s * e = e`. -/
def IsLocallyTrivial (S : Type*) [Semigroup S] : Prop :=
  ∀ e : S, IsIdempotentElem e → ∀ s : S, e * s * e = e

/-! ### Closure properties -/

theorem IsDefinite.of_injective {f : S →ₙ* T} (hf : Function.Injective f) (h : IsDefinite T) :
    IsDefinite S := fun e he s ↦ hf <| by rw [map_mul, h (f e) (he.map f) (f s)]

theorem IsReverseDefinite.of_injective {f : S →ₙ* T} (hf : Function.Injective f)
    (h : IsReverseDefinite T) : IsReverseDefinite S := fun e he s ↦ hf <| by
  rw [map_mul, h (f e) (he.map f) (f s)]

theorem IsLocallyTrivial.of_injective {f : S →ₙ* T} (hf : Function.Injective f)
    (h : IsLocallyTrivial T) : IsLocallyTrivial S := fun e he s ↦ hf <| by
  rw [map_mul, map_mul, h (f e) (he.map f) (f s)]

theorem IsDefinite.prod (hS : IsDefinite S) (hT : IsDefinite T) : IsDefinite (S × T) := by
  rintro ⟨e₁, e₂⟩ he ⟨s₁, s₂⟩
  exact Prod.ext (hS e₁ (congrArg Prod.fst he) s₁) (hT e₂ (congrArg Prod.snd he) s₂)

theorem IsReverseDefinite.prod (hS : IsReverseDefinite S) (hT : IsReverseDefinite T) :
    IsReverseDefinite (S × T) := by
  rintro ⟨e₁, e₂⟩ he ⟨s₁, s₂⟩
  exact Prod.ext (hS e₁ (congrArg Prod.fst he) s₁) (hT e₂ (congrArg Prod.snd he) s₂)

theorem IsLocallyTrivial.prod (hS : IsLocallyTrivial S) (hT : IsLocallyTrivial T) :
    IsLocallyTrivial (S × T) := by
  rintro ⟨e₁, e₂⟩ he ⟨s₁, s₂⟩
  exact Prod.ext (hS e₁ (congrArg Prod.fst he) s₁) (hT e₂ (congrArg Prod.snd he) s₂)

/-- A definite monoid is trivial, since the condition at the idempotent `1` gives
`s = s * 1 = 1`. -/
theorem IsDefinite.subsingleton {M : Type*} [Monoid M] (h : IsDefinite M) : Subsingleton M :=
  ⟨fun a b ↦ by rw [← mul_one a, h 1 .one a, ← mul_one b, h 1 .one b]⟩

/-- A definite semigroup is locally trivial. -/
theorem IsDefinite.isLocallyTrivial (h : IsDefinite S) : IsLocallyTrivial S :=
  fun e he s ↦ h e he (e * s)

/-- A reverse definite semigroup is locally trivial. -/
theorem IsReverseDefinite.isLocallyTrivial (h : IsReverseDefinite S) : IsLocallyTrivial S :=
  fun e he s ↦ by rw [h e he s, h e he e]

section Surjective

variable [Finite S]

theorem IsDefinite.of_surjective {f : S →ₙ* T} (hf : Function.Surjective f) (h : IsDefinite S) :
    IsDefinite T := by
  intro e' he' t
  obtain ⟨e, he, rfl⟩ := exists_isIdempotentElem_map_eq hf he'
  obtain ⟨s, rfl⟩ := hf t
  rw [← map_mul, h e he s]

theorem IsReverseDefinite.of_surjective {f : S →ₙ* T} (hf : Function.Surjective f)
    (h : IsReverseDefinite S) : IsReverseDefinite T := by
  intro e' he' t
  obtain ⟨e, he, rfl⟩ := exists_isIdempotentElem_map_eq hf he'
  obtain ⟨s, rfl⟩ := hf t
  rw [← map_mul, h e he s]

theorem IsLocallyTrivial.of_surjective {f : S →ₙ* T} (hf : Function.Surjective f)
    (h : IsLocallyTrivial S) : IsLocallyTrivial T := by
  intro e' he' t
  obtain ⟨e, he, rfl⟩ := exists_isIdempotentElem_map_eq hf he'
  obtain ⟨s, rfl⟩ := hf t
  rw [← map_mul, ← map_mul, h e he s]

end Surjective

/-! ### Long products

Each condition is equivalent to an equation on all sufficiently long products: `S` is definite
exactly when long products are right zeros, reverse definite when they are left zeros, and locally
trivial when they absorb any element placed between two copies. A product is the image of a word
under a homomorphism `f` out of a free semigroup. One direction holds with the bound `|S|`, by
`FreeSemigroup.exists_isIdempotentElem_map_eq_mul_mul`; the other holds for any bound once `f` is
surjective, because an idempotent is the image of arbitrarily long words. -/

section LongProducts

variable {α : Type*} {f : FreeSemigroup α →ₙ* S} {w : FreeSemigroup α} {k : ℕ}

/-- A semigroup is definite when, for some bound, every product of at least that many elements is a
right zero. -/
theorem IsDefinite.of_mul_map_eq (hf : Function.Surjective f)
    (h : ∀ w, k ≤ w.length → ∀ s, s * f w = f w) : IsDefinite S := by
  intro e he s
  obtain ⟨u, rfl⟩ := hf e
  obtain ⟨v, hv, hfv⟩ := FreeSemigroup.exists_le_length_map_eq f he k
  rw [← hfv, h v hv]

theorem IsReverseDefinite.of_map_mul_eq (hf : Function.Surjective f)
    (h : ∀ w, k ≤ w.length → ∀ s, f w * s = f w) : IsReverseDefinite S := by
  intro e he s
  obtain ⟨u, rfl⟩ := hf e
  obtain ⟨v, hv, hfv⟩ := FreeSemigroup.exists_le_length_map_eq f he k
  rw [← hfv, h v hv]

theorem IsLocallyTrivial.of_map_mul_map_eq (hf : Function.Surjective f)
    (h : ∀ w, k ≤ w.length → ∀ s, f w * s * f w = f w) : IsLocallyTrivial S := by
  intro e he s
  obtain ⟨u, rfl⟩ := hf e
  obtain ⟨v, hv, hfv⟩ := FreeSemigroup.exists_le_length_map_eq f he k
  rw [← hfv, h v hv]

variable [Finite S] (f)

/-- In a finite definite semigroup, a product of at least `|S|` elements is a right zero. -/
theorem IsDefinite.mul_map_eq (h : IsDefinite S) (hw : Nat.card S ≤ w.length) (s : S) :
    s * f w = f w := by
  obtain ⟨x, e, y, he, hw⟩ := FreeSemigroup.exists_isIdempotentElem_map_eq_mul_mul f hw
  simp only [hw, ← mul_assoc, h e he]

/-- In a finite reverse definite semigroup, a product of at least `|S|` elements is a left
zero. -/
theorem IsReverseDefinite.map_mul_eq (h : IsReverseDefinite S) (hw : Nat.card S ≤ w.length)
    (s : S) : f w * s = f w := by
  obtain ⟨x, e, y, he, hw⟩ := FreeSemigroup.exists_isIdempotentElem_map_eq_mul_mul f hw
  simp only [hw, mul_assoc, h e he]

/-- In a finite locally trivial semigroup, a product of at least `|S|` elements absorbs anything
placed between two copies of it. -/
theorem IsLocallyTrivial.map_mul_map_eq (h : IsLocallyTrivial S) (hw : Nat.card S ≤ w.length)
    (s : S) : f w * s * f w = f w := by
  obtain ⟨x, e, y, he, hw⟩ := FreeSemigroup.exists_isIdempotentElem_map_eq_mul_mul f hw
  rw [hw, show x * e * y * s * (x * e * y) = x * (e * (y * s * x) * e) * y by
    simp only [mul_assoc], h e he]

theorem IsLocallyTrivial.isIdempotentElem_map (h : IsLocallyTrivial S)
    (hw : Nat.card S ≤ w.length) : IsIdempotentElem (f w) := by
  obtain ⟨x, e, y, he, hw⟩ := FreeSemigroup.exists_isIdempotentElem_map_eq_mul_mul f hw
  rw [IsIdempotentElem, hw, show x * e * y * (x * e * y) = x * (e * (y * x) * e) * y by
    simp only [mul_assoc], h e he]

end LongProducts

/-! ### The bundled pseudovarieties -/

/-- The pseudovariety **D** of definite semigroups. -/
def definiteVariety : Pseudovariety.{u} where
  mem S _ := Finite S ∧ IsDefinite S
  finite_of_mem h := h.1
  sub hf h := have := h.1; ⟨.of_injective _ hf, h.2.of_injective hf⟩
  quot hf h := have := h.1; ⟨.of_surjective _ hf, h.2.of_surjective hf⟩
  prod hS hT := have := hS.1; have := hT.1; ⟨inferInstance, hS.2.prod hT.2⟩
  memUnit := ⟨inferInstance, fun _ _ _ ↦ rfl⟩

/-- The pseudovariety **K** of reverse definite semigroups. -/
def reverseDefiniteVariety : Pseudovariety.{u} where
  mem S _ := Finite S ∧ IsReverseDefinite S
  finite_of_mem h := h.1
  sub hf h := have := h.1; ⟨.of_injective _ hf, h.2.of_injective hf⟩
  quot hf h := have := h.1; ⟨.of_surjective _ hf, h.2.of_surjective hf⟩
  prod hS hT := have := hS.1; have := hT.1; ⟨inferInstance, hS.2.prod hT.2⟩
  memUnit := ⟨inferInstance, fun _ _ _ ↦ rfl⟩

/-- The pseudovariety **LI** of locally trivial semigroups. -/
def locallyTrivialVariety : Pseudovariety.{u} where
  mem S _ := Finite S ∧ IsLocallyTrivial S
  finite_of_mem h := h.1
  sub hf h := have := h.1; ⟨.of_injective _ hf, h.2.of_injective hf⟩
  quot hf h := have := h.1; ⟨.of_surjective _ hf, h.2.of_surjective hf⟩
  prod hS hT := have := hS.1; have := hT.1; ⟨inferInstance, hS.2.prod hT.2⟩
  memUnit := ⟨inferInstance, fun _ _ _ ↦ rfl⟩

@[simp] theorem mem_definiteVariety {S : Type u} [Semigroup S] :
    definiteVariety.mem S ↔ Finite S ∧ IsDefinite S := Iff.rfl

@[simp] theorem mem_reverseDefiniteVariety {S : Type u} [Semigroup S] :
    reverseDefiniteVariety.mem S ↔ Finite S ∧ IsReverseDefinite S := Iff.rfl

@[simp] theorem mem_locallyTrivialVariety {S : Type u} [Semigroup S] :
    locallyTrivialVariety.mem S ↔ Finite S ∧ IsLocallyTrivial S := Iff.rfl

end Semigroup
