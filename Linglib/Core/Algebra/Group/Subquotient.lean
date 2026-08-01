/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Subquotients of monoids

A monoid `T` is a **subquotient** of a monoid `S` when `T` is a homomorphic image of a
submonoid of `S` — the relation called **division** (`T ≼ S`) in finite semigroup theory
[eilenberg-1976], and a *section* for groups. It is the comparison order of the algebraic
theory of automata: pseudovarieties are the division-closed classes, and the syntactic monoid
of a language is a subquotient of every monoid recognising it.

## Main definitions

* `Monoid.IsSubquotient T S`: `T` is a homomorphic image of a submonoid of `S`.

## Main results

* `Monoid.IsSubquotient.trans`: the subquotient relation is transitive.
* `Monoid.IsSubquotient.card_le`: a subquotient of a finite monoid is no larger.
* `Monoid.IsSubquotient.nonempty_mulEquiv`: finite monoids that are subquotients of each
  other are isomorphic.

## Implementation notes

The relation compares carriers-with-instances, not terms of one type, so there is no `Trans`
or `Preorder` instance to register; transitivity and antisymmetry-up-to-`MulEquiv` are
standalone lemmas.
-/

namespace Monoid

variable {T S R : Type*} [Monoid T] [Monoid S] [Monoid R]

/-- `T` is a **subquotient** of `S` when `T` is a homomorphic image of a submonoid of `S` —
the **division** `T ≼ S` of finite semigroup theory [eilenberg-1976]. -/
@[to_additive /-- `T` is a **subquotient** of `S` when `T` is a homomorphic image of an
additive submonoid of `S`. -/]
def IsSubquotient (T S : Type*) [Monoid T] [Monoid S] : Prop :=
  ∃ (N : Submonoid S) (f : N →* T), Function.Surjective f

/-- A homomorphic image is a subquotient. -/
@[to_additive]
theorem IsSubquotient.of_surjective (f : S →* T) (hf : Function.Surjective f) :
    IsSubquotient T S :=
  ⟨⊤, f.comp Submonoid.topEquiv.toMonoidHom, hf.comp Submonoid.topEquiv.surjective⟩

/-- An embedded monoid is a subquotient. -/
@[to_additive]
theorem IsSubquotient.of_injective (f : T →* S) (hf : Function.Injective f) :
    IsSubquotient T S :=
  have e := MulEquiv.ofBijective f.mrangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.mrangeRestrict_surjective⟩
  ⟨MonoidHom.mrange f, e.symm.toMonoidHom, e.symm.surjective⟩

@[to_additive]
theorem _root_.MulEquiv.isSubquotient (e : T ≃* S) : IsSubquotient T S :=
  IsSubquotient.of_surjective e.symm.toMonoidHom e.symm.surjective

/-- A submonoid is a subquotient. -/
@[to_additive]
theorem _root_.Submonoid.isSubquotient (N : Submonoid S) : IsSubquotient N S :=
  IsSubquotient.of_injective N.subtype N.subtype_injective

/-- A congruence quotient is a subquotient. -/
@[to_additive]
theorem _root_.Con.isSubquotient_quotient (c : Con S) : IsSubquotient c.Quotient S :=
  IsSubquotient.of_surjective c.mk' c.mk'_surjective

@[to_additive]
theorem IsSubquotient.refl (T : Type*) [Monoid T] : IsSubquotient T T :=
  (MulEquiv.refl T).isSubquotient

@[to_additive]
theorem IsSubquotient.trans (hTS : IsSubquotient T S) (hSR : IsSubquotient S R) :
    IsSubquotient T R := by
  obtain ⟨N, f, hf⟩ := hTS
  obtain ⟨M, g, hg⟩ := hSR
  have hcomap : Function.Surjective (g.submonoidComap N) := by
    rintro ⟨n, hn⟩
    obtain ⟨m, rfl⟩ := hg n
    exact ⟨⟨m, hn⟩, rfl⟩
  have e := Submonoid.equivMapOfInjective (N.comap g) M.subtype M.subtype_injective
  exact ⟨(N.comap g).map M.subtype, (f.comp (g.submonoidComap N)).comp e.symm.toMonoidHom,
    (hf.comp hcomap).comp e.symm.surjective⟩

@[to_additive]
theorem isSubquotient_prod_left (T S : Type*) [Monoid T] [Monoid S] :
    IsSubquotient T (T × S) :=
  IsSubquotient.of_injective (MonoidHom.inl T S) fun _ _ h => congrArg Prod.fst h

@[to_additive]
theorem isSubquotient_prod_right (T S : Type*) [Monoid T] [Monoid S] :
    IsSubquotient T (S × T) :=
  IsSubquotient.of_injective (MonoidHom.inr S T) fun _ _ h => congrArg Prod.snd h

/-- A subquotient of a finite monoid is no larger. -/
@[to_additive]
theorem IsSubquotient.card_le [Finite S] (h : IsSubquotient T S) :
    Nat.card T ≤ Nat.card S := by
  obtain ⟨N, f, hf⟩ := h
  exact (Nat.card_le_card_of_surjective f hf).trans
    (Nat.card_le_card_of_injective N.subtype N.subtype_injective)

/-- Finite monoids that are subquotients of each other are isomorphic ([eilenberg-1976]):
division is antisymmetric up to `MulEquiv` on finite monoids. -/
@[to_additive]
theorem IsSubquotient.nonempty_mulEquiv [Finite T] [Finite S] (hTS : IsSubquotient T S)
    (hST : IsSubquotient S T) : Nonempty (T ≃* S) := by
  have hcard : Nat.card T = Nat.card S := le_antisymm hTS.card_le hST.card_le
  obtain ⟨N, f, hf⟩ := hTS
  have hN : Nat.card N = Nat.card S :=
    le_antisymm (Nat.card_le_card_of_injective N.subtype N.subtype_injective)
      (hcard ▸ Nat.card_le_card_of_surjective f hf)
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_surjective_and_card f).mpr ⟨hf, by rw [hN, hcard]⟩
  have hbij' : Function.Bijective N.subtype :=
    (Nat.bijective_iff_injective_and_card N.subtype).mpr ⟨N.subtype_injective, hN⟩
  exact ⟨(MulEquiv.ofBijective f hbij).symm.trans (MulEquiv.ofBijective N.subtype hbij')⟩

end Monoid
