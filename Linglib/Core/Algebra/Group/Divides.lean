/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Division of monoids

A monoid `T` **divides** a monoid `S` ([eilenberg-1976]'s `≺`; a *subquotient*, or for groups
a *section*) when `T` is a homomorphic image of a submonoid of `S`. Division is the comparison
order of finite semigroup theory: pseudovarieties are division-closed classes, and the
syntactic monoid of a language divides every monoid recognising it.

## Main definitions

* `Monoid.Divides T S`: `T` is a homomorphic image of a submonoid of `S`.

## Main results

* `Monoid.Divides.trans`: division is transitive.
* `Monoid.Divides.card_le`: a divisor of a finite monoid is no larger.
* `Monoid.Divides.nonempty_mulEquiv`: finite monoids dividing each other are isomorphic.

## Implementation notes

Division relates carriers-with-instances, not terms of one type, so there is no `Trans` or
`Preorder` instance to register; transitivity and antisymmetry-up-to-`MulEquiv` are standalone
lemmas.
-/

namespace Monoid

variable {T S R : Type*} [Monoid T] [Monoid S] [Monoid R]

/-- `T` **divides** `S` when `T` is a homomorphic image of a submonoid of `S`. -/
def Divides (T S : Type*) [Monoid T] [Monoid S] : Prop :=
  ∃ (N : Submonoid S) (f : N →* T), Function.Surjective f

/-- A homomorphic image divides. -/
theorem Divides.of_surjective (f : S →* T) (hf : Function.Surjective f) : Divides T S :=
  ⟨⊤, f.comp Submonoid.topEquiv.toMonoidHom, hf.comp Submonoid.topEquiv.surjective⟩

/-- An embedded monoid divides. -/
theorem Divides.of_injective (f : T →* S) (hf : Function.Injective f) : Divides T S :=
  have e := MulEquiv.ofBijective f.mrangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.mrangeRestrict_surjective⟩
  ⟨MonoidHom.mrange f, e.symm.toMonoidHom, e.symm.surjective⟩

theorem _root_.MulEquiv.divides (e : T ≃* S) : Divides T S :=
  Divides.of_surjective e.symm.toMonoidHom e.symm.surjective

theorem Divides.refl (T : Type*) [Monoid T] : Divides T T :=
  (MulEquiv.refl T).divides

theorem Divides.trans (hTS : Divides T S) (hSR : Divides S R) : Divides T R := by
  obtain ⟨N, f, hf⟩ := hTS
  obtain ⟨M, g, hg⟩ := hSR
  have hcomap : Function.Surjective (g.submonoidComap N) := by
    rintro ⟨n, hn⟩
    obtain ⟨m, rfl⟩ := hg n
    exact ⟨⟨m, hn⟩, rfl⟩
  have e := Submonoid.equivMapOfInjective (N.comap g) M.subtype M.subtype_injective
  exact ⟨(N.comap g).map M.subtype, (f.comp (g.submonoidComap N)).comp e.symm.toMonoidHom,
    (hf.comp hcomap).comp e.symm.surjective⟩

theorem divides_prod_left (T S : Type*) [Monoid T] [Monoid S] : Divides T (T × S) :=
  Divides.of_injective (MonoidHom.inl T S) fun _ _ h => congrArg Prod.fst h

theorem divides_prod_right (T S : Type*) [Monoid T] [Monoid S] : Divides T (S × T) :=
  Divides.of_injective (MonoidHom.inr S T) fun _ _ h => congrArg Prod.snd h

/-- A divisor of a finite monoid is no larger. -/
theorem Divides.card_le [Finite S] (h : Divides T S) : Nat.card T ≤ Nat.card S := by
  obtain ⟨N, f, hf⟩ := h
  exact (Nat.card_le_card_of_surjective f hf).trans
    (Nat.card_le_card_of_injective N.subtype N.subtype_injective)

/-- Finite monoids dividing each other are isomorphic ([eilenberg-1976]): division is
antisymmetric up to `MulEquiv` on finite monoids. -/
theorem Divides.nonempty_mulEquiv [Finite T] [Finite S] (hTS : Divides T S)
    (hST : Divides S T) : Nonempty (T ≃* S) := by
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
