/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.SyntacticSemigroup`.
-/
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.Algebra.Free

/-!
# The syntactic semigroup of a language

The *syntactic semigroup* of `L : Language α` is the quotient of the free semigroup `FreeSemigroup
α` — the nonempty words — by the syntactic congruence. It is the primary algebraic invariant of a
language ([eilenberg-1976]): the syntactic monoid is obtained from it by adjoining an identity, and
the classes `D`, `K`, `LI`, `N` are varieties of *semigroups*, not of monoids. Over the free monoid
those classes collapse, since the definite condition applied to the idempotent `1` forces
triviality; stating them on `FreeSemigroup α` is what avoids the collapse.

`Language.SyntacticEquiv` is the underlying two-sided context relation, defined with
`Language.syntacticCon`: both congruences are that one relation read on their own carrier, and
share its multiplicativity lemma `SyntacticEquiv.append`.

## Main definitions

* `Language.syntacticSemigroupCon`: the syntactic congruence on `FreeSemigroup α`.
* `Language.syntacticSemigroup`: the quotient semigroup.
* `Language.toSyntacticSemigroup`: the projection, as a `MulHom`.

## Main results

* `Language.syntacticSemigroupToMonoid_injective`: the syntactic semigroup embeds in the
  syntactic monoid.

## Implementation notes

The projection is `Con.mkMulHom`, mathlib's `MulHom`-valued quotient map for a `Con` over a plain
`Mul` (the monoid-valued `Con.mk'` would not apply). `FreeSemigroup.toList` is absent from mathlib
and is supplied by `Linglib.Core.Algebra.Free`.
-/

namespace Language

variable {α : Type*} (L : Language α)

/-- The **syntactic congruence** on the free semigroup: the syntactic equivalence of the
underlying nonempty words. -/
def syntacticSemigroupCon : Con (FreeSemigroup α) where
  r u v := L.SyntacticEquiv u.toList v.toList
  iseqv := ⟨fun _ => .refl _, .symm, .trans⟩
  mul' hab hcd := hab.append hcd

theorem syntacticSemigroupCon_iff {u v : FreeSemigroup α} :
    L.syntacticSemigroupCon u v ↔ L.SyntacticEquiv u.toList v.toList := Iff.rfl

/-- The **syntactic semigroup** of `L`: the quotient of `FreeSemigroup α` by the syntactic
congruence. -/
def syntacticSemigroup : Type _ := (syntacticSemigroupCon L).Quotient

instance : Semigroup (syntacticSemigroup L) :=
  inferInstanceAs (Semigroup (syntacticSemigroupCon L).Quotient)

/-- The canonical projection sending a nonempty word to its syntactic class. -/
def toSyntacticSemigroup : FreeSemigroup α →ₙ* L.syntacticSemigroup :=
  Con.mkMulHom (syntacticSemigroupCon L)

theorem toSyntacticSemigroup_eq_iff {u v : FreeSemigroup α} :
    L.toSyntacticSemigroup u = L.toSyntacticSemigroup v ↔ L.syntacticSemigroupCon u v :=
  Con.eq _

theorem toSyntacticSemigroup_surjective : Function.Surjective L.toSyntacticSemigroup :=
  fun s => Quotient.exists_rep s

/-! ### Relation to the syntactic monoid -/

/-- The syntactic semigroup embeds into the syntactic monoid: a nonempty word is sent to its
class in the monoid. It is injective because both quotients are by the same context relation. -/
def syntacticSemigroupToMonoid : L.syntacticSemigroup →ₙ* L.syntacticMonoid where
  toFun := Quotient.lift (fun u : FreeSemigroup α => L.syntacticClass u.toList)
    fun _ _ h => syntacticClass_eq_iff.mpr h
  map_mul' := by rintro ⟨u⟩ ⟨v⟩; exact L.syntacticClass_append u.toList v.toList

@[simp] theorem syntacticSemigroupToMonoid_apply (u : FreeSemigroup α) :
    L.syntacticSemigroupToMonoid (L.toSyntacticSemigroup u) = L.syntacticClass u.toList := rfl


theorem syntacticSemigroupToMonoid_injective :
    Function.Injective L.syntacticSemigroupToMonoid := by
  rintro ⟨u⟩ ⟨v⟩ h
  exact Quotient.sound (syntacticClass_eq_iff.mp h)

/-- A regular language has a finite syntactic semigroup, since it embeds in the syntactic
monoid. -/
instance instFiniteSyntacticSemigroup [Finite L.syntacticMonoid] :
    Finite L.syntacticSemigroup :=
  .of_injective _ L.syntacticSemigroupToMonoid_injective

/-- A regular language has a finite syntactic semigroup. -/
theorem finite_syntacticSemigroup (h : L.IsRegular) : Finite L.syntacticSemigroup :=
  haveI := finite_syntacticMonoid h
  inferInstance

/-- The syntactic congruence is complement-invariant, as on the monoid side. -/
theorem syntacticSemigroupCon_compl : Lᶜ.syntacticSemigroupCon = L.syntacticSemigroupCon := by
  ext u v
  simp only [syntacticSemigroupCon_iff, SyntacticEquiv]
  exact ⟨fun h x y => not_iff_not.mp (h x y), fun h x y => not_iff_not.mpr (h x y)⟩

end Language
