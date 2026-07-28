/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.SyntacticSemigroup`.
-/
import Linglib.Core.Computability.SyntacticMonoid
import Mathlib.Algebra.Free

/-!
# The syntactic semigroup of a language

The *syntactic semigroup* of `L : Language α` is the quotient of the free semigroup `FreeSemigroup
α` — the nonempty words — by the syntactic congruence. It is the primary algebraic invariant of a
language ([eilenberg-1976]): the syntactic monoid is obtained from it by adjoining an identity, and
the classes `D`, `K`, `LI`, `N` are varieties of *semigroups*, not of monoids. Over the free monoid
those classes collapse, since the definite condition applied to the idempotent `1` forces
triviality; stating them on `FreeSemigroup α` is what avoids the collapse.

`Language.SyntacticEquiv` is the underlying two-sided context relation, shared with
`Language.syntacticCon`: the two congruences differ only in the monoid they live on.

## Main definitions

* `Language.SyntacticEquiv`: two words are equivalent when no two-sided context separates them.
* `Language.syntacticSemigroupCon`: the syntactic congruence on `FreeSemigroup α`.
* `Language.syntacticSemigroup`: the quotient semigroup.
* `Language.toSyntacticSemigroup`: the projection, as a `MulHom`.
* `FreeSemigroup.toList`: the nonempty word underlying a free-semigroup element.

## Main results

* `Language.syntacticSemigroupClass_eq_iff`: two nonempty words share a class exactly when no
  two-sided context separates them.

## Implementation notes

The projection is built by hand rather than with `Con.mk'`, which mathlib provides only as
`M →* c.Quotient` for `[Monoid M]`; there is no `MulHom`-valued projection for a `Con` over a plain
`Mul`. `FreeSemigroup.toList` is likewise absent from mathlib.
-/

namespace FreeSemigroup

variable {α : Type*}

/-- The nonempty word underlying a free-semigroup element. -/
def toList (u : FreeSemigroup α) : List α := u.head :: u.tail

@[simp] theorem toList_of (a : α) : (of a).toList = [a] := rfl

@[simp] theorem toList_mul (u v : FreeSemigroup α) :
    (u * v).toList = u.toList ++ v.toList := rfl

@[simp] theorem toList_ne_nil (u : FreeSemigroup α) : u.toList ≠ [] := List.cons_ne_nil _ _

@[simp] theorem length_toList (u : FreeSemigroup α) : u.toList.length = u.length := rfl

theorem toList_injective : Function.Injective (toList (α := α)) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ h
  simpa [toList, and_comm] using h

end FreeSemigroup

namespace Language

variable {α : Type*} (L : Language α)

/-- Two words are **syntactically equivalent** for `L` when no two-sided context distinguishes
them as `L`-members. This is the relation underlying both syntactic congruences. -/
def SyntacticEquiv (u v : List α) : Prop := ∀ x y : List α, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L

variable {L} in
theorem SyntacticEquiv.refl (u : List α) : L.SyntacticEquiv u u := fun _ _ => Iff.rfl

variable {L} in
theorem SyntacticEquiv.symm {u v : List α} (h : L.SyntacticEquiv u v) : L.SyntacticEquiv v u :=
  fun x y => (h x y).symm

variable {L} in
theorem SyntacticEquiv.trans {u v w : List α} (h : L.SyntacticEquiv u v)
    (h' : L.SyntacticEquiv v w) : L.SyntacticEquiv u w := fun x y => (h x y).trans (h' x y)

variable {L} in
/-- Syntactically equivalent words agree on membership: take the empty context. -/
theorem mem_iff_of_syntacticEquiv {u v : List α} (h : L.SyntacticEquiv u v) : u ∈ L ↔ v ∈ L := by
  have := h [] []
  simpa using this

/-- The **syntactic congruence** on the free semigroup: the syntactic equivalence of the
underlying nonempty words. -/
def syntacticSemigroupCon : Con (FreeSemigroup α) where
  r u v := L.SyntacticEquiv u.toList v.toList
  iseqv := ⟨fun _ => .refl _, .symm, .trans⟩
  mul' {a b c d} hab hcd x y := by
    have h1 := hab x (c.toList ++ y)
    have h2 := hcd (x ++ b.toList) y
    simp only [FreeSemigroup.toList_mul, ← List.append_assoc] at h1 h2 ⊢
    exact h1.trans h2

theorem syntacticSemigroupCon_iff {u v : FreeSemigroup α} :
    L.syntacticSemigroupCon u v ↔ L.SyntacticEquiv u.toList v.toList := Iff.rfl

/-- The **syntactic semigroup** of `L`: the quotient of `FreeSemigroup α` by the syntactic
congruence. -/
def syntacticSemigroup : Type _ := (syntacticSemigroupCon L).Quotient

instance : Semigroup (syntacticSemigroup L) :=
  inferInstanceAs (Semigroup (syntacticSemigroupCon L).Quotient)

/-- The canonical projection sending a nonempty word to its syntactic class. -/
def toSyntacticSemigroup : FreeSemigroup α →ₙ* L.syntacticSemigroup where
  toFun := (syntacticSemigroupCon L).toQuotient
  map_mul' _ _ := rfl

theorem toSyntacticSemigroup_eq_iff {u v : FreeSemigroup α} :
    L.toSyntacticSemigroup u = L.toSyntacticSemigroup v ↔ L.syntacticSemigroupCon u v :=
  Con.eq _

theorem toSyntacticSemigroup_surjective : Function.Surjective L.toSyntacticSemigroup :=
  fun s => Quotient.exists_rep s

/-- The syntactic class of a nonempty word. -/
def syntacticSemigroupClass (u : FreeSemigroup α) : L.syntacticSemigroup :=
  L.toSyntacticSemigroup u

@[simp] theorem syntacticSemigroupClass_mul (u v : FreeSemigroup α) :
    L.syntacticSemigroupClass (u * v)
      = L.syntacticSemigroupClass u * L.syntacticSemigroupClass v := rfl

variable {L} in
/-- Two nonempty words share a syntactic class exactly when no two-sided context distinguishes
them as `L`-members. -/
theorem syntacticSemigroupClass_eq_iff {u v : FreeSemigroup α} :
    L.syntacticSemigroupClass u = L.syntacticSemigroupClass v
      ↔ ∀ x y : List α, x ++ u.toList ++ y ∈ L ↔ x ++ v.toList ++ y ∈ L :=
  toSyntacticSemigroup_eq_iff L

/-! ### Relation to the syntactic monoid -/

/-- The syntactic semigroup embeds into the syntactic monoid: a nonempty word is sent to its
class in the monoid. Eilenberg's `M_A` adjoins an identity to `S_A`, so this is injective. -/
def syntacticSemigroupToMonoid : L.syntacticSemigroup →ₙ* L.syntacticMonoid where
  toFun := Quotient.lift (fun u : FreeSemigroup α => L.syntacticClass u.toList)
    fun _ _ h => syntacticClass_eq_iff.mpr h
  map_mul' := by rintro ⟨u⟩ ⟨v⟩; exact L.syntacticClass_append u.toList v.toList

@[simp] theorem syntacticSemigroupToMonoid_apply (u : FreeSemigroup α) :
    L.syntacticSemigroupToMonoid (L.syntacticSemigroupClass u) = L.syntacticClass u.toList := rfl

theorem syntacticSemigroupToMonoid_injective :
    Function.Injective L.syntacticSemigroupToMonoid := by
  rintro ⟨u⟩ ⟨v⟩ h
  exact Quotient.sound (syntacticClass_eq_iff.mp h)

/-- A regular language has a finite syntactic semigroup, since it embeds in the syntactic
monoid. -/
instance instFiniteSyntacticSemigroup [Finite L.syntacticMonoid] :
    Finite L.syntacticSemigroup :=
  .of_injective _ L.syntacticSemigroupToMonoid_injective

/-- The syntactic congruence is complement-invariant, as on the monoid side. -/
theorem syntacticSemigroupCon_compl : Lᶜ.syntacticSemigroupCon = L.syntacticSemigroupCon := by
  ext u v
  simp only [syntacticSemigroupCon_iff, SyntacticEquiv]
  exact ⟨fun h x y => not_iff_not.mp (h x y), fun h x y => not_iff_not.mpr (h x y)⟩

end Language
