/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.SyntacticSemigroup`.
-/
import Linglib.Core.Algebra.Free
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.GroupTheory.Congruence.Hom
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Option

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
  Con.mkMulHom_surjective _

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
theorem syntacticSemigroupCon_compl : Lᶜ.syntacticSemigroupCon = L.syntacticSemigroupCon :=
  Con.ext fun _ _ => SyntacticEquiv.compl_iff

/-- Conversely, a finite syntactic semigroup forces a finite syntactic monoid: the monoid is
covered by the semigroup together with the identity, which is Eilenberg's `M_A = S_A ∪ {1}`. -/
theorem finite_syntacticMonoid_of_finite_syntacticSemigroup [Finite L.syntacticSemigroup] :
    Finite L.syntacticMonoid := by
  refine .of_surjective (β := L.syntacticMonoid)
    (Option.elim · 1 L.syntacticSemigroupToMonoid) fun m => ?_
  obtain ⟨w, rfl⟩ := L.syntacticClass_surjective m
  match w with
  | [] => exact ⟨none, L.syntacticClass_nil.symm⟩
  | c :: w => exact ⟨some (L.toSyntacticSemigroup ⟨c, w⟩), rfl⟩

/-- **Myhill–Nerode, semigroup form**: a language is regular exactly when its syntactic semigroup
is finite. -/
theorem isRegular_iff_finite_syntacticSemigroup :
    L.IsRegular ↔ Finite L.syntacticSemigroup :=
  ⟨fun h => haveI := finite_syntacticMonoid h; inferInstance,
   fun _ => isRegular_of_finite_syntacticMonoid L.finite_syntacticMonoid_of_finite_syntacticSemigroup⟩

theorem isRegular_of_finite_syntacticSemigroup (h : Finite L.syntacticSemigroup) : L.IsRegular :=
  L.isRegular_iff_finite_syntacticSemigroup.2 h
/-! ### Meets of syntactic congruences -/

/-- Words indistinguishable for both `L` and `M` are indistinguishable for `L ⊓ M`. -/
theorem inf_syntacticSemigroupCon_le_syntacticSemigroupCon_inf (L M : Language α) :
    L.syntacticSemigroupCon ⊓ M.syntacticSemigroupCon ≤ (L ⊓ M).syntacticSemigroupCon := by
  rw [Con.le_def]
  intro u v huv x y
  rw [Con.inf_iff_and, syntacticSemigroupCon_iff, syntacticSemigroupCon_iff] at huv
  exact and_congr (huv.1 x y) (huv.2 x y)

/-- The kernel of the pairing of the two syntactic morphisms is the meet of the two syntactic
congruences. -/
theorem ker_prod_toSyntacticSemigroup (L M : Language α) :
    Con.ker (L.toSyntacticSemigroup.prod M.toSyntacticSemigroup) =
      L.syntacticSemigroupCon ⊓ M.syntacticSemigroupCon :=
  Con.ext fun u v => by
    rw [Con.ker_rel, MulHom.prod_apply, MulHom.prod_apply, Prod.ext_iff,
      toSyntacticSemigroup_eq_iff, toSyntacticSemigroup_eq_iff, Con.inf_iff_and]

/-- **The syntactic semigroup does not see the empty word.** Its congruence quantifies only over
nonempty words, so adjoining `[]` to a language leaves it unchanged. This is the `+`-variety
semantics working as intended ([eilenberg-1976] indexes varieties of sets on `Σ⁺`), and it is why
`Semigroup.Pseudovariety.langs` cannot distinguish `L` from `insert [] L`. -/
theorem syntacticSemigroupCon_insert_nil (L : Language α) :
    (insert [] L).syntacticSemigroupCon = L.syntacticSemigroupCon :=
  Con.ext fun u v => by
    have h : ∀ (x : List α) (w : FreeSemigroup α) (y : List α),
        x ++ w.toList ++ y ∈ insert [] L ↔ x ++ w.toList ++ y ∈ L := fun x w y => by
      refine (Set.mem_insert_iff).trans (or_iff_right ?_)
      intro hnil
      exact absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hnil).1).2
        (FreeSemigroup.toList_ne_nil w)
    exact forall_congr' fun x => forall_congr' fun y => iff_congr (h x u y) (h x v y)

end Language
