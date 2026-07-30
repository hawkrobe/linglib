/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.SyntacticSemigroup`.
-/
import Linglib.Core.Algebra.FreeMonoid.FreeSemigroup
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.GroupTheory.Congruence.Hom
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Data.Fintype.Option

/-!
# The syntactic semigroup of a language

The *syntactic semigroup* of `L : Language α` is the quotient of the free semigroup `FreeSemigroup
α` — the nonempty words — by the syntactic congruence: the pullback of `Language.syntacticCon`
along `FreeSemigroup.toFreeMonoid` (`syntacticSemigroupCon_eq_comap`). The two quotients are
related by `M_A = S_A ∪ {1}` ([eilenberg-1976]), a union that is disjoint exactly when no nonempty
word is equivalent to the empty one.

It is the primary invariant for varieties: `D`, `K`, `LI` and `N` are varieties of *semigroups*,
not of monoids. Over the free monoid they collapse, since the definite condition applied to the
idempotent `1` forces triviality; stating them on `FreeSemigroup α` is what avoids the collapse.

## Main definitions

- `Language.syntacticSemigroupCon`: the syntactic congruence on `FreeSemigroup α`
- `Language.SyntacticSemigroup`: the quotient semigroup
- `Language.toSyntacticSemigroup`: the projection, as a `MulHom`
- `Language.RecognizesSemigroup`: recognition of a language by a homomorphism to a semigroup

## Main results

- `Language.syntacticSemigroupCon_eq_comap`: the congruence is the monoid one, pulled back
- `Language.syntacticSemigroupToMonoid_injective`: the syntactic semigroup embeds in the
  syntactic monoid
- `Language.isRegular_iff_finite_syntacticSemigroup`: Myhill–Nerode in semigroup form
- `Language.recognizesSemigroup_iff_recognizes`: recognition by `η` is recognition by its
  unitization `WithOne.mapMulHom η` — Eilenberg's `M_A = S_A ∪ {1}` at the recognition level
- `Language.syntacticSemigroupCon_insert_nil`: the syntactic semigroup does not see the empty
  word

## Implementation notes

The projection is `Con.mkMulHom`, mathlib's `MulHom`-valued quotient map for a `Con` over a plain
`Mul` (the monoid-valued `Con.mk'` would not apply). Words are carried to `List α` by
`FreeSemigroup.toList` from `Linglib.Core.Algebra.FreeMonoid.FreeSemigroup`, a thin layer over
`FreeSemigroup.toFreeMonoid`.

## References

* [eilenberg-1976]
* [pin-mfa]
-/

namespace Language

variable {α : Type*} {L : Language α}

/-! ### The syntactic congruence and semigroup -/

/-- The *syntactic congruence* of `L` on the free semigroup identifies two nonempty words when
no two-sided context distinguishes them as `L`-members. -/
def syntacticSemigroupCon (L : Language α) : Con (FreeSemigroup α) where
  r u v := L.SyntacticEquiv u.toList v.toList
  iseqv := ⟨fun _ => .refl _, .symm, .trans⟩
  mul' hab hcd := by simpa using hab.append hcd

theorem syntacticSemigroupCon_iff {u v : FreeSemigroup α} :
    L.syntacticSemigroupCon u v ↔ L.SyntacticEquiv u.toList v.toList := Iff.rfl

/-- The syntactic congruence on nonempty words is the monoid one, pulled back along
`FreeSemigroup.toFreeMonoid`. -/
theorem syntacticSemigroupCon_eq_comap (L : Language α) :
    L.syntacticSemigroupCon = L.syntacticCon.comap FreeSemigroup.toFreeMonoid (map_mul _) :=
  Con.ext fun _ _ => Iff.rfl

/-- The *syntactic semigroup* of `L` is the quotient of `FreeSemigroup α` by the syntactic
congruence. -/
abbrev SyntacticSemigroup (L : Language α) := (syntacticSemigroupCon L).Quotient

/-- The *syntactic morphism* of `L` projects `FreeSemigroup α` onto the syntactic semigroup. -/
def toSyntacticSemigroup (L : Language α) : FreeSemigroup α →ₙ* L.SyntacticSemigroup :=
  Con.mkMulHom (syntacticSemigroupCon L)

theorem toSyntacticSemigroup_eq_iff {u v : FreeSemigroup α} :
    L.toSyntacticSemigroup u = L.toSyntacticSemigroup v ↔ L.syntacticSemigroupCon u v :=
  Con.eq _

theorem toSyntacticSemigroup_surjective (L : Language α) :
    Function.Surjective L.toSyntacticSemigroup :=
  Con.mkMulHom_surjective _

theorem ker_toSyntacticSemigroup (L : Language α) :
    Con.ker L.toSyntacticSemigroup = L.syntacticSemigroupCon :=
  Con.ker_mkMulHom_eq _

/-! ### Relation to the syntactic monoid -/

/-- The syntactic class of the underlying nonempty word, as a homomorphism on the free
semigroup. -/
def syntacticClassMulHom (L : Language α) : FreeSemigroup α →ₙ* L.SyntacticMonoid where
  toFun u := L.syntacticClass u.toList
  map_mul' u v := by simp

theorem ker_syntacticClassMulHom (L : Language α) :
    Con.ker L.syntacticClassMulHom = L.syntacticSemigroupCon :=
  Con.ext fun _ _ => ((Con.ker_rel _).trans syntacticClass_eq_iff).trans
    syntacticSemigroupCon_iff.symm

/-- The syntactic semigroup embeds into the syntactic monoid: a nonempty word is sent to its
class in the monoid. -/
def syntacticSemigroupToMonoid (L : Language α) : L.SyntacticSemigroup →ₙ* L.SyntacticMonoid :=
  (syntacticSemigroupCon L).liftMulHom L.syntacticClassMulHom L.ker_syntacticClassMulHom.ge

@[simp] theorem syntacticSemigroupToMonoid_apply (L : Language α) (u : FreeSemigroup α) :
    L.syntacticSemigroupToMonoid (L.toSyntacticSemigroup u) = L.syntacticClass u.toList := rfl

theorem syntacticSemigroupToMonoid_injective (L : Language α) :
    Function.Injective L.syntacticSemigroupToMonoid :=
  Con.liftMulHom_injective L.ker_syntacticClassMulHom.le

instance [Finite L.SyntacticMonoid] : Finite L.SyntacticSemigroup :=
  .of_injective _ L.syntacticSemigroupToMonoid_injective

/-- The syntactic monoid is the syntactic semigroup with an identity adjoined: every element is
the class of the empty word or the image of one of the semigroup. -/
theorem eq_one_or_mem_range_syntacticSemigroupToMonoid (L : Language α) (s : L.SyntacticMonoid) :
    s = 1 ∨ s ∈ Set.range L.syntacticSemigroupToMonoid := by
  obtain ⟨w, rfl⟩ := L.syntacticClass_surjective s
  rcases w with _ | ⟨c, w⟩
  exacts [.inl L.syntacticClass_nil, .inr ⟨L.toSyntacticSemigroup ⟨c, w⟩, by simp⟩]

/-- A finite syntactic semigroup forces a finite syntactic monoid: the monoid is covered by
`WithOne` of the semigroup, which is Eilenberg's `M_A = S_A ∪ {1}`. -/
theorem finite_syntacticMonoid_of_finite_syntacticSemigroup (L : Language α)
    [Finite L.SyntacticSemigroup] : Finite L.SyntacticMonoid := by
  haveI : Finite (WithOne L.SyntacticSemigroup) := inferInstanceAs (Finite (Option _))
  refine .of_surjective (WithOne.lift L.syntacticSemigroupToMonoid) fun m => ?_
  rcases L.eq_one_or_mem_range_syntacticSemigroupToMonoid m with rfl | ⟨t, rfl⟩
  exacts [⟨1, map_one _⟩, ⟨(t : WithOne _), WithOne.lift_coe _ _⟩]

/-! ### Myhill–Nerode -/

theorem IsRegular.finite_syntacticSemigroup (h : L.IsRegular) : Finite L.SyntacticSemigroup :=
  haveI := IsRegular.finite_syntacticMonoid h
  inferInstance

theorem IsRegular.of_finite_syntacticSemigroup (h : Finite L.SyntacticSemigroup) : L.IsRegular :=
  IsRegular.of_finite_syntacticMonoid L.finite_syntacticMonoid_of_finite_syntacticSemigroup

/-- `L` is regular iff `L.SyntacticSemigroup` is finite. -/
theorem isRegular_iff_finite_syntacticSemigroup :
    L.IsRegular ↔ Finite L.SyntacticSemigroup :=
  ⟨IsRegular.finite_syntacticSemigroup, IsRegular.of_finite_syntacticSemigroup⟩

/-! ### Boolean combinations -/

theorem syntacticSemigroupCon_compl : Lᶜ.syntacticSemigroupCon = L.syntacticSemigroupCon := by
  rw [syntacticSemigroupCon_eq_comap, syntacticSemigroupCon_eq_comap, syntacticCon_compl]

theorem inf_syntacticSemigroupCon_le_syntacticSemigroupCon_inf {L' : Language α} :
    L.syntacticSemigroupCon ⊓ L'.syntacticSemigroupCon ≤ (L ⊓ L').syntacticSemigroupCon := by
  rw [syntacticSemigroupCon_eq_comap, syntacticSemigroupCon_eq_comap,
    syntacticSemigroupCon_eq_comap]
  exact fun {_ _} h => inf_syntacticCon_le_syntacticCon_inf h

theorem ker_prod_toSyntacticSemigroup {L' : Language α} :
    Con.ker (L.toSyntacticSemigroup.prod L'.toSyntacticSemigroup) =
      L.syntacticSemigroupCon ⊓ L'.syntacticSemigroupCon := by
  rw [Con.ker_prodMulHom, ker_toSyntacticSemigroup, ker_toSyntacticSemigroup]

/-! ### Quotients -/

theorem syntacticSemigroupCon_le_leftQuotient (L : Language α) (u : List α) :
    L.syntacticSemigroupCon ≤ (L.leftQuotient u).syntacticSemigroupCon := by
  rw [syntacticSemigroupCon_eq_comap, syntacticSemigroupCon_eq_comap]
  exact fun {_ _} h => L.syntacticCon_le_leftQuotient u h

theorem syntacticSemigroupCon_le_rightQuotient (L : Language α) (u : List α) :
    L.syntacticSemigroupCon ≤ (L.rightQuotient u).syntacticSemigroupCon := by
  rw [syntacticSemigroupCon_eq_comap, syntacticSemigroupCon_eq_comap]
  exact fun {_ _} h => L.syntacticCon_le_rightQuotient u h

/-- The syntactic congruence on nonempty words depends on `L` only through its nonempty words. -/
theorem syntacticSemigroupCon_congr {L' : Language α}
    (h : ∀ w : List α, w ≠ [] → (w ∈ L ↔ w ∈ L')) :
    L.syntacticSemigroupCon = L'.syntacticSemigroupCon :=
  Con.ext fun u v => forall_congr' fun x => forall_congr' fun y =>
    iff_congr (h _ (by simp)) (h _ (by simp))

/-- Adjoining the empty word leaves the syntactic congruence unchanged, since it quantifies only
over nonempty words. This is the `+`-variety semantics ([eilenberg-1976] indexes varieties of sets
on `Σ⁺`): no pseudovariety of semigroups distinguishes `L` from `insert [] L`. -/
theorem syntacticSemigroupCon_insert_nil :
    (insert [] L).syntacticSemigroupCon = L.syntacticSemigroupCon :=
  syntacticSemigroupCon_congr fun _ hw => Set.mem_insert_iff.trans (or_iff_right hw)

/-! ### Recognition by a semigroup -/

/-- `η` *recognizes* `L` when membership of a nonempty word is decided by its image. Recognition
of the empty word is delegated to the unitization (`recognizesSemigroup_iff_recognizes`). -/
def RecognizesSemigroup {T : Type*} [Semigroup T] (η : FreeSemigroup α →ₙ* T)
    (L : Language α) : Prop :=
  ∃ P : Set T, ∀ w : FreeSemigroup α, w.toList ∈ L ↔ η w ∈ P

section

variable {T : Type*} [Semigroup T] {η : FreeSemigroup α →ₙ* T}

theorem mapMulHom_comp_equivWithOneFreeSemigroup_toFreeMonoid (u : FreeSemigroup α) :
    ((WithOne.mapMulHom η).comp FreeMonoid.equivWithOneFreeSemigroup.toMonoidHom)
      (FreeSemigroup.toFreeMonoid u) = ↑(η u) := by
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    FreeMonoid.equivWithOneFreeSemigroup_toFreeMonoid, WithOne.mapMulHom_coe]

/-- **Recognition by a semigroup is recognition by its unitization**: `η` and
`WithOne.mapMulHom η`, read on `FreeMonoid α` through `FreeMonoid.equivWithOneFreeSemigroup`,
recognize the same languages — Eilenberg's `M_A = S_A ∪ {1}` at the recognition level. -/
theorem recognizesSemigroup_iff_recognizes :
    L.RecognizesSemigroup η ↔
      Recognizes ((WithOne.mapMulHom η).comp
        FreeMonoid.equivWithOneFreeSemigroup.toMonoidHom) L := by
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨(↑) '' P ∪ {x | x = 1 ∧ [] ∈ L}, Set.ext fun w => ?_⟩
    show w ∈ L ↔ ((WithOne.mapMulHom η).comp
        FreeMonoid.equivWithOneFreeSemigroup.toMonoidHom) (FreeMonoid.ofList w) ∈
      (↑) '' P ∪ {x | x = 1 ∧ [] ∈ L}
    rcases w with _ | ⟨c, l⟩
    · rw [show FreeMonoid.ofList ([] : List α) = 1 from rfl, map_one]
      simp
    · rw [show FreeMonoid.ofList (c :: l) = FreeSemigroup.toFreeMonoid ⟨c, l⟩ by
          rw [FreeSemigroup.toFreeMonoid_eq_ofList, FreeSemigroup.toList_mk],
        mapMulHom_comp_equivWithOneFreeSemigroup_toFreeMonoid]
      simpa using hP ⟨c, l⟩
  · rintro ⟨S, hS⟩
    have hmem : ∀ v : List α, v ∈ L ↔ ((WithOne.mapMulHom η).comp
        FreeMonoid.equivWithOneFreeSemigroup.toMonoidHom) (FreeMonoid.ofList v) ∈ S :=
      fun v => by rw [hS]; rfl
    refine ⟨(↑) ⁻¹' S, fun w => (hmem w.toList).trans ?_⟩
    rw [← FreeSemigroup.toFreeMonoid_eq_ofList,
      mapMulHom_comp_equivWithOneFreeSemigroup_toFreeMonoid]
    rfl

theorem ker_le_syntacticSemigroupCon_of_recognizes (hrec : L.RecognizesSemigroup η) :
    Con.ker η ≤ L.syntacticSemigroupCon := by
  rw [syntacticSemigroupCon_eq_comap]
  intro u v huv
  exact ker_le_syntacticCon_of_recognizes (recognizesSemigroup_iff_recognizes.mp hrec)
    (Con.ker_apply.mpr (by
      rw [mapMulHom_comp_equivWithOneFreeSemigroup_toFreeMonoid,
        mapMulHom_comp_equivWithOneFreeSemigroup_toFreeMonoid, (Con.ker_rel η).mp huv]))

theorem recognizesSemigroup_of_ker_le (h : Con.ker η ≤ L.syntacticSemigroupCon) :
    L.RecognizesSemigroup η :=
  ⟨η '' {u | u.toList ∈ L}, fun w =>
    ⟨fun hw => ⟨w, hw, rfl⟩, fun ⟨_, hu, hη⟩ =>
      (SyntacticEquiv.mem_iff (h ((Con.ker_rel η).mpr hη))).mp hu⟩⟩

theorem recognizesSemigroup_iff_ker_le :
    L.RecognizesSemigroup η ↔ Con.ker η ≤ L.syntacticSemigroupCon :=
  ⟨ker_le_syntacticSemigroupCon_of_recognizes, recognizesSemigroup_of_ker_le⟩

end

theorem recognizesSemigroup_toSyntacticSemigroup (L : Language α) :
    L.RecognizesSemigroup L.toSyntacticSemigroup :=
  recognizesSemigroup_of_ker_le L.ker_toSyntacticSemigroup.le

end Language
