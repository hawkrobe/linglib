/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.SyntacticSemigroup`.
-/
import Linglib.Core.Algebra.Free
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.GroupTheory.Congruence.Hom
import Mathlib.Data.Fintype.Option

/-!
# The syntactic semigroup of a language

The *syntactic semigroup* of `L : Language α` is the quotient of the free semigroup `FreeSemigroup
α` — the nonempty words — by the syntactic congruence. It is the same congruence as
`Language.syntacticCon`, read on `FreeSemigroup α` instead of `FreeMonoid α`; the two quotients are
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

## Main theorems

- `Language.syntacticSemigroupToMonoid_injective`: the syntactic semigroup embeds in the
  syntactic monoid
- `Language.isRegular_iff_finite_syntacticSemigroup`: Myhill–Nerode in semigroup form
- `Language.recognizesSemigroup_iff_ker_le`: the syntactic congruence is the coarsest one
  recognizing `L`
- `Language.syntacticSemigroupCon_insert_nil`: the syntactic semigroup does not see the empty
  word

## Implementation notes

The projection is `Con.mkMulHom`, mathlib's `MulHom`-valued quotient map for a `Con` over a plain
`Mul` (the monoid-valued `Con.mk'` would not apply).

Words are carried to `List α` by `FreeSemigroup.toList` from `Linglib.Core.Algebra.Free`, which is
structural (`head :: tail`). Mathlib's `FreeSemigroup.toFreeMonoid` is the same map bundled as a
`→ₙ*`, but built by the universal property, so the two are equal only propositionally
(`FreeSemigroup.toFreeMonoid_mk_eq_cons`); adopting it would replace this file's `rfl` proofs with
rewrites.
-/

namespace Language

variable {α : Type*} (L : Language α)

/-- The **syntactic congruence** on the free semigroup: the syntactic equivalence of the
underlying nonempty words. -/
def syntacticSemigroupCon : Con (FreeSemigroup α) where
  r u v := L.SyntacticEquiv u.toList v.toList
  iseqv := ⟨fun _ => .refl _, .symm, .trans⟩
  mul' hab hcd := hab.append hcd

section

variable {u v : FreeSemigroup α}

theorem syntacticSemigroupCon_iff :
    L.syntacticSemigroupCon u v ↔ L.SyntacticEquiv u.toList v.toList := Iff.rfl

/-- The **syntactic semigroup** of `L`: the quotient of `FreeSemigroup α` by the syntactic
congruence. -/
abbrev SyntacticSemigroup := (syntacticSemigroupCon L).Quotient

/-- The *syntactic morphism* of `L` projects `FreeSemigroup α` onto the syntactic semigroup. -/
def toSyntacticSemigroup : FreeSemigroup α →ₙ* L.SyntacticSemigroup :=
  Con.mkMulHom (syntacticSemigroupCon L)

theorem toSyntacticSemigroup_eq_iff :
    L.toSyntacticSemigroup u = L.toSyntacticSemigroup v ↔ L.syntacticSemigroupCon u v :=
  Con.eq _

end

theorem toSyntacticSemigroup_surjective : Function.Surjective L.toSyntacticSemigroup :=
  Con.mkMulHom_surjective _

theorem ker_toSyntacticSemigroup : Con.ker L.toSyntacticSemigroup = L.syntacticSemigroupCon :=
  Con.ker_mkMulHom_eq _

/-! ### Relation to the syntactic monoid -/

/-- The syntactic semigroup embeds into the syntactic monoid: a nonempty word is sent to its
class in the monoid. It is injective because both quotients are by the same context relation. -/
def syntacticSemigroupToMonoid : L.SyntacticSemigroup →ₙ* L.SyntacticMonoid where
  toFun := Quotient.lift (fun u : FreeSemigroup α => L.syntacticClass u.toList)
    fun _ _ h => syntacticClass_eq_iff.mpr h
  map_mul' := by rintro ⟨u⟩ ⟨v⟩; exact L.syntacticClass_append u.toList v.toList

@[simp] theorem syntacticSemigroupToMonoid_apply (u : FreeSemigroup α) :
    L.syntacticSemigroupToMonoid (L.toSyntacticSemigroup u) = L.syntacticClass u.toList := rfl

theorem syntacticSemigroupToMonoid_injective :
    Function.Injective L.syntacticSemigroupToMonoid := by
  rintro ⟨u⟩ ⟨v⟩ h
  exact Quotient.sound (syntacticClass_eq_iff.mp h)

instance instFiniteSyntacticSemigroup [Finite L.SyntacticMonoid] :
    Finite L.SyntacticSemigroup :=
  .of_injective _ L.syntacticSemigroupToMonoid_injective

/-- Conversely, a finite syntactic semigroup forces a finite syntactic monoid: the monoid is
covered by the semigroup together with the identity, which is Eilenberg's `M_A = S_A ∪ {1}`. -/
theorem finite_syntacticMonoid_of_finite_syntacticSemigroup [Finite L.SyntacticSemigroup] :
    Finite L.SyntacticMonoid := by
  refine .of_surjective (β := L.SyntacticMonoid)
    (Option.elim · 1 L.syntacticSemigroupToMonoid) fun m => ?_
  obtain ⟨w, rfl⟩ := L.syntacticClass_surjective m
  match w with
  | [] => exact ⟨none, L.syntacticClass_nil.symm⟩
  | c :: w => exact ⟨some (L.toSyntacticSemigroup ⟨c, w⟩), rfl⟩

/-! ### Myhill–Nerode -/

section

variable {L}

theorem IsRegular.finite_syntacticSemigroup (h : L.IsRegular) : Finite L.SyntacticSemigroup :=
  haveI := IsRegular.finite_syntacticMonoid h
  inferInstance

theorem IsRegular.of_finite_syntacticSemigroup (h : Finite L.SyntacticSemigroup) : L.IsRegular :=
  IsRegular.of_finite_syntacticMonoid L.finite_syntacticMonoid_of_finite_syntacticSemigroup

/-- `L` is regular iff `L.SyntacticSemigroup` is finite. -/
theorem isRegular_iff_finite_syntacticSemigroup :
    L.IsRegular ↔ Finite L.SyntacticSemigroup :=
  ⟨IsRegular.finite_syntacticSemigroup, IsRegular.of_finite_syntacticSemigroup⟩

end

/-! ### Boolean combinations -/

theorem syntacticSemigroupCon_compl : Lᶜ.syntacticSemigroupCon = L.syntacticSemigroupCon :=
  Con.ext fun _ _ => SyntacticEquiv.compl_iff

section

variable (L L' : Language α)

theorem inf_syntacticSemigroupCon_le_syntacticSemigroupCon_inf :
    L.syntacticSemigroupCon ⊓ L'.syntacticSemigroupCon ≤ (L ⊓ L').syntacticSemigroupCon :=
  fun {_ _} huv x y => and_congr (huv.1 x y) (huv.2 x y)

theorem ker_prod_toSyntacticSemigroup :
    Con.ker (L.toSyntacticSemigroup.prod L'.toSyntacticSemigroup) =
      L.syntacticSemigroupCon ⊓ L'.syntacticSemigroupCon := by
  rw [Con.ker_prodMulHom, ker_toSyntacticSemigroup, ker_toSyntacticSemigroup]

end

/-! ### Quotients -/

/-- Syntactic equivalence for `L` implies it for any left quotient of `L`: prepend `u` to the
left context. -/
theorem syntacticSemigroupCon_le_leftQuotient (u : List α) :
    L.syntacticSemigroupCon ≤ (L.leftQuotient u).syntacticSemigroupCon := fun {p q} h x y => by
  simpa [List.append_assoc] using h (u ++ x) y

/-- Syntactic equivalence for `L` implies it for any right quotient of `L`: append `u` to the
right context. -/
theorem syntacticSemigroupCon_le_rightQuotient (u : List α) :
    L.syntacticSemigroupCon ≤ (L.rightQuotient u).syntacticSemigroupCon := fun {p q} h x y => by
  simpa [List.append_assoc] using h x (y ++ u)

/-- **The syntactic semigroup does not see the empty word.** Its congruence quantifies only over
nonempty words, so adjoining `[]` to a language leaves it unchanged. This is the `+`-variety
semantics working as intended ([eilenberg-1976] indexes varieties of sets on `Σ⁺`), and it is why
no pseudovariety of semigroups can distinguish `L` from `insert [] L`. -/
theorem syntacticSemigroupCon_insert_nil :
    (insert [] L).syntacticSemigroupCon = L.syntacticSemigroupCon :=
  Con.ext fun u v => by
    have h : ∀ (x : List α) (w : FreeSemigroup α) (y : List α),
        x ++ w.toList ++ y ∈ insert [] L ↔ x ++ w.toList ++ y ∈ L := fun x w y => by
      refine (Set.mem_insert_iff).trans (or_iff_right ?_)
      intro hnil
      exact absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hnil).1).2
        (FreeSemigroup.toList_ne_nil w)
    exact forall_congr' fun x => forall_congr' fun y => iff_congr (h x u y) (h x v y)

/-! ### Recognition by a semigroup

`Language.Recognizes` pulls the fibre equation back along `FreeMonoid.ofList`; `FreeSemigroup α`
omits the empty word, so no such pullback exists and recognition is stated pointwise on nonempty
words. It says nothing about `[]` — which is right, since the syntactic semigroup does not see it
(`syntacticSemigroupCon_insert_nil`). -/

/-- `η` **recognizes** `L` when membership of a nonempty word is decided by its image. -/
def RecognizesSemigroup {T : Type*} [Semigroup T] (η : FreeSemigroup α →ₙ* T)
    (L : Language α) : Prop :=
  ∃ P : Set T, ∀ w : FreeSemigroup α, w.toList ∈ L ↔ η w ∈ P

/-- A nonempty word in a two-sided context, as an element of the free semigroup. The four cases
are needed because an empty context contributes no factor to multiply through. -/
private def ctx (x : List α) (u : FreeSemigroup α) (y : List α) : FreeSemigroup α :=
  match x, y with
  | [], [] => u
  | [], c :: y => u * ⟨c, y⟩
  | a :: x, [] => ⟨a, x⟩ * u
  | a :: x, c :: y => ⟨a, x⟩ * u * ⟨c, y⟩

private theorem toList_ctx (x : List α) (u : FreeSemigroup α) (y : List α) :
    (ctx x u y).toList = x ++ u.toList ++ y := by
  cases x <;> cases y <;> simp [ctx, FreeSemigroup.toList]

private theorem map_ctx {T : Type*} [Semigroup T] (η : FreeSemigroup α →ₙ* T)
    {u v : FreeSemigroup α} (h : η u = η v) (x y : List α) :
    η (ctx x u y) = η (ctx x v y) := by
  cases x <;> cases y <;> simp [ctx, map_mul, h]

section

variable {T : Type*} [Semigroup T] {η : FreeSemigroup α →ₙ* T}

theorem ker_le_syntacticSemigroupCon_of_recognizes (hrec : L.RecognizesSemigroup η) :
    Con.ker η ≤ L.syntacticSemigroupCon := by
  obtain ⟨P, hP⟩ := hrec
  intro u v huv x y
  rw [← toList_ctx x u y, ← toList_ctx x v y, hP, hP, map_ctx η huv]

theorem recognizesSemigroup_of_ker_le (h : Con.ker η ≤ L.syntacticSemigroupCon) :
    L.RecognizesSemigroup η :=
  ⟨η '' {u | u.toList ∈ L}, fun w =>
    ⟨fun hw => ⟨w, hw, rfl⟩, fun ⟨_, hu, hη⟩ =>
      (SyntacticEquiv.mem_iff (h ((Con.ker_rel η).mpr hη))).mp hu⟩⟩

theorem recognizesSemigroup_iff_ker_le :
    L.RecognizesSemigroup η ↔ Con.ker η ≤ L.syntacticSemigroupCon :=
  ⟨L.ker_le_syntacticSemigroupCon_of_recognizes, L.recognizesSemigroup_of_ker_le⟩

end

theorem recognizesSemigroup_toSyntacticSemigroup :
    L.RecognizesSemigroup L.toSyntacticSemigroup :=
  L.recognizesSemigroup_of_ker_le L.ker_toSyntacticSemigroup.le

end Language
