/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.SyntacticMonoid`, extending
`Mathlib.Computability.MyhillNerode`'s residual program to the two-sided
congruence.
-/
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Finite.Range
import Linglib.Core.Computability.TransitionMonoid

/-!
# The syntactic monoid of a language

The *syntactic monoid* of a language `L : Language α` is the quotient of the free monoid
`FreeMonoid α` by the *syntactic congruence*: two words are identified when no two-sided context
distinguishes them as `L`-members, `∀ x y, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L`.

It is the coarsest congruence saturating `L`, so every recognizing homomorphism factors through it,
and it is finite exactly when `L` is regular. This is the two-sided refinement of the one-sided
right-Nerode quotient `Language.leftQuotient`, carrying a monoid structure rather than a bare set
of states.

## Main definitions

- `Language.syntacticCon`: the syntactic congruence, two-sided context equivalence
- `Language.syntacticMonoid`: the quotient monoid `(syntacticCon L).Quotient`
- `Language.toSyntacticMonoid`: the projection `FreeMonoid α →* L.syntacticMonoid`
- `Language.syntacticClass`: the syntactic class of a word
- `Language.Recognizes`: `φ` recognizes `L`, i.e. `L` is a union of `φ`-fibres

## Main theorems

- `Language.recognizes_iff_ker_le_syntacticCon`: the syntactic congruence is the coarsest
  congruence saturating `L` — a hom recognizes `L` exactly when its kernel refines it
- `Language.syntacticCon_eq_ker_transitionHom`: the intrinsic congruence is the kernel of the
  transition action of `L.toDFA`
- `Language.isRegular_iff_finite_syntacticMonoid`: the Myhill–Nerode theorem in monoid form

## References

* [pin-mfa]
-/

namespace Language

variable {α : Type*} (L : Language α)

/-! ### The syntactic congruence and monoid -/

/-- Two words are **syntactically equivalent** for `L` when no two-sided context distinguishes
them as `L`-members. -/
def SyntacticEquiv (u v : List α) : Prop := ∀ x y : List α, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L

section

variable {L} {u u' v v' w : List α}

theorem mem_iff_of_syntacticEquiv (h : L.SyntacticEquiv u v) : u ∈ L ↔ v ∈ L := by
  simpa using h [] []

@[refl] theorem SyntacticEquiv.refl (u : List α) : L.SyntacticEquiv u u := fun _ _ => Iff.rfl

@[symm] theorem SyntacticEquiv.symm (h : L.SyntacticEquiv u v) : L.SyntacticEquiv v u :=
  fun x y => (h x y).symm

@[trans] theorem SyntacticEquiv.trans (h : L.SyntacticEquiv u v) (h' : L.SyntacticEquiv v w) :
    L.SyntacticEquiv u w := fun x y => (h x y).trans (h' x y)

theorem SyntacticEquiv.append (h : L.SyntacticEquiv u u') (h' : L.SyntacticEquiv v v') :
    L.SyntacticEquiv (u ++ v) (u' ++ v') := by grind [SyntacticEquiv]

theorem SyntacticEquiv.compl_iff : Lᶜ.SyntacticEquiv u v ↔ L.SyntacticEquiv u v :=
  forall_congr' fun _ => forall_congr' fun _ => not_iff_not

theorem SyntacticEquiv.reverse_iff :
    L.reverse.SyntacticEquiv u v ↔ L.SyntacticEquiv u.reverse v.reverse := by
  refine ⟨fun h x y => ?_, fun h x y => ?_⟩ <;> simpa using h y.reverse x.reverse

end

section

variable {u v : FreeMonoid α}

/-- The *syntactic congruence* of `L` identifies two words when no two-sided context distinguishes
them as `L`-members. -/
def syntacticCon : Con (FreeMonoid α) where
  r u v := L.SyntacticEquiv u.toList v.toList
  iseqv := ⟨fun _ => .refl _, .symm, .trans⟩
  mul' hab hcd := hab.append hcd

theorem syntacticCon_iff :
    L.syntacticCon u v ↔ ∀ x y, x ++ u.toList ++ y ∈ L ↔ x ++ v.toList ++ y ∈ L :=
  Iff.rfl

/-- The *syntactic monoid* of `L` is the quotient of `FreeMonoid α` by the syntactic congruence. -/
abbrev syntacticMonoid : Type _ := (syntacticCon L).Quotient

/-- The *syntactic morphism* of `L` projects `FreeMonoid α` onto the syntactic monoid. -/
def toSyntacticMonoid : FreeMonoid α →* L.syntacticMonoid := (syntacticCon L).mk'

theorem toSyntacticMonoid_eq_iff :
    L.toSyntacticMonoid u = L.toSyntacticMonoid v ↔ L.syntacticCon u v :=
  Con.eq _

end

/-! ### The syntactic class of a word -/

/-- The *syntactic class* of a word `w` is its image in the syntactic monoid. -/
def syntacticClass (w : List α) : L.syntacticMonoid := L.toSyntacticMonoid (FreeMonoid.ofList w)

@[simp] theorem syntacticClass_nil : L.syntacticClass [] = 1 := map_one _

@[simp] theorem syntacticClass_append (u v : List α) :
    L.syntacticClass (u ++ v) = L.syntacticClass u * L.syntacticClass v := map_mul _ _ _

theorem syntacticClass_surjective : Function.Surjective L.syntacticClass :=
  Con.mk'_surjective.comp FreeMonoid.ofList.surjective

variable {L} {u v : List α}

theorem syntacticClass_eq_iff : L.syntacticClass u = L.syntacticClass v ↔ L.SyntacticEquiv u v :=
  L.toSyntacticMonoid_eq_iff

theorem mem_iff_of_syntacticClass_eq (h : L.syntacticClass u = L.syntacticClass v) :
    u ∈ L ↔ v ∈ L := mem_iff_of_syntacticEquiv (syntacticClass_eq_iff.mp h)

/-- **Reverse duality**: a syntactic-class equality in `L.reverse` is the reversed-word equality
in `L`. -/
theorem syntacticClass_reverse_eq_iff :
    L.reverse.syntacticClass u = L.reverse.syntacticClass v ↔
      L.syntacticClass u.reverse = L.syntacticClass v.reverse :=
  syntacticClass_eq_iff.trans (SyntacticEquiv.reverse_iff.trans syntacticClass_eq_iff.symm)

/-! ### Universal property -/

/-- `φ` *recognizes* `L` when `L` is a union of `φ`-fibres. -/
def Recognizes {M : Type*} [Monoid M] (φ : FreeMonoid α →* M) (L : Language α) : Prop :=
  ∃ S : Set M, L = φ ⁻¹' S

section

variable {M : Type*} [Monoid M] {φ : FreeMonoid α →* M}

theorem ker_le_syntacticCon_of_recognizes (hrec : Recognizes φ L) :
    Con.ker φ ≤ syntacticCon L := by
  obtain ⟨S, rfl⟩ := hrec
  intro u v huv
  change ∀ x y : FreeMonoid α, x * u * y ∈ φ ⁻¹' S ↔ x * v * y ∈ φ ⁻¹' S
  simp [Con.ker_apply.mp huv]

theorem recognizes_of_ker_le_syntacticCon (h : Con.ker φ ≤ syntacticCon L) :
    Recognizes φ L :=
  ⟨φ '' L, (Set.subset_preimage_image φ L).antisymm
    fun _ ⟨_, hu, hφ⟩ => (mem_iff_of_syntacticEquiv (h (Con.ker_apply.mpr hφ))).mp hu⟩

theorem recognizes_iff_ker_le_syntacticCon :
    Recognizes φ L ↔ Con.ker φ ≤ syntacticCon L :=
  ⟨ker_le_syntacticCon_of_recognizes, recognizes_of_ker_le_syntacticCon⟩

end

theorem recognizes_toSyntacticMonoid : Recognizes L.toSyntacticMonoid L :=
  recognizes_of_ker_le_syntacticCon (Con.mk'_ker _).le

/-! ### Connection to the minimal DFA -/

/-- A DFA's transition action recognizes the language it accepts. -/
theorem recognizes_transitionHom {σ : Type*} (M : DFA α σ) :
    Recognizes M.transitionHom M.accepts :=
  ⟨{t | t.unop M.start ∈ M.accept}, rfl⟩

@[simp] theorem evalFrom_toDFA (s : Set.range L.leftQuotient) (w : List α) :
    (L.toDFA.evalFrom s w).val = s.val.leftQuotient w := by
  induction w using List.reverseRecOn <;> simp_all [leftQuotient_append]

/-- The intrinsic syntactic congruence is the kernel of the minimal DFA's transition action. -/
theorem syntacticCon_eq_ker_transitionHom : L.syntacticCon = Con.ker L.toDFA.transitionHom := by
  refine le_antisymm ?_ (by simpa using
    ker_le_syntacticCon_of_recognizes (recognizes_transitionHom L.toDFA))
  intro u v h
  refine L.toDFA.transitionHom_eq_iff.mpr fun s => ?_
  obtain ⟨x, hx⟩ := s.2
  simp only [Subtype.ext_iff, evalFrom_toDFA, ← hx, ← leftQuotient_append]
  exact Set.ext (h x)

/-! ### Myhill–Nerode -/

theorem IsRegular.finite_syntacticMonoid (h : L.IsRegular) : Finite L.syntacticMonoid := by
  haveI := h.finite_range_leftQuotient.to_subtype
  show Finite (syntacticCon L).Quotient
  rw [syntacticCon_eq_ker_transitionHom]
  exact Finite.of_equiv _ (DFA.transitionMonoidEquiv L.toDFA).symm.toEquiv

theorem IsRegular.of_finite_syntacticMonoid (h : Finite L.syntacticMonoid) : L.IsRegular := by
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  let g : L.syntacticMonoid → Language α :=
    Quot.lift (fun w => L.leftQuotient w.toList) fun _ _ huv => Set.ext (huv [])
  exact (Set.finite_range g).subset fun _ ⟨x, hx⟩ => ⟨Quot.mk _ (FreeMonoid.ofList x), hx⟩

/-- **Myhill–Nerode**, syntactic-monoid form: `L` is regular iff `L.syntacticMonoid` is finite. -/
theorem isRegular_iff_finite_syntacticMonoid : L.IsRegular ↔ Finite L.syntacticMonoid :=
  ⟨IsRegular.finite_syntacticMonoid, IsRegular.of_finite_syntacticMonoid⟩

/-! ### Complement- and intersection-invariance

Generic syntactic-monoid facts about boolean combinations, used by any class defined through the
syntactic monoid (e.g. `Language.IsStarFree`, and `Monoid.Pseudovariety.langs` in general). -/

/-- The syntactic congruence is complement-invariant: a two-sided context distinguishes `u` from
`v` for `L` exactly when it does for `Lᶜ`. -/
theorem syntacticCon_compl (L : Language α) : Lᶜ.syntacticCon = L.syntacticCon :=
  Con.ext fun _ _ => SyntacticEquiv.compl_iff

/-- The meet of the two syntactic congruences refines that of the intersection: if no `L`-context
and no `M`-context distinguishes `u` from `v`, then no `(L ⊓ M)`-context does either. -/
theorem inf_syntacticCon_le_syntacticCon_inf (L M : Language α) :
    L.syntacticCon ⊓ M.syntacticCon ≤ (L ⊓ M).syntacticCon :=
  fun {_ _} huv x y => and_congr (huv.1 x y) (huv.2 x y)

/-- The kernel of the pairing of the two syntactic morphisms is exactly the meet of the two
syntactic congruences (a word's class in the product is the pair of its classes). -/
theorem ker_prod_toSyntacticMonoid (L M : Language α) :
    Con.ker (L.toSyntacticMonoid.prod M.toSyntacticMonoid) =
      L.syntacticCon ⊓ M.syntacticCon :=
  Con.ext fun _ _ => by simp [Prod.ext_iff, toSyntacticMonoid_eq_iff, Con.inf_iff_and]

/-- The **right quotient** `L u⁻¹` is the set of words that land in `L` when `u` is appended. The
left quotient is mathlib's `Language.leftQuotient`. -/
def rightQuotient (L : Language α) (u : List α) : Language α := {w | w ++ u ∈ L}

@[simp] theorem mem_rightQuotient {L : Language α} {u w : List α} :
    w ∈ L.rightQuotient u ↔ w ++ u ∈ L := Iff.rfl

end Language
