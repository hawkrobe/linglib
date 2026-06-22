/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Range
import Mathlib.GroupTheory.Congruence.Hom

/-!
# The syntactic monoid of a language

The *syntactic monoid* of a language `L : Language α` is the quotient of the free monoid
`FreeMonoid α` by the *syntactic congruence*: two words are identified when no two-sided context
distinguishes them as `L`-members, `∀ x y, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L`.

This is the two-sided, monoid-valued refinement of `Mathlib.Computability.MyhillNerode`, which
builds the one-sided right-Nerode quotient (`Language.leftQuotient`) and proves regularity ↔
finitely many left quotients. The syntactic monoid carries a *monoid* structure rather than just a
set of states, and its Myhill–Nerode theorem reads `L.IsRegular ↔ Finite L.syntacticMonoid`.

## Main definitions

* `Language.SyntacticEquiv L u v`: the two-sided context equivalence on words.
* `Language.syntacticCon L : Con (FreeMonoid α)`: the syntactic congruence.
* `Language.syntacticMonoid L`: the quotient monoid `(syntacticCon L).Quotient`.
* `Language.toSyntacticMonoid L`: the projection `FreeMonoid α →* L.syntacticMonoid`.
* `Language.Recognises φ L`: `φ` recognises `L`, i.e. `L` is a union of `φ`-fibres.

## Main results

* `Language.mem_iff_of_syntacticEquiv`: `L` is saturated by the syntactic congruence.
* `Language.ker_le_syntacticCon_of_recognises`: the syntactic congruence is the coarsest congruence
  recognising `L`, so every recognising hom factors through `toSyntacticMonoid` via `Con.lift`.
* `Language.isRegular_iff_finite_syntacticMonoid`: the Myhill–Nerode theorem in monoid form.

## Implementation notes

`FreeMonoid α` is definitionally `List α`, but the elaborator does not unfold the `def`.
`SyntacticEquiv` is stated on `List α` so that `++` and `Language.leftQuotient` apply directly; the
`Con` packaging reuses it through the definitional equality, bridging `*` on `FreeMonoid` to `++` on
`List` via `FreeMonoid.toList` (an `Equiv.refl`).

## References

* Myhill (1957), Nerode (1958)
* Pin, *Mathematical Foundations of Automata Theory*, Chapter I
* <https://en.wikipedia.org/wiki/Syntactic_monoid>
-/

namespace Language

variable {α : Type*} {L : Language α}

/-! ### Syntactic equivalence on words -/

variable (L) in
/-- Two words are *syntactically equivalent* w.r.t. `L` when no two-sided context distinguishes
them: the largest left- and right-concatenation-stable equivalence contained in `(· ∈ L)`. -/
def SyntacticEquiv (u v : List α) : Prop :=
  ∀ x y : List α, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L

namespace SyntacticEquiv

variable {u v w : List α}

@[refl] protected theorem refl (u : List α) : SyntacticEquiv L u u := fun _ _ => Iff.rfl

@[symm] protected theorem symm (h : SyntacticEquiv L u v) : SyntacticEquiv L v u :=
  fun x y => (h x y).symm

@[trans] protected theorem trans (h₁ : SyntacticEquiv L u v) (h₂ : SyntacticEquiv L v w) :
    SyntacticEquiv L u w := fun x y => (h₁ x y).trans (h₂ x y)

/-- Specialising the two-sided test to `x = []` shows that syntactic equivalence refines the
right-Nerode equivalence: equivalent words have the same `Language.leftQuotient`. -/
theorem leftQuotient_eq (h : SyntacticEquiv L u v) : L.leftQuotient u = L.leftQuotient v := by
  ext y; simpa using h [] y

end SyntacticEquiv

/-! ### The syntactic congruence and monoid -/

variable (L) in
/-- The *syntactic congruence* of `L`: syntactic equivalence upgraded with closure under two-sided
concatenation. The `mul'` proof reassociates the context with `List.append_assoc`; `FreeMonoid.toList`
(an `Equiv.refl`) bridges `*` on `FreeMonoid` to `++` on `List`. -/
def syntacticCon : Con (FreeMonoid α) where
  toSetoid := ⟨SyntacticEquiv L, SyntacticEquiv.refl, SyntacticEquiv.symm, SyntacticEquiv.trans⟩
  mul' := by
    intro w x y z hwx hyz a b
    show a ++ (FreeMonoid.toList w ++ FreeMonoid.toList y) ++ b ∈ L ↔
         a ++ (FreeMonoid.toList x ++ FreeMonoid.toList z) ++ b ∈ L
    have h₁ := hwx a (FreeMonoid.toList y ++ b)
    have h₂ := hyz (a ++ FreeMonoid.toList x) b
    simp only [List.append_assoc] at h₁ h₂ ⊢
    exact h₁.trans h₂

variable (L) in
/-- The *syntactic monoid* of `L`: the quotient of `FreeMonoid α` by the syntactic congruence. An
`abbrev` so that `Monoid` instance search resolves through `Con.Quotient`. -/
abbrev syntacticMonoid : Type _ := (syntacticCon L).Quotient

variable (L) in
/-- The canonical projection sending each word to its syntactic class; the underlying `Con.mk'`. -/
def toSyntacticMonoid : FreeMonoid α →* L.syntacticMonoid := (syntacticCon L).mk'

/-- **`L` is saturated by the syntactic congruence**: equivalent words are equi-members. This is the
defining property — `syntacticCon L` is the coarsest congruence on `FreeMonoid α` for which `L` is a
union of classes. -/
theorem mem_iff_of_syntacticEquiv {u v : List α} (h : SyntacticEquiv L u v) : u ∈ L ↔ v ∈ L := by
  simpa using h [] []

/-! ### Universal property -/

/-- A monoid hom `φ : FreeMonoid α →* M` *recognises* `L` when `L` is a union of `φ`-fibres, i.e.
`L = φ ⁻¹' S` for some `S ⊆ M` (Pin, Chapter I). -/
def Recognises {M : Type*} [Monoid M] (φ : FreeMonoid α →* M) (L : Language α) : Prop :=
  ∃ S : Set M, L = φ ⁻¹' S

/-- **Universal property** (kernel form): the kernel of any `L`-recognising hom is contained in the
syntactic congruence, so `syntacticCon L` is the coarsest congruence recognising `L`. Composing with
`Con.lift` gives the factorisation `(syntacticCon L).lift φ (ker_le_syntacticCon_of_recognises h)`. -/
theorem ker_le_syntacticCon_of_recognises {M : Type*} [Monoid M] {φ : FreeMonoid α →* M}
    (hrec : Recognises φ L) : Con.ker φ ≤ syntacticCon L := by
  obtain ⟨S, hS⟩ := hrec
  intro u v huv
  change ∀ x y : FreeMonoid α, x * u * y ∈ L ↔ x * v * y ∈ L
  intro x y
  have step : ∀ w : FreeMonoid α, w ∈ L ↔ φ w ∈ S := fun w => by rw [hS]; rfl
  simp only [step, map_mul, show φ u = φ v from huv]

/-! ### Regularity implies a finite syntactic monoid -/

/-- **Myhill, forward direction**: a regular language has a finite syntactic monoid. The right action
`[u] ↦ (Q ↦ Q.leftQuotient u)` injects `syntacticMonoid L` into the finite function space `LQ → LQ`,
where `LQ = Set.range L.leftQuotient` is finite by `IsRegular.finite_range_leftQuotient`. -/
theorem IsRegular.finite_syntacticMonoid (h : L.IsRegular) : Finite L.syntacticMonoid := by
  classical
  set LQ : Set (Language α) := Set.range L.leftQuotient
  haveI : Finite LQ := h.finite_range_leftQuotient.to_subtype
  let action : FreeMonoid α → (LQ → LQ) := fun u Q =>
    ⟨Q.val.leftQuotient (FreeMonoid.toList u), by
      obtain ⟨x, hx⟩ := Q.prop
      exact ⟨x ++ FreeMonoid.toList u, by rw [← hx, ← Language.leftQuotient_append]⟩⟩
  have action_well_defined :
      ∀ u v : FreeMonoid α, SyntacticEquiv L u v → action u = action v := by
    intro u v huv
    funext Q
    obtain ⟨x, hx⟩ := Q.prop
    refine Subtype.ext ?_
    show Q.val.leftQuotient (FreeMonoid.toList u) = Q.val.leftQuotient (FreeMonoid.toList v)
    rw [← hx, ← Language.leftQuotient_append, ← Language.leftQuotient_append]
    refine SyntacticEquiv.leftQuotient_eq fun a b => ?_
    have := huv (a ++ x) b
    simp only [List.append_assoc] at this ⊢
    exact this
  let phi : L.syntacticMonoid → (LQ → LQ) := fun cls => Con.liftOn cls action action_well_defined
  have phi_inj : Function.Injective phi := by
    rintro ⟨u⟩ ⟨v⟩ huv
    apply Quotient.sound
    intro a b
    -- Reading off the action at `Q := L.leftQuotient a` equates the two left quotients.
    have key : L.leftQuotient (a ++ FreeMonoid.toList u) =
        L.leftQuotient (a ++ FreeMonoid.toList v) := by
      rw [Language.leftQuotient_append, Language.leftQuotient_append]
      exact congr_arg Subtype.val (congr_fun huv ⟨L.leftQuotient a, a, rfl⟩)
    show b ∈ L.leftQuotient (a ++ FreeMonoid.toList u) ↔
         b ∈ L.leftQuotient (a ++ FreeMonoid.toList v)
    rw [key]
  exact Finite.of_injective phi phi_inj

/-! ### A finite syntactic monoid implies regularity -/

/-- **Myhill, reverse direction**: a language with finite syntactic monoid is regular. The map
`[u] ↦ L.leftQuotient u` is well-defined on classes (by `SyntacticEquiv.leftQuotient_eq`) and
surjects onto `Set.range L.leftQuotient`, so the latter is finite; close via
`IsRegular.of_finite_range_leftQuotient`. -/
theorem IsRegular.of_finite_syntacticMonoid [Finite L.syntacticMonoid] : L.IsRegular := by
  apply Language.IsRegular.of_finite_range_leftQuotient
  let f : L.syntacticMonoid → Language α := fun cls =>
    Con.liftOn cls L.leftQuotient fun _ _ huv => SyntacticEquiv.leftQuotient_eq huv
  have hrange : Set.range L.leftQuotient = Set.range f := by
    ext L'
    refine ⟨fun ⟨u, hu⟩ => ⟨(syntacticCon L).toQuotient u, hu⟩, ?_⟩
    rintro ⟨cls, hcls⟩
    induction cls using Con.induction_on with
    | _ u => exact ⟨u, hcls⟩
  rw [hrange]
  exact Set.finite_range f

/-- **Myhill–Nerode theorem (syntactic-monoid form)**: a language is regular iff its syntactic
monoid is finite. -/
theorem isRegular_iff_finite_syntacticMonoid : L.IsRegular ↔ Finite L.syntacticMonoid :=
  ⟨IsRegular.finite_syntacticMonoid, fun _ => IsRegular.of_finite_syntacticMonoid⟩

end Language
