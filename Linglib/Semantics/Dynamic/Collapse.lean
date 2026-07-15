import Linglib.Semantics.Dynamic.Category
import Mathlib.CategoryTheory.Category.RelCat

/-!
# The one-object collapse
[muskens-van-benthem-visser-2011], [muskens-1996], [groenendijk-stokhof-1991]

The collapse of based dynamic semantics to level 0 — the relational
algebra of procedures over a single state space, with composition,
converse, and the diagonal ([muskens-van-benthem-visser-2011]'s "Dynamic
Constants as Operators in Relational Algebra"; mathlib's `RelCat`). The
collapse is a functor from the category of contexts to `RelCat`, sending a
context to its possibilities *up to agreement on the base* and a
transition to its `toUpdate` relation. The quotient is forced: `toUpdate` sends `𝟙 X` to
agreement-on-`X`, not to equality, so the collapse is only lawful on
base-agreement classes — `supported_left`/`supported_right` are exactly the
congruence conditions. The collapse is faithful (`Ctx.collapse_faithful`):
a transition loses nothing under it; what the collapse forgets is the
base-indexing of the objects.

This lives apart from `Category.lean` because importing `RelCat` (a type
synonym for `Type u` carrying the relations category) interferes with
instance resolution for the functions category on `Type u`, which the
state presheaf needs.

## Main declarations

* `Ctx.agreeSetoid` — `Possibility.agreeSetoid` at the context's base.
* `Ctx.collapse` — the collapse functor to `RelCat`; faithful.
-/

namespace DynamicSemantics

open CategoryTheory



namespace Ctx

variable {W M V : Type*}

/-- Agreement on the context's base: `Possibility.agreeSetoid` at `↑X.base`. -/
abbrev agreeSetoid (X : Ctx W M V) : Setoid (Possibility W V M) :=
  Possibility.agreeSetoid ↑X.base

/-- `toUpdate` descends to base-agreement classes: `supported_left` and
`supported_right` are precisely the congruence conditions. -/
def collapseRel {X Y : Ctx W M V} (u : X ⟶ Y) :
    Quotient X.agreeSetoid → Quotient Y.agreeSetoid → Prop :=
  Quotient.lift₂ (fun p q => u.t.toUpdate p q)
    fun p₁ q₁ p₂ q₂ hp hq => propext <| by
      simp only [Transition.toUpdate]
      rw [hp.1, hq.1]
      exact and_congr Iff.rfl
        ((u.t.supported_left hp.2).trans (u.t.supported_right hq.2))

@[simp] theorem collapseRel_mk {X Y : Ctx W M V} (u : X ⟶ Y)
    (p q : Possibility W V M) :
    collapseRel u (⟦p⟧) (⟦q⟧) ↔ u.t.toUpdate p q := Iff.rfl

/-- On base-agreement classes the identity transition collapses to
equality — the unitality the raw `toUpdate` lacks. -/
theorem collapseRel_id (X : Ctx W M V) (p q : Quotient X.agreeSetoid) :
    collapseRel (𝟙 X) p q ↔ p = q := by
  induction p using Quotient.ind
  induction q using Quotient.ind
  rename_i p q
  constructor
  · rintro ⟨hw, ha⟩
    exact Quotient.sound ⟨hw, ha⟩
  · intro h
    obtain ⟨hw, ha⟩ := Quotient.exact h
    exact ⟨hw, ha⟩

/-- On base-agreement classes sequencing collapses to relational
composition. -/
theorem collapseRel_comp {X Y Z : Ctx W M V} (u : X ⟶ Y) (v : Y ⟶ Z)
    (p : Quotient X.agreeSetoid) (r : Quotient Z.agreeSetoid) :
    collapseRel (u ≫ v) p r ↔
      ∃ q, collapseRel u p q ∧ collapseRel v q r := by
  induction p using Quotient.ind
  induction r using Quotient.ind
  rename_i p r
  constructor
  · intro h
    have h' : (u.t.toUpdate ⨟ v.t.toUpdate) p r := by
      rw [← Transition.toUpdate_comp, ← t_comp]
      exact h
    obtain ⟨k, hk₁, hk₂⟩ := h'
    exact ⟨(⟦k⟧), hk₁, hk₂⟩
  · rintro ⟨q, hq₁, hq₂⟩
    induction q using Quotient.ind
    rename_i k
    show (u ≫ v).t.toUpdate p r
    rw [t_comp, Transition.toUpdate_comp]
    exact ⟨k, hq₁, hq₂⟩

/-- **The one-object collapse**: forget the bases, keeping possibilities up
to base-agreement. Functoriality on composition is `toUpdate_comp`; on
identities it is `Quotient.sound`/`exact` — which is why the quotient is
forced: on raw possibilities `toUpdate (𝟙 X)` is agreement-on-`X`, not
equality. -/
def collapse (W M V : Type*) : Ctx W M V ⥤ RelCat where
  obj X := Quotient X.agreeSetoid
  map u := .ofRel {pq | collapseRel u pq.1 pq.2}
  map_id X := by
    apply RelCat.Hom.ext
    ext ⟨p, q⟩
    rw [Set.mem_setOf_eq, RelCat.Hom.rel_id]
    exact (collapseRel_id X p q).trans SetRel.mem_id.symm
  map_comp {X Y Z} u v := by
    apply RelCat.Hom.ext
    ext ⟨p, r⟩
    rw [Set.mem_setOf_eq, RelCat.Hom.rel_comp, collapseRel_comp]
    constructor
    · rintro ⟨q, h₁, h₂⟩
      exact SetRel.prodMk_mem_comp h₁ h₂
    · rintro ⟨q, h₁, h₂⟩
      exact ⟨q, h₁, h₂⟩

/-- The collapse is faithful: a transition is recoverable from its relation
on base-agreement classes. What the collapse forgets is only the
base-indexing of the objects. -/
instance collapse_faithful : (collapse W M V).Faithful where
  map_injective {X Y} {u v} h := by
    have hs : ∀ p q : Possibility W V M, u.t.toUpdate p q ↔ v.t.toUpdate p q :=
      fun p q => Set.ext_iff.mp (congrArg RelCat.Hom.rel h) (⟦p⟧, ⟦q⟧)
    refine Hom.ext (Transition.ext ?_)
    funext w f g
    exact propext (by simpa [Transition.toUpdate] using hs ⟨w, f⟩ ⟨w, g⟩)

end Ctx

end DynamicSemantics
