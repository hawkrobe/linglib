import Linglib.Semantics.Dynamic.State
import Linglib.Semantics.Dynamic.ContextChange

/-!
# Transitions between based information states
[kamp-vangenabith-reyle-2011] (Defs. 24, 27)

The hom type of based dynamic semantics: a `Transition W M X Y` is a
world-indexed relation between assignments that reads its input only at the
source base `X` and writes its output only at the target base `Y ⊇ X`.
Objects are bases (finite sets of discourse referents); a DRS denotes an
arrow `X ⟶ X ∪ U`; sequencing is world-pointwise relational composition.

Applying a transition to a `State` (Def. 24) is the level-0 `lift` of
`ContextChange.lean` at the forgotten relation (`toUpdate`) — level 1 rides
level 0 by construction. The chapter's regularity conditions (Def. 27)
become theorems: the base of the output is `I.base ∪ Y` (`apply_base`), and
applying an extension at its source base only adds information
(`le_apply`). In the unbased, one-object collapse these facts degrade into
side conditions (the Merging Lemma's freshness hypothesis); here the typing
carries them.

## Main declarations

* `Transition` — the based relation; `id`, `comp` and their laws.
* `Transition.toUpdate` — forget the bases (the collapse to level 0).
* `Transition.apply` — Def. 24's context change, via `lift`.
* `Transition.IsExtension` / `le_apply` — Def. 27(ii): information growth.
-/

namespace Semantics.Dynamic

open Semantics.Dynamic.Core (lift)

variable {W V M : Type*} {X Y Z : Finset V}

/-- A transition: a world-indexed relation between assignments reading
inputs at `X` and writing outputs at `Y`. The `grow` field makes arrows
context-extending — bases never shrink. -/
@[ext] structure Transition (W M : Type*) {V : Type*} (X Y : Finset V) where
  /-- The world-indexed relation between input and output assignments. -/
  rel : W → (V → M) → (V → M) → Prop
  /-- Bases only grow along an update. -/
  grow : X ⊆ Y
  /-- Inputs are read only at the source base. -/
  supported_left : ∀ ⦃w f f' g⦄, Set.EqOn f f' ↑X → (rel w f g ↔ rel w f' g)
  /-- Outputs are constrained only at the target base. -/
  supported_right : ∀ ⦃w f g g'⦄, Set.EqOn g g' ↑Y → (rel w f g ↔ rel w f g')

namespace Transition

/-- The identity transition at `X`: the test that changes nothing. -/
def id (X : Finset V) : Transition W M X X where
  rel _ f g := Set.EqOn f g ↑X
  grow := subset_rfl
  supported_left _ _ _ _ hff' := ⟨hff'.symm.trans, hff'.trans⟩
  supported_right _ _ _ _ hgg' := ⟨(·.trans hgg'), (·.trans hgg'.symm)⟩

/-- Sequencing: world-pointwise relational composition. -/
def comp (u : Transition W M X Y) (v : Transition W M Y Z) :
    Transition W M X Z where
  rel w := Relation.Comp (u.rel w) (v.rel w)
  grow := u.grow.trans v.grow
  supported_left _ _ _ _ hff' :=
    exists_congr fun _ => and_congr_left fun _ => u.supported_left hff'
  supported_right _ _ _ _ hgg' :=
    exists_congr fun _ => and_congr_right fun _ => v.supported_right hgg'

@[simp] theorem id_comp (u : Transition W M X Y) : (id X).comp u = u := by
  ext w f g
  exact ⟨fun ⟨k, hfk, hk⟩ => (u.supported_left hfk).mpr hk,
    fun h => ⟨f, Set.eqOn_refl f _, h⟩⟩

@[simp] theorem comp_id (u : Transition W M X Y) : u.comp (id Y) = u := by
  ext w f g
  exact ⟨fun ⟨k, hk, hkg⟩ => (u.supported_right hkg).mp hk,
    fun h => ⟨g, h, Set.eqOn_refl g _⟩⟩

theorem comp_assoc (u : Transition W M X Y) (v : Transition W M Y Z)
    {Z' : Finset V} (t : Transition W M Z Z') :
    (u.comp v).comp t = u.comp (v.comp t) := by
  ext w f g
  exact ⟨fun ⟨k, ⟨j, hj, hjk⟩, hk⟩ => ⟨j, hj, k, hjk, hk⟩,
    fun ⟨j, hj, k, hjk, hk⟩ => ⟨k, ⟨j, hj, hjk⟩, hk⟩⟩

/-! ### Application to information states -/

section Apply
variable [DecidableEq V]

/-- Forget the bases: the level-0 relation on possibilities (the world is
preserved). -/
def toUpdate (u : Transition W M X Y) :
    Core.DynProp.Update (Possibility W V M) :=
  fun p q => p.world = q.world ∧ u.rel p.world p.assignment q.assignment

/-- Context change ([kamp-vangenabith-reyle-2011], Def. 24): the carrier is
the level-0 `lift` of the forgotten relation; the base grows to
`I.base ∪ Y` (Def. 27(ii)). -/
def apply (u : Transition W M X Y) (I : State W V M) : State W V M where
  base := I.base ∪ Y
  carrier := lift u.toUpdate I.carrier
  supported := baseSupported_of_iff fun _ _ _ hgg' =>
    exists_congr fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      u.supported_right (hgg'.mono (by simp))

@[simp] theorem apply_base (u : Transition W M X Y) (I : State W V M) :
    (u.apply I).base = I.base ∪ Y := rfl

theorem mem_apply {u : Transition W M X Y} {I : State W V M} {w : W}
    {g : V → M} :
    (⟨w, g⟩ : Possibility W V M) ∈ u.apply I ↔
      ∃ f, (⟨w, f⟩ : Possibility W V M) ∈ I ∧ u.rel w f g := by
  constructor
  · rintro ⟨⟨w', f⟩, hf, rfl, hr⟩
    exact ⟨f, hf, hr⟩
  · rintro ⟨f, hf, hr⟩
    exact ⟨⟨w, f⟩, hf, rfl, hr⟩

/-- Applying the identity transition is the identity, at the identity. -/
@[simp] theorem apply_id (I : State W V M) (h : I.base = X) :
    (id X).apply I = I := by
  ext1
  · simp [h]
  · ext ⟨w, g⟩
    rw [State.mem_carrier, mem_apply]
    exact ⟨fun ⟨f, hf, hfg⟩ => (I.supported.mem_iff (h ▸ hfg)).mp hf,
      fun hg => ⟨g, hg, Set.eqOn_refl g _⟩⟩

/-- `apply` is functorial: sequencing then applying is applying twice. -/
theorem apply_comp (u : Transition W M X Y) (v : Transition W M Y Z)
    (I : State W V M) : (u.comp v).apply I = v.apply (u.apply I) := by
  ext1
  · simp only [apply_base, Finset.union_assoc, Finset.union_eq_right.mpr v.grow]
  · ext ⟨w, h⟩
    rw [State.mem_carrier, mem_apply, State.mem_carrier, mem_apply]
    constructor
    · rintro ⟨f, hf, k, hfk, hkh⟩
      exact ⟨k, mem_apply.mpr ⟨f, hf, hfk⟩, hkh⟩
    · rintro ⟨k, hk, hkh⟩
      obtain ⟨f, hf, hfk⟩ := mem_apply.mp hk
      exact ⟨f, hf, k, hfk, hkh⟩

end Apply

/-! ### Information growth (Def. 27) -/

/-- A transition is an *extension* when outputs agree with inputs on the source
base: established referents persist, only new ones are assigned. -/
def IsExtension (u : Transition W M X Y) : Prop :=
  ∀ ⦃w f g⦄, u.rel w f g → Set.EqOn g f ↑X

/-- The identity is an extension. -/
theorem isExtension_id : (id X : Transition W M X X).IsExtension :=
  fun _ _ _ h => h.symm

/-- Extensions compose. -/
theorem IsExtension.comp {u : Transition W M X Y} {v : Transition W M Y Z}
    (hu : u.IsExtension) (hv : v.IsExtension) : (u.comp v).IsExtension := by
  rintro w f g ⟨k, hfk, hkg⟩
  exact ((hv hkg).mono (Finset.coe_subset.mpr u.grow)).trans (hu hfk)

/-- Def. 27(ii): applying an extension at its source base only adds
information — the informativeness order grows along updates. -/
theorem le_apply [DecidableEq V] (u : Transition W M X Y) (hu : u.IsExtension)
    (I : State W V M) (hbase : I.base = X) : I ≤ u.apply I := by
  refine ⟨hbase ▸ Finset.subset_union_left, ?_⟩
  rintro ⟨w, g⟩ hg
  obtain ⟨f, hf, hr⟩ := mem_apply.mp hg
  exact (I.supported.mem_iff ((hu hr).symm.mono (by rw [hbase]))).mp hf

end Transition

end Semantics.Dynamic
