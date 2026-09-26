module

public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.List.Sublists

/-!
# Premise sets and conversational backgrounds

Kratzer's premise semantics: a premise set is a list of propositions over an index type, a
proposition follows from it when it holds throughout the set's intersection, and the set is
consistent when that intersection is inhabited ([kratzer-1977]). A conversational background
assigns each index a premise set, and Kratzer's two parameters of modal interpretation are
backgrounds in different roles: a modal base, `ModalBase`, whose premises at a world fix the
accessible worlds, those in its intersection, and an ordering source, `OrderingSource`, whose
premises rank the accessible worlds by how many of them they verify ([kratzer-1981],
[kratzer-2012]). A background is realistic when every world verifies its own premises,
`ConvBackground.IsRealistic`, so that the actual world is accessible from itself, and totally
realistic when its premises single out the world, `ConvBackground.IsTotallyRealistic`; the
empty background, `emptyBackground`, makes every world accessible. Nothing here commits to what
an index is: worlds, situations, or times.

## Main definitions

* `propIntersection A`: the indices satisfying every member of `A`, Kratzer's `⋂A`.
* `FollowsFrom p A`, `IsConsistent A`, `IsCompatibleWith p A`.
* `ConvBackground`, `ModalBase`, `OrderingSource`, `emptyBackground`.
* `ConvBackground.IsRealistic`, `ConvBackground.IsTotallyRealistic`.

## Main results

* `isCompatibleWith_iff_not_followsFrom_not`: compatibility with a premise set is the failure
  of the negation to follow from it, the duality of *can* and *must*.
* `propIntersection_anti_of_subset`, `followsFrom_mono_of_subset`,
  `isCompatibleWith_anti_of_subset`: more premises mean fewer indices, more consequences, and
  fewer compatible propositions.

## Implementation notes

Kratzer's *must* and *can* in view of a background, Definitions 5 and 6 of [kratzer-1977], are
`simpleNecessity` and `simplePossibility` in `Modality.Operators`; their revision over the
consistent sublists of an inconsistent premise set, Definitions 7 and 8, is the apparatus of
`Studies/Kratzer1977.lean`.

## References

* [kratzer-1977]
* [kratzer-1981]
* [kratzer-2012]
-/

@[expose] public section

namespace Modality

variable {W : Type*}

/-! ### Premise sets -/

/-- The intersection of a list of propositions: the indices satisfying all of them. -/
def propIntersection (props : List (W → Prop)) : Set W :=
  {i | ∀ p ∈ props, p i}

/-- A proposition `p` follows from a premise set `A` when `⋂ A ⊆ {i | p i}`. -/
def FollowsFrom (p : W → Prop) (A : List (W → Prop)) : Prop :=
  propIntersection A ⊆ {i | p i}

/-- A premise set is consistent when `⋂ A` is inhabited. -/
def IsConsistent (A : List (W → Prop)) : Prop :=
  (propIntersection A).Nonempty

/-- A proposition `p` is compatible with `A` when `A ∪ {p}` is consistent. -/
def IsCompatibleWith (p : W → Prop) (A : List (W → Prop)) : Prop :=
  IsConsistent (p :: A)

theorem mem_propIntersection {A : List (W → Prop)} {i : W} :
    i ∈ propIntersection A ↔ ∀ p ∈ A, p i := Iff.rfl

/-- The intersection of a premise set is contained in each of its members. -/
theorem propIntersection_subset {x : W → Prop} {A : List (W → Prop)} (hx : x ∈ A) :
    propIntersection A ⊆ {i | x i} :=
  fun _ hi ↦ hi x hx

theorem propIntersection_nil : propIntersection ([] : List (W → Prop)) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ hp ↦ absurd hp List.not_mem_nil

theorem propIntersection_cons (p : W → Prop) (A : List (W → Prop)) :
    propIntersection (p :: A) = {i | p i} ∩ propIntersection A := by
  ext i
  simp [mem_propIntersection]

theorem propIntersection_singleton (p : W → Prop) : propIntersection [p] = {i | p i} := by
  rw [propIntersection_cons, propIntersection_nil, Set.inter_univ]

/-- More premises can only shrink the indices satisfying all of them. -/
theorem propIntersection_anti_of_subset {A B : List (W → Prop)} (h : A ⊆ B) :
    propIntersection B ⊆ propIntersection A :=
  fun _ hi p hp ↦ hi p (h hp)

/-- More premises only add consequences. -/
theorem followsFrom_mono_of_subset {p : W → Prop} {A B : List (W → Prop)} (h : A ⊆ B)
    (hp : FollowsFrom p A) : FollowsFrom p B :=
  fun _ hi ↦ hp (propIntersection_anti_of_subset h hi)

theorem isCompatibleWith_iff_exists {p : W → Prop} {A : List (W → Prop)} :
    IsCompatibleWith p A ↔ ∃ i ∈ propIntersection A, p i := by
  simp only [IsCompatibleWith, IsConsistent, Set.Nonempty, mem_propIntersection,
    List.forall_mem_cons]
  exact ⟨fun ⟨i, hp, hA⟩ ↦ ⟨i, hA, hp⟩, fun ⟨i, hA, hp⟩ ↦ ⟨i, hp, hA⟩⟩

/-- Removing premises can only make a proposition easier to be compatible with. -/
theorem isCompatibleWith_anti_of_subset {p : W → Prop} {A B : List (W → Prop)} (h : B ⊆ A)
    (hp : IsCompatibleWith p A) : IsCompatibleWith p B :=
  isCompatibleWith_iff_exists.2 <|
    (isCompatibleWith_iff_exists.1 hp).imp fun _ ⟨hi, hpi⟩ ↦
      ⟨propIntersection_anti_of_subset h hi, hpi⟩

/-- `p` is compatible with `A` iff `¬p` does not follow from `A`. -/
theorem isCompatibleWith_iff_not_followsFrom_not {p : W → Prop} {A : List (W → Prop)} :
    IsCompatibleWith p A ↔ ¬ FollowsFrom (fun i ↦ ¬ p i) A := by
  rw [isCompatibleWith_iff_exists]
  simp [FollowsFrom, Set.subset_def, not_forall]

/-! ### Conversational backgrounds -/

/-- A conversational background assigns each index a premise set. -/
abbrev ConvBackground (W : Type*) := W → List (W → Prop)

/-- A modal base, the background whose premises fix the accessible worlds. -/
abbrev ModalBase (W : Type*) := ConvBackground W

/-- An ordering source, the background whose premises rank the accessible worlds. -/
abbrev OrderingSource (W : Type*) := ConvBackground W

/-- A background is realistic when every world verifies its own premises. -/
def ConvBackground.IsRealistic (f : ConvBackground W) : Prop :=
  ∀ w : W, ∀ p ∈ f w, p w

/-- A background is totally realistic when its premises at a world single out that world. -/
def ConvBackground.IsTotallyRealistic (f : ConvBackground W) : Prop :=
  ∀ w : W, propIntersection (f w) = {w}

/-- The empty background, with no premises at any world, makes every world accessible. -/
def emptyBackground : ConvBackground W := fun _ ↦ []

end Modality
