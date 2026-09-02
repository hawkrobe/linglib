import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Sublists

/-!
# Premise sets

Kratzer's premise semantics: a premise set is a list of propositions over an index type, a
proposition follows from it when it holds throughout the set's intersection, and the set is
consistent when that intersection is inhabited. *Must* and *can* in view of a conversational
background `f` are consequence from, and compatibility with, `f i` (Definitions 5 and 6);
when `f i` may be inconsistent they are restated over its consistent sublists (Definitions 7
and 8), and the two pairs agree on consistent backgrounds. Nothing here commits to what an
index is: worlds, situations, or times.

## Main definitions

* `propIntersection A`: the indices satisfying every member of `A`, Kratzer's `⋂A`.
* `followsFrom p A`, `isConsistent A`, `isCompatibleWith p A`.
* `mustInView`, `canInView`: Definitions 5 and 6.
* `mustInView'`, `canInView'`: Definitions 7 and 8, over `consistentSublists`.

## Main results

* `mustInView_iff_mustInView'_of_consistent`, `canInView_iff_canInView'_of_consistent`:
  the revised operators agree with the original ones on a consistent premise set.

## References

* [A. Kratzer, *What 'must' and 'can' must and can mean* (1977)][kratzer-1977]
* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
-/

namespace Modality.Kratzer

variable {W : Type*}

/-! ### Primitives on premise sets -/

/-- The intersection of a list of propositions: indices satisfying *all* of them. -/
def propIntersection (props : List (W → Prop)) : Set W :=
  {i | ∀ p ∈ props, p i}

/-- A proposition `p` **follows from** a premise set `A` iff `⋂ A ⊆ {i | p i}`
    ([kratzer-1977] p. 31). -/
def followsFrom (p : W → Prop) (A : List (W → Prop)) : Prop :=
  propIntersection A ⊆ {i | p i}

/-- A premise set is **consistent** iff `⋂ A` is non-empty ([kratzer-1977] p. 31). -/
def isConsistent (A : List (W → Prop)) : Prop :=
  (propIntersection A).Nonempty

/-- A proposition `p` is **compatible with** `A` iff `A ∪ {p}` is consistent. -/
def isCompatibleWith (p : W → Prop) (A : List (W → Prop)) : Prop :=
  isConsistent (p :: A)

theorem mem_propIntersection {A : List (W → Prop)} {i : W} :
    i ∈ propIntersection A ↔ ∀ p ∈ A, p i := Iff.rfl

/-- The intersection of a premise set is contained in each of its members. -/
theorem propIntersection_subset {x : W → Prop} {A : List (W → Prop)} (hx : x ∈ A) :
    propIntersection A ⊆ {i | x i} :=
  fun _ hi => hi x hx

theorem propIntersection_nil : propIntersection ([] : List (W → Prop)) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ hp => absurd hp List.not_mem_nil

theorem propIntersection_cons (p : W → Prop) (A : List (W → Prop)) :
    propIntersection (p :: A) = {i | p i} ∩ propIntersection A := by
  ext i
  simp [mem_propIntersection]

theorem propIntersection_singleton (p : W → Prop) : propIntersection [p] = {i | p i} := by
  rw [propIntersection_cons, propIntersection_nil, Set.inter_univ]

theorem isCompatibleWith_iff_exists {p : W → Prop} {A : List (W → Prop)} :
    isCompatibleWith p A ↔ ∃ i ∈ propIntersection A, p i := by
  simp only [isCompatibleWith, isConsistent, Set.Nonempty, mem_propIntersection,
    List.forall_mem_cons]
  exact ⟨fun ⟨i, hp, hA⟩ => ⟨i, hA, hp⟩, fun ⟨i, hA, hp⟩ => ⟨i, hp, hA⟩⟩

/-- Duality: `p` is compatible with `A` iff `¬p` does not follow from `A`. -/
theorem isCompatibleWith_iff_not_followsFrom_not {p : W → Prop}
    {A : List (W → Prop)} :
    isCompatibleWith p A ↔ ¬ followsFrom (fun i => ¬ p i) A := by
  rw [isCompatibleWith_iff_exists]
  simp [followsFrom, Set.subset_def, not_forall]

/-! ### Definitions 5 and 6: must and can in view of -/

/-- **Def 5** ([kratzer-1977]): `must p in view of f` at index `i`
    iff `p` follows from the premise set `f i`.

    `ν(p, f) = {i : ⋂(f i) ⊆ p}` -/
def mustInView (f : W → List (W → Prop)) (p : W → Prop) (i : W) : Prop :=
  followsFrom p (f i)

/-- **Def 6** ([kratzer-1977]): `can p in view of f` at index `i`
    iff `p` is compatible with the premise set `f i`.

    `μ(p, f) = {i : ⋂((f i) ∪ {p}) ≠ ∅}` -/
def canInView (f : W → List (W → Prop)) (p : W → Prop) (i : W) : Prop :=
  isCompatibleWith p (f i)

/-! ### Definitions 7 and 8: must and can over consistent sublists -/

/-- The set of consistent sublists of a premise set: `X_A = {B ⊆ A : consistent B}`.
    Kratzer's revised definitions quantify over these to handle inconsistent `A`.

    Concretely: a sublist `B` of `A` such that `B` is consistent. -/
def consistentSublists (A : List (W → Prop)) : Set (List (W → Prop)) :=
  {B | B ∈ A.sublists ∧ isConsistent B}

/-- **Def 7** ([kratzer-1977]): the revised necessity operator that handles
    possibly inconsistent premise sets.

    `must p in view of f` at `i` iff for every consistent subset `B` of `f i`,
    there exists a consistent subset `C ⊇ B` such that `p` follows from `C`.

    Original notation:
    `ν(p, f) = {i : ∀B[B ∈ X_{f(i)} → ∃C[C ∈ X_{f(i)} ∧ B ⊆ C ∧ ⋂C ⊆ p]]}` -/
def mustInView' (f : W → List (W → Prop)) (p : W → Prop) (i : W) : Prop :=
  ∀ B ∈ consistentSublists (f i),
    ∃ C ∈ consistentSublists (f i), B ⊆ C ∧ followsFrom p C

/-- **Def 8** ([kratzer-1977]): the revised possibility operator that handles
    possibly inconsistent premise sets.

    `can p in view of f` at `i` iff there exists a consistent subset `B` of `f i`
    such that for every consistent subset `C ⊇ B`, the set `C ∪ {p}` is consistent.

    Original notation:
    `μ(p, f) = {i : ∃B[B ∈ X_{f(i)} ∧ ∀C[(C ∈ X_{f(i)} ∧ B ⊆ C) → consistent(C ∪ {p})]]}` -/
def canInView' (f : W → List (W → Prop)) (p : W → Prop) (i : W) : Prop :=
  ∃ B ∈ consistentSublists (f i),
    ∀ C ∈ consistentSublists (f i), B ⊆ C → isCompatibleWith p C

/-! ### Monotonicity

The reduction theorems below need three monotonicity facts about the premise
algebra. They are proved here once and reused. -/

/-- `propIntersection` is **anti-monotone** in the premise list: more premises
    can only shrink the set of indices satisfying *all* of them. -/
theorem propIntersection_anti_of_subset
    {A B : List (W → Prop)} (h : A ⊆ B) :
    propIntersection B ⊆ propIntersection A := by
  intro _ hi p hp
  exact hi p (h hp)

/-- `followsFrom` is **monotone** in the premise list: more premises only add
    consequences. -/
theorem followsFrom_mono_of_subset
    {p : W → Prop} {A B : List (W → Prop)}
    (h : A ⊆ B) (hp : followsFrom p A) : followsFrom p B :=
  fun _ hi => hp (propIntersection_anti_of_subset h hi)

/-- `isCompatibleWith` is **anti-monotone** in the premise list: removing
    premises can only make a proposition easier to be compatible with. -/
theorem isCompatibleWith_anti_of_subset
    {p : W → Prop} {A B : List (W → Prop)}
    (h : B ⊆ A) (hp : isCompatibleWith p A) :
    isCompatibleWith p B := by
  have hcons : (p :: B) ⊆ (p :: A) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxB
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h hxB)
  obtain ⟨i, hi⟩ := hp
  exact ⟨i, propIntersection_anti_of_subset hcons hi⟩

/-- A consistent premise list is itself a member of its own consistent
    sublist powerset. -/
theorem self_mem_consistentSublists
    {A : List (W → Prop)} (h : isConsistent A) :
    A ∈ consistentSublists A :=
  ⟨List.mem_sublists.mpr (List.Sublist.refl _), h⟩

/-- Every element of `consistentSublists A` is a `⊆`-subset of `A`. -/
theorem subset_of_mem_consistentSublists
    {A B : List (W → Prop)} (h : B ∈ consistentSublists A) :
    B ⊆ A :=
  (List.mem_sublists.mp h.1).subset

/-! ### Reduction to Definitions 5 and 6

When the premise set `f i` is itself consistent, Kratzer's revised definitions
collapse to the original Defs 5–6: there is no "inconsistency to repair." The
witness for both directions is `f i` itself — it is a sublist of itself, it
is consistent by hypothesis, and `B ⊆ f i` for every `B ∈ consistentSublists (f i)`. -/

/-- When `f i` is consistent, the revised necessity operator coincides with
    the original. -/
theorem mustInView_iff_mustInView'_of_consistent
    (f : W → List (W → Prop)) (p : W → Prop) (i : W)
    (h : isConsistent (f i)) :
    mustInView' f p i ↔ mustInView f p i := by
  unfold mustInView mustInView'
  refine ⟨fun hAll => ?_, fun hFollows B hB => ?_⟩
  · -- (⇒) Specialize the universal to `B := f i`; the resulting `C` is a
    -- sublist of `f i`, so `followsFrom` lifts back to `f i`.
    obtain ⟨C, hC_mem, _, hfollows⟩ := hAll _ (self_mem_consistentSublists h)
    exact followsFrom_mono_of_subset (subset_of_mem_consistentSublists hC_mem) hfollows
  · -- (⇐) Take `C := f i`; it dominates every `B` in the sublist powerset
    -- and inherits `followsFrom p` from the hypothesis.
    exact ⟨f i, self_mem_consistentSublists h,
      subset_of_mem_consistentSublists hB, hFollows⟩

/-- When `f i` is consistent, the revised possibility operator coincides with
    the original. -/
theorem canInView_iff_canInView'_of_consistent
    (f : W → List (W → Prop)) (p : W → Prop) (i : W)
    (h : isConsistent (f i)) :
    canInView' f p i ↔ canInView f p i := by
  unfold canInView canInView'
  refine ⟨fun ⟨B, hB_mem, hAll⟩ => ?_, fun hCompat => ?_⟩
  · -- (⇒) Apply the universal to `C := f i`, which dominates `B`.
    exact hAll (f i) (self_mem_consistentSublists h)
      (subset_of_mem_consistentSublists hB_mem)
  · -- (⇐) Take `B := f i` as the existential witness; every dominating `C`
    -- in the sublist powerset is itself `⊆ f i`, so compatibility transfers.
    refine ⟨f i, self_mem_consistentSublists h, fun C hC _ => ?_⟩
    exact isCompatibleWith_anti_of_subset
      (subset_of_mem_consistentSublists hC) hCompat

end Modality.Kratzer
