import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Sublists

/-!
# Premise Sets and Logical Relations

@cite{kratzer-1977} @cite{kratzer-1981} @cite{kratzer-2012}

Generic, modality-agnostic primitives over **premise sets** — finite collections
of propositions over an arbitrary index type. These are the logical primitives
on which Kratzer's modal semantics, ordering sources, conditional restriction,
and lumping all rest, but they have no built-in commitment to "worlds" vs.
"situations" vs. "times": they make sense for any `Index : Type*` of points
at which propositions are evaluated.

## Why this lives in `Core/IntensionalLogic/`

A premise set is a `List (Index → Prop)`. The notions of *consistency*,
*following from*, and *compatibility* are purely set-theoretic facts about
extensions in `Index` — they are about logical relations on propositions, not
about modality. Modal operators (necessity, possibility) are then defined in
terms of these primitives, but the primitives themselves should be available
to any module that wants to talk about premises (counterfactual analysis,
discourse update, situation lumping, …).

## Mathlib-style discipline

Propositions are `Index → Prop` (mathlib-native), extensions are `Set Index`
(also mathlib-native). All predicates return `Prop`; we reason classically and
do *not* register `Decidable` instances. Callers who need decidability can
supply it locally via `[DecidablePred p]` in their own theorems; the core
intensional algebra is purely classical.

## Key definitions

- `propExtension` — extension of a proposition (`{i | p i}` as a `Set Index`)
- `propIntersection` — intersection of a list of propositions (`Set Index`)
- `followsFrom` — `p` follows from `A` iff `⋂ A ⊆ {i | p i}` (Kratzer p. 31)
- `isConsistent` — `A` is consistent iff `⋂ A` is non-empty
- `isCompatibleWith` — `p` is compatible with `A` iff `A ∪ {p}` is consistent

## Kratzer 1977 Definitions 5–8

- `mustInView` (Def 5) — `must p in view of f` at `i` iff `p` follows from `f i`
- `canInView`  (Def 6) — `can p in view of f`  at `i` iff `p` is compatible with `f i`

When `f i` may be inconsistent, Kratzer revises these in terms of *maximally
consistent subsets*:

- `consistentSublists` — `X_{f(i)}` in Kratzer's notation
- `mustInView'` (Def 7) — every consistent subset has a consistent extension
   from which `p` follows
- `canInView'`  (Def 8) — some consistent subset has a consistent extension
   that remains consistent with `p`

The revised definitions reduce to the original ones when the premise set is
itself consistent (`mustInView_iff_mustInView'_of_consistent`).
-/

namespace Core.IntensionalLogic.Premise

variable {Index : Type*}

/-! ## Primitives on premise sets -/

/-- The extension of a proposition: the set of indices at which it holds. -/
def propExtension (p : Index → Prop) : Set Index := {i | p i}

/-- The intersection of a list of propositions: indices satisfying *all* of them. -/
def propIntersection (props : List (Index → Prop)) : Set Index :=
  {i | ∀ p ∈ props, p i}

/-- A proposition `p` **follows from** a premise set `A` iff `⋂ A ⊆ {i | p i}`
    (@cite{kratzer-1977} p. 31). -/
def followsFrom (p : Index → Prop) (A : List (Index → Prop)) : Prop :=
  propIntersection A ⊆ propExtension p

/-- A premise set is **consistent** iff `⋂ A` is non-empty (@cite{kratzer-1977} p. 31). -/
def isConsistent (A : List (Index → Prop)) : Prop :=
  (propIntersection A).Nonempty

/-- A proposition `p` is **compatible with** `A` iff `A ∪ {p}` is consistent. -/
def isCompatibleWith (p : Index → Prop) (A : List (Index → Prop)) : Prop :=
  isConsistent (p :: A)

/-! ## Kratzer 1977 Definitions 5–6: must/can in view of -/

/-- **Def 5** (@cite{kratzer-1977}): `must p in view of f` at index `i`
    iff `p` follows from the premise set `f i`.

    `ν(p, f) = {i : ⋂(f i) ⊆ p}` -/
def mustInView (f : Index → List (Index → Prop)) (p : Index → Prop) (i : Index) : Prop :=
  followsFrom p (f i)

/-- **Def 6** (@cite{kratzer-1977}): `can p in view of f` at index `i`
    iff `p` is compatible with the premise set `f i`.

    `μ(p, f) = {i : ⋂((f i) ∪ {p}) ≠ ∅}` -/
def canInView (f : Index → List (Index → Prop)) (p : Index → Prop) (i : Index) : Prop :=
  isCompatibleWith p (f i)

/-! ## Kratzer 1977 Definitions 7–8: revised must/can for inconsistent premise sets -/

/-- The set of consistent sublists of a premise set: `X_A = {B ⊆ A : consistent B}`.
    Kratzer's revised definitions quantify over these to handle inconsistent `A`.

    Concretely: a sublist `B` of `A` such that `B` is consistent. -/
def consistentSublists (A : List (Index → Prop)) : Set (List (Index → Prop)) :=
  {B | B ∈ A.sublists ∧ isConsistent B}

/-- **Def 7** (@cite{kratzer-1977}): the revised necessity operator that handles
    possibly inconsistent premise sets.

    `must p in view of f` at `i` iff for every consistent subset `B` of `f i`,
    there exists a consistent subset `C ⊇ B` such that `p` follows from `C`.

    Original notation:
    `ν(p, f) = {i : ∀B[B ∈ X_{f(i)} → ∃C[C ∈ X_{f(i)} ∧ B ⊆ C ∧ ⋂C ⊆ p]]}` -/
def mustInView' (f : Index → List (Index → Prop)) (p : Index → Prop) (i : Index) : Prop :=
  ∀ B ∈ consistentSublists (f i),
    ∃ C ∈ consistentSublists (f i), B ⊆ C ∧ followsFrom p C

/-- **Def 8** (@cite{kratzer-1977}): the revised possibility operator that handles
    possibly inconsistent premise sets.

    `can p in view of f` at `i` iff there exists a consistent subset `B` of `f i`
    such that for every consistent subset `C ⊇ B`, the set `C ∪ {p}` is consistent.

    Original notation:
    `μ(p, f) = {i : ∃B[B ∈ X_{f(i)} ∧ ∀C[(C ∈ X_{f(i)} ∧ B ⊆ C) → consistent(C ∪ {p})]]}` -/
def canInView' (f : Index → List (Index → Prop)) (p : Index → Prop) (i : Index) : Prop :=
  ∃ B ∈ consistentSublists (f i),
    ∀ C ∈ consistentSublists (f i), B ⊆ C → isCompatibleWith p C

/-! ## Monotonicity helpers

The reduction theorems below need three monotonicity facts about the premise
algebra. They are proved here once and reused. -/

/-- `propIntersection` is **anti-monotone** in the premise list: more premises
    can only shrink the set of indices satisfying *all* of them. -/
theorem propIntersection_anti_of_subset
    {A B : List (Index → Prop)} (h : A ⊆ B) :
    propIntersection B ⊆ propIntersection A := by
  intro _ hi p hp
  exact hi p (h hp)

/-- `followsFrom` is **monotone** in the premise list: more premises only add
    consequences. -/
theorem followsFrom_mono_of_subset
    {p : Index → Prop} {A B : List (Index → Prop)}
    (h : A ⊆ B) (hp : followsFrom p A) : followsFrom p B :=
  fun i hi => hp (propIntersection_anti_of_subset h hi)

/-- `isCompatibleWith` is **anti-monotone** in the premise list: removing
    premises can only make a proposition easier to be compatible with. -/
theorem isCompatibleWith_anti_of_subset
    {p : Index → Prop} {A B : List (Index → Prop)}
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
    {A : List (Index → Prop)} (h : isConsistent A) :
    A ∈ consistentSublists A :=
  ⟨List.mem_sublists.mpr (List.Sublist.refl _), h⟩

/-- Every element of `consistentSublists A` is a `⊆`-subset of `A`. -/
theorem subset_of_mem_consistentSublists
    {A B : List (Index → Prop)} (h : B ∈ consistentSublists A) :
    B ⊆ A :=
  (List.mem_sublists.mp h.1).subset

/-! ## Reduction to the unrevised definitions

When the premise set `f i` is itself consistent, Kratzer's revised definitions
collapse to the original Defs 5–6: there is no "inconsistency to repair." The
witness for both directions is `f i` itself — it is a sublist of itself, it
is consistent by hypothesis, and `B ⊆ f i` for every `B ∈ consistentSublists (f i)`. -/

/-- When `f i` is consistent, the revised necessity operator coincides with
    the original. -/
theorem mustInView_iff_mustInView'_of_consistent
    (f : Index → List (Index → Prop)) (p : Index → Prop) (i : Index)
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
    (f : Index → List (Index → Prop)) (p : Index → Prop) (i : Index)
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

end Core.IntensionalLogic.Premise
