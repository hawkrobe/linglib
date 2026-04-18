import Mathlib.Data.Finset.Card

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

A premise set is a `List (Index → Bool)`. The notions of *consistency*,
*following from*, and *compatibility* are purely set-theoretic facts about
extensions in `Index` — they are about logical relations on propositions, not
about modality. Modal operators (necessity, possibility) are then defined in
terms of these primitives, but the primitives themselves should be available
to any module that wants to talk about premises (counterfactual analysis,
discourse update, situation lumping, ...).

This file lifts what was previously sitting inside
`Theories/Semantics/Modality/Kratzer/Background.lean` to the Core layer, so
that downstream modules can import it without dragging in the entire Kratzer
modal machinery.

## Key definitions

- `propExtension` — extension of a proposition (set of indices where it holds)
- `propIntersection` — intersection of a list of propositions
- `followsFrom` — `p` follows from `A` iff `∩A ⊆ p` (Kratzer p. 31)
- `isConsistent` — `A` is consistent iff `∩A ≠ ∅`
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

variable {Index : Type*} [DecidableEq Index] [Fintype Index]

/-! ## Primitives on premise sets -/

/-- Convert a Boolean proposition to the finite set of indices at which it holds. -/
def propExtension (p : Index → Bool) : Finset Index :=
  Finset.univ.filter (fun i => p i)

/-- The intersection of a list of propositions: indices satisfying *all* of them. -/
def propIntersection (props : List (Index → Bool)) : Finset Index :=
  Finset.univ.filter (fun i => props.all fun p => p i)

/-- A proposition `p` **follows from** a premise set `A` iff `∩A ⊆ p`
    (@cite{kratzer-1977} p. 31). -/
def followsFrom (p : Index → Bool) (A : List (Index → Bool)) : Bool :=
  decide (∀ i ∈ propIntersection A, p i = true)

/-- A premise set is **consistent** iff `∩A ≠ ∅` (@cite{kratzer-1977} p. 31). -/
def isConsistent (A : List (Index → Bool)) : Bool :=
  !(propIntersection A == ∅)

/-- A proposition `p` is **compatible with** `A` iff `A ∪ {p}` is consistent. -/
def isCompatibleWith (p : Index → Bool) (A : List (Index → Bool)) : Bool :=
  isConsistent (p :: A)

/-! ## Kratzer 1977 Definitions 5–6: must/can in view of -/

/-- **Def 5** (@cite{kratzer-1977}): `must p in view of f` at index `i`
    iff `p` follows from the premise set `f i`.

    `ν(p, f) = {i : ∩(f i) ⊆ p}` -/
def mustInView (f : Index → List (Index → Bool)) (p : Index → Bool) (i : Index) : Bool :=
  followsFrom p (f i)

/-- **Def 6** (@cite{kratzer-1977}): `can p in view of f` at index `i`
    iff `p` is compatible with the premise set `f i`.

    `μ(p, f) = {i : ∩((f i) ∪ {p}) ≠ ∅}` -/
def canInView (f : Index → List (Index → Bool)) (p : Index → Bool) (i : Index) : Bool :=
  isCompatibleWith p (f i)

/-! ## Kratzer 1977 Definitions 7–8: revised must/can for inconsistent premise sets -/

/-- The set of consistent sublists of a premise set: `X_A = {B ⊆ A : consistent B}`.
    Kratzer's revised definitions quantify over these to handle inconsistent `A`.

    Concretely: powerset of `A` (as a list, since `A` is a list), filtered by
    `isConsistent`. -/
def consistentSublists (A : List (Index → Bool)) : List (List (Index → Bool)) :=
  A.sublists.filter isConsistent

/-- **Def 7** (@cite{kratzer-1977}): the revised necessity operator that handles
    possibly inconsistent premise sets.

    `must p in view of f` at `i` iff for every consistent subset `B` of `f i`,
    there exists a consistent subset `C ⊇ B` such that `p` follows from `C`.

    Original notation:
    `ν(p, f) = {i : ∀B[B ∈ X_{f(i)} → ∃C[C ∈ X_{f(i)} ∧ B ⊆ C ∧ ∩C ⊆ p]]}` -/
def mustInView' (f : Index → List (Index → Bool)) (p : Index → Bool) (i : Index) : Bool :=
  decide (∀ B ∈ consistentSublists (f i),
    ∃ C ∈ consistentSublists (f i), B ⊆ C ∧ followsFrom p C = true)

/-- **Def 8** (@cite{kratzer-1977}): the revised possibility operator that handles
    possibly inconsistent premise sets.

    `can p in view of f` at `i` iff there exists a consistent subset `B` of `f i`
    such that for every consistent subset `C ⊇ B`, the set `C ∪ {p}` is consistent.

    Original notation:
    `μ(p, f) = {i : ∃B[B ∈ X_{f(i)} ∧ ∀C[(C ∈ X_{f(i)} ∧ B ⊆ C) → consistent(C ∪ {p})]]}` -/
def canInView' (f : Index → List (Index → Bool)) (p : Index → Bool) (i : Index) : Bool :=
  decide (∃ B ∈ consistentSublists (f i),
    ∀ C ∈ consistentSublists (f i), B ⊆ C → isCompatibleWith p C = true)

/-! ## Reduction to the unrevised definitions

When the premise set `f i` is itself consistent, Kratzer's revised definitions
collapse to the original Defs 5–6: there is no "inconsistency to repair." The
proofs are deferred — they require the witness `B := f i` (with `f i ⊆ f i`),
plus the lemma that `B ⊆ C` and `consistent C` jointly imply `B ⊆ C` is
witnessed by `f i` itself. -/

/-- When `f i` is consistent, the revised necessity operator coincides with the
    original. -/
theorem mustInView_iff_mustInView'_of_consistent
    (f : Index → List (Index → Bool)) (p : Index → Bool) (i : Index)
    (_h : isConsistent (f i) = true) :
    mustInView' f p i = true ↔ mustInView f p i = true := by
  sorry
  -- TODO: prove using `f i ∈ consistentSublists (f i)` (it is a sublist of
  -- itself and is consistent by `_h`); the witness `C := f i` always works.

/-- When `f i` is consistent, the revised possibility operator coincides with
    the original. -/
theorem canInView_iff_canInView'_of_consistent
    (f : Index → List (Index → Bool)) (p : Index → Bool) (i : Index)
    (_h : isConsistent (f i) = true) :
    canInView' f p i = true ↔ canInView f p i = true := by
  sorry
  -- TODO: prove using `B := f i` as the existential witness, then specialize
  -- the universal to `C := f i`.

end Core.IntensionalLogic.Premise
