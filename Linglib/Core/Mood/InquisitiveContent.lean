import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

/-!
# Inquisitive Content
@cite{ciardelli-groenendijk-roelofsen-2018} @cite{puncochar-2016}
@cite{puncochar-2019} @cite{theiler-etal-2018}

A bundled `InquisitiveContent W` representing a sentence meaning in the
sense of @cite{theiler-etal-2018} Definition 1: a non-empty
downward-closed set of propositions over `W` (where a proposition is a
subset of `W`).

This is the linglib **sibling structure** to `Setoid W` for the inquiry
component of a discourse context. Where `Setoid W` (used in
`Core/Mood/POSWQ.lean`) represents partition-based questions, this type
represents the full @cite{ciardelli-groenendijk-roelofsen-2018}
inquisitive proposition: a downward-closed family of information states
with possibly non-disjoint, possibly non-exhaustive alternatives.
Mention-some, intermediate-exhaustive, and conditional question
phenomena live here (none representable as a Setoid partition).

Algebraically (per @cite{puncochar-2019}, p. 298): declarative
propositions are the **principal ideals** in the algebra of information
states. We expose this characterization as `isDeclarative`.

## Mathlib alignment

- `props : Set (Set W)` — sets of subsets of `W`, mathlib-native
- `contains_empty` is logically equivalent to `Nonempty props` together
  with downward closure — we expose it as the field directly because
  it's the only constraint that matters once downward closure holds
- `info` returns `Set W` (mathlib-native), not `W → Bool` — for the
  Bool/List computational variants of inquisitive operations, see
  `Core/Inquisitive.lean`

## Architectural placement

This file sits in `Core/Mood/` next to `POSW.lean` and `POSWQ.lean` as
the **sibling type** to `Setoid W` for the inquiry component, following
the prescription in the `POSWQ.lean` "Architectural note" docstring. It
does *not* replace `POSWQ.inquiry : Setoid W`; the embedding goes the
other way (`Setoid → InquisitiveContent` in
`Core/Mood/PartitionAsInquiry.lean`, forthcoming). Mirrors mathlib's
`Set`/`Finset` and `Filter`/`Ultrafilter` parallel-structures pattern
rather than collapsing the two types.
-/

namespace Core.Mood

universe u

/-- A sentence meaning in the inquisitive-semantics sense of
    @cite{theiler-etal-2018} Definition 1: a non-empty downward-closed
    set of propositions over `W`. The propositions in `props` are the
    information states that *resolve* the issue raised by the sentence. -/
structure InquisitiveContent (W : Type u) where
  /-- The set of propositions resolving the issue. -/
  props : Set (Set W)
  /-- Contains the empty proposition (= the inconsistent information
      state). Equivalent to non-emptiness given downward closure. -/
  contains_empty : ∅ ∈ props
  /-- Downward closed: if `p` resolves the issue and `q ⊆ p`, then `q`
      also resolves it (any sufficient evidence is also sufficient when
      strengthened). -/
  downward_closed : ∀ p ∈ props, ∀ q : Set W, q ⊆ p → q ∈ props

namespace InquisitiveContent

variable {W : Type u}

/-- The **alternatives** of an inquisitive content (@cite{theiler-etal-2018}
    Definition 2): the maximal propositions in `props`. These are the
    "answers" — the strongest information states that resolve the issue. -/
def alt (P : InquisitiveContent W) : Set (Set W) :=
  {p ∈ P.props | ∀ q ∈ P.props, p ⊆ q → p = q}

/-- The **informative content** of an inquisitive content
    (@cite{theiler-etal-2018} Definition 2): the union of all
    propositions in `props`. The information any utterance with this
    meaning provides — the actual world must lie in `info P`. -/
def info (P : InquisitiveContent W) : Set W :=
  ⋃₀ P.props

/-- Truth in a world (@cite{theiler-etal-2018} Definition 2): `w ∈ info P`. -/
def trueAt (P : InquisitiveContent W) (w : W) : Prop :=
  w ∈ info P

/-- A sentence is **informative** iff its informative content excludes
    at least one possible world. -/
def isInformative (P : InquisitiveContent W) : Prop :=
  info P ≠ Set.univ

/-- A sentence is **inquisitive** iff resolving the issue it raises
    requires more than the information it provides — equivalently, iff
    `info P` itself is not in `props` (so no single proposition in
    `props` covers all of `info P`). -/
def isInquisitive (P : InquisitiveContent W) : Prop :=
  info P ∉ P.props

/-- A sentence is **declarative** iff it is not inquisitive —
    equivalently, iff `info P ∈ props`. Algebraic characterization
    (@cite{puncochar-2019}, p. 298): `props` is a principal ideal in
    the algebra of information states. -/
def isDeclarative (P : InquisitiveContent W) : Prop :=
  info P ∈ P.props

/-! ### Constructors -/

/-- The **declarative** content of a proposition `p`: the principal
    ideal `{q | q ⊆ p}`. Single alternative `p`; non-inquisitive;
    informative iff `p ≠ univ`. The meaning of `Amy left.`
    (@cite{theiler-etal-2018} Figure 2(b)). -/
def declarative (p : Set W) : InquisitiveContent W where
  props := {q | q ⊆ p}
  contains_empty := Set.empty_subset p
  downward_closed := fun _ hq _ hr => hr.trans hq

/-- The **polar interrogative** content of a proposition `p`:
    alternatives are `p` and its complement `pᶜ`. Inquisitive (two
    alternatives) when `p` is non-trivial; non-informative
    (`info = univ`). The meaning of `Did Amy leave?`
    (@cite{theiler-etal-2018} Figure 2(a)). -/
def polar (p : Set W) : InquisitiveContent W where
  props := {q | q ⊆ p ∨ q ⊆ pᶜ}
  contains_empty := Or.inl (Set.empty_subset p)
  downward_closed := fun _ hq _ hr => by
    rcases hq with h | h
    · exact Or.inl (hr.trans h)
    · exact Or.inr (hr.trans h)

/-! ### Basic theorems on declarative -/

theorem info_declarative (p : Set W) : (declarative p).info = p := by
  ext w
  simp only [info, declarative, Set.mem_sUnion, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨q, hq, hwq⟩; exact hq hwq
  · intro hw; exact ⟨p, subset_rfl, hw⟩

theorem isDeclarative_declarative (p : Set W) :
    (declarative p).isDeclarative := by
  show (declarative p).info ∈ (declarative p).props
  rw [info_declarative]
  exact (subset_rfl : p ⊆ p)

theorem not_isInquisitive_declarative (p : Set W) :
    ¬ (declarative p).isInquisitive :=
  fun h => h (isDeclarative_declarative p)

/-! ### Basic theorems on polar -/

theorem info_polar (p : Set W) : (polar p).info = Set.univ := by
  ext w
  simp only [info, polar, Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_univ,
             iff_true]
  by_cases hw : w ∈ p
  · exact ⟨p, Or.inl subset_rfl, hw⟩
  · exact ⟨pᶜ, Or.inr subset_rfl, hw⟩

theorem not_isInformative_polar (p : Set W) :
    ¬ (polar p).isInformative := by
  show ¬ (polar p).info ≠ Set.univ
  rw [not_not]
  exact info_polar p

/-- A polar question is **inquisitive** iff its proposition is
    non-trivial (neither `∅` nor `univ`). The trivial cases collapse to
    declaratives because `univ ⊆ p` requires `p = univ`. -/
theorem isInquisitive_polar_iff (p : Set W) :
    (polar p).isInquisitive ↔ p ≠ ∅ ∧ p ≠ Set.univ := by
  show (polar p).info ∉ (polar p).props ↔ _
  rw [info_polar]
  simp only [polar, Set.mem_setOf_eq, not_or]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro hp
      apply h2
      rw [hp, Set.compl_empty]
    · intro hp
      apply h1
      rw [hp]
  · rintro ⟨hne, hnu⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hnu (Set.eq_univ_of_univ_subset h)
    · intro h
      apply hne
      have : (Set.univ : Set W) ⊆ pᶜ := h
      rw [Set.univ_subset_iff] at this
      rw [← compl_compl p, this, Set.compl_univ]

end InquisitiveContent

end Core.Mood
