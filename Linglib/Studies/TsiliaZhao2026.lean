import Linglib.Semantics.Tense.Perspective
import Linglib.Data.Examples.TsiliaZhao2026

/-!
# Tsilia and Zhao (2026): Tense and Perspective: A Solution to the ⌈then⌉-Present Puzzle

This file formalizes the solution of [tsilia-zhao-2026] to the ⌈then⌉-present puzzle, (12):
the temporal adverb ⌈then⌉ cannot restrict a present-tensed verb phrase, whether the present
is shifted or not. In Greek, Hebrew, Russian and Japanese a present under a past attitude
verb shifts to the attitude's time, (8), yet ⌈then⌉ is still excluded, (9)–(11), although it
restricts an embedded past with the same simultaneous reference, (38)–(39), and a deleted,
sequence-of-tense past, (48)–(49). Tenses and ⌈then⌉ are temporal pronouns with
presuppositions relative to a perspective parameter `π`, (69)–(71): PRES overlap, PAST
precedence, ⌈then⌉ disjointness, the substrate's `Tense.Perspective`. Tense shift is the
rebinding of `π`, by the propositional operator OP_π of (73), to an evaluation index that an
attitude verb or WOLL binds, so a clausemate PRES and ⌈then⌉ shift together and read the same
`π`; since ⌈then⌉ restricts the reference of the tense it modifies, (76), their
presuppositions clash whatever `π` is, `not_presThen`, the derivations (77), (79), (81) and
(82). A pronominal anchor would let the two anchor separately, (36), which is coherent,
`exists_split_anchor`, hence the parameter. ⌈then⌉ restricts a PAST to its own reference,
`pastThen_self`, and a deleted tense, carrying no presupposition, (86)–(87), is compatible
with ⌈then⌉ when no operator shifts the perspective onto its reference, (89),
`deletedThen_of_not_overlaps` and `not_deletedThen_of_subset`.

## Implementation notes

Times are sets of points of a linear order, and clause meanings are their presuppositions
as functions of the perspective; the assertion, the assignment and the evaluation index are
suppressed, so OP_π is instantiation of the perspective, and the intensional binding that
licenses a shift, absent in relative clauses under past except in Japanese, is described by
the rows. The typology of Tables 1 and 2 is the rows: under past the present shifts in
attitude reports in Greek, Hebrew, Russian and Japanese, in relative clauses only in
Japanese, and never in English, whose present under past indicates the utterance time; under
future it shifts everywhere, WOLL binding the index, and only English admits ⌈then⌉ there,
its present being deleted under WOLL's PRES rather than shifted, a difference among
sequence-of-tense languages the paper leaves open, (94)–(97). Japanese *tōji* is
past-oriented, (32). The perspective is not the context's time, since Greek shifts the
present but never *tora* 'now', (99). The examples are the rows of
`Data.Examples.TsiliaZhao2026`.

## References

* [tsilia-zhao-2026]
* [zhao-2025]
* [ogihara-sharvit-2012]
* [anand-nevins-2004]
* [deal-2020]
* [abusch-1988]
* [heim-1992]
-/

namespace TsiliaZhao2026

open Tense.Perspective

variable {T : Type*}

/-! ### The clash and the shift-together effect (section 5) -/

/-- (77): the presuppositions of a present-tensed clause restricted by ⌈then⌉, as a function
of the perspective: the reference `r` of PRES overlaps `π`, ⌈then⌉'s reference `th` contains
it, and `th` is disjoint from `π`. -/
def presThen (r th π : Set T) : Prop := presPresup π r ∧ r ⊆ th ∧ thenPresup π th

/-- OP_π rebinds the perspective of PRES and ⌈then⌉ at once, so the clause is contradictory
whatever the perspective: the root case (75), the shifted case (78) and the future cases
(81)–(82) alike. -/
theorem not_presThen (r th π : Set T) : ¬ presThen r th π :=
  λ ⟨hp, hd, ht⟩ => then_present_clash hp hd ht

/-- (36): with pronominal anchors, PRES and ⌈then⌉ could be anchored to different times and
the clause would be coherent, which is why the anchor is a parameter. -/
theorem exists_split_anchor {π₁ π₂ : Set T} (h : ¬ Overlaps π₁ π₂)
    (hne : π₁.Nonempty) :
    ∃ r th : Set T, presPresup π₁ r ∧ r ⊆ th ∧ thenPresup π₂ th :=
  ⟨π₁, π₁, by simpa [presPresup, Overlaps] using hne, subset_rfl, h⟩

/-! ### Past and deleted tense (sections 3 and 6) -/

/-- The presuppositions of a past-tensed clause restricted by ⌈then⌉. -/
def pastThen [LT T] (r th π : Set T) : Prop := pastPresup π r ∧ r ⊆ th ∧ thenPresup π th

/-- (38), (39), (44): a PAST admits ⌈then⌉ at its own reference. -/
theorem pastThen_self [Preorder T] {r π : Set T} (h : pastPresup π r) : pastThen r r π :=
  ⟨h, subset_rfl, thenPresup_of_pastPresup h⟩

/-- (89): a deleted tense carries no presupposition, so only ⌈then⌉'s remains. -/
def deletedThen (r th π : Set T) : Prop := r ⊆ th ∧ thenPresup π th

/-- (89a): with no OP_π the perspective stays the utterance time, from which the reported
meeting is disjoint, and ⌈then⌉ restricts the deleted past. -/
theorem deletedThen_of_not_overlaps {r π : Set T} (h : ¬ Overlaps r π) : deletedThen r r π :=
  ⟨subset_rfl, h⟩

/-- (89b): with OP_π shifting the perspective onto the time of the reported speech, within
which the meeting time lies, ⌈then⌉ can no longer restrict it. -/
theorem not_deletedThen_of_subset {r th π : Set T} (hr : r ⊆ π) (hne : r.Nonempty) :
    ¬ deletedThen r th π :=
  λ ⟨hd, ht⟩ =>
    ht ((show Overlaps r π from ⟨hne.some, hne.some_mem, hr hne.some_mem⟩).mono_left hd)

end TsiliaZhao2026
