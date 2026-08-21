import Linglib.Morphology.DistributedMorphology.Basic
import Linglib.Morphology.Exponence.Select

/-!
# Vocabulary insertion

Vocabulary Insertion supplies syntactic terminals with phonological
exponents: the Vocabulary Items of List 2 compete for insertion at each
terminal, and the Subset Principle of [halle-marantz-1993] picks the item
whose specification is the largest one the terminal's neighborhood contains —
its own features and, for a contextual item, the features of the adjacent
terminals. This file specializes the shared exponence engine
(`Morphology.Exponence.selectBy`) to that competition.

## Main definitions

* `winner?`, `subsetPrinciple`: the Subset Principle's winning item and its
  exponent.

## Main results

* `winner?_isElsewhereWinner`: the winner is an Elsewhere winner of the
  shared core, with no faithfulness hypothesis — the engine's specificity
  order is reverse inclusion of specifications (`VocabularyItem.le_iff`).
* `winner?_retreat`: deleting features from the neighborhood can only make
  the winner less specific — retreat to the general case.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
-/

namespace DistributedMorphology

open Morphology.Exponence

/-! ### The Subset Principle -/

section SubsetPrinciple

variable {F E : Type*} [DecidableEq F] {items : List (VocabularyItem F E)}
  {n n' : Neighborhood (List F)} {i i' : VocabularyItem F E} {e : E}

/-- The Subset Principle's winning item: the applicable item of greatest
`specificity` (the earliest, under ties). -/
def winner? (items : List (VocabularyItem F E)) (n : Neighborhood (List F)) :
    Option (VocabularyItem F E) :=
  selectBy VocabularyItem.specificity items n

/-- The **Subset Principle** ([halle-marantz-1993]): the exponent of the most
specific item whose specification the neighborhood contains; `none` iff no
item applies. -/
def subsetPrinciple (items : List (VocabularyItem F E)) (n : Neighborhood (List F)) : Option E :=
  realize VocabularyItem.specificity items n

theorem winner?_mem (h : winner? items n = some i) : i ∈ applicable items n :=
  List.argmax_mem h

theorem winner?_spec (h : winner? items n = some i) : i ∈ items ∧ i.spec ⊆ n :=
  mem_applicable.mp (winner?_mem h)

/-- The Subset Principle's exponent comes from an applicable item — the
selection never draws on features the neighborhood does not bear. -/
theorem subsetPrinciple_winner_mem (h : subsetPrinciple items n = some e) :
    ∃ i ∈ items, i.exponent = e ∧ i.spec ⊆ n := by
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨i, (winner?_spec hi).1, rfl, (winner?_spec hi).2⟩

theorem winner?_isSome_iff : (winner? items n).isSome ↔ applicable items n ≠ [] := by
  rw [Option.isSome_iff_ne_none]; exact not_congr selectBy_eq_none_iff

theorem winner?_max (h : winner? items n = some i) :
    ∀ j ∈ applicable items n, j.specificity ≤ i.specificity :=
  fun _ hj => List.le_of_mem_argmax hj h

/-- The winner is an Elsewhere winner of the shared core — with no
faithfulness hypothesis, since `VocabularyItem.specificity` is strictly
antitone outright. -/
theorem winner?_isElsewhereWinner (h : winner? items n = some i) : IsElsewhereWinner items n i :=
  selectBy_isElsewhereWinner (VocabularyItem.specificity_strictAnti.strictAntiOn _) h

theorem subsetPrinciple_realizes (h : subsetPrinciple items n = some e) : Realizes items n e :=
  realize_realizes (VocabularyItem.specificity_strictAnti.strictAntiOn _) h

/-- Applicability is monotone in the neighborhood. -/
theorem applicable_mono (hsub : n' ⊆ n) : applicable items n' ⊆ applicable items n :=
  fun _ hi => mem_applicable.mpr
    ⟨(mem_applicable.mp hi).1, Neighborhood.Subset.trans (mem_applicable.mp hi).2 hsub⟩

/-- **Retreat to the general case**: shrinking the neighborhood — deleting
features by Impoverishment — can only make the winner weakly less specific,
which is why impoverishment yields syncretism with a more general exponent
rather than a different specific one ([halle-marantz-1993],
[arregi-nevins-2012]). -/
theorem winner?_retreat (hsub : n' ⊆ n) (h' : winner? items n' = some i') :
    ∃ i, winner? items n = some i ∧ i'.specificity ≤ i.specificity := by
  have hmem := applicable_mono hsub (winner?_mem h')
  obtain ⟨i, hi⟩ :=
    Option.isSome_iff_exists.mp (winner?_isSome_iff.mpr (List.ne_nil_of_mem hmem))
  exact ⟨i, hi, winner?_max hi _ hmem⟩

end SubsetPrinciple

end DistributedMorphology
