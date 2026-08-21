import Linglib.Morphology.DistributedMorphology.Basic
import Linglib.Morphology.Exponence.Select

/-!
# Vocabulary insertion

Vocabulary Insertion is the operation that supplies syntactic terminals with
phonological exponents in Distributed Morphology: the Vocabulary Items of
List 2 compete for insertion at each terminal, and the Subset Principle of
[halle-marantz-1993] picks the item whose feature specification is the
largest subset of the terminal's bundle. This file specializes the shared
exponence engine (`Morphology.Exponence.selectBy`) to that competition.

## Main definitions

* `winner?`, `subsetPrinciple`: the Subset Principle's winning item and its
  exponent.

## Main results

* `winner?_isElsewhereWinner`: the winner is an Elsewhere winner of the
  shared core, with no faithfulness hypothesis — over feature
  specifications the engine's specificity order is reverse feature
  inclusion (`VocabularyItem.le_iff`).
* `winner?_retreat`: deleting features from the target can only make the
  winner less specific — retreat to the general case.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
-/

namespace DistributedMorphology

open Morphology.Exponence

/-! ### The Subset Principle -/

section SubsetPrinciple

variable {F E : Type*} [DecidableEq F] {items : List (VocabularyItem F E)} {t t' : List F}
  {i i' : VocabularyItem F E} {e : E}

/-- The Subset Principle's winning item: the applicable item of greatest
`specificity` (the earliest, under ties). -/
def winner? (items : List (VocabularyItem F E)) (t : List F) : Option (VocabularyItem F E) :=
  selectBy VocabularyItem.specificity items t

/-- The **Subset Principle** ([halle-marantz-1993]): the exponent of the most
specific item whose features the target bears; `none` iff no item applies. -/
def subsetPrinciple (items : List (VocabularyItem F E)) (t : List F) : Option E :=
  realize VocabularyItem.specificity items t

theorem winner?_mem (h : winner? items t = some i) : i ∈ applicable items t :=
  List.argmax_mem h

theorem winner?_spec (h : winner? items t = some i) : i ∈ items ∧ i.features ⊆ t :=
  mem_applicable.mp (winner?_mem h)

/-- The Subset Principle's exponent comes from an applicable item — the
selection never draws on features the node does not bear. -/
theorem subsetPrinciple_winner_mem (h : subsetPrinciple items t = some e) :
    ∃ i ∈ items, i.exponent = e ∧ i.features ⊆ t := by
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨i, (winner?_spec hi).1, rfl, (winner?_spec hi).2⟩

theorem winner?_isSome_iff : (winner? items t).isSome ↔ applicable items t ≠ [] := by
  rw [Option.isSome_iff_ne_none]; exact not_congr selectBy_eq_none_iff

theorem winner?_max (h : winner? items t = some i) :
    ∀ j ∈ applicable items t, j.specificity ≤ i.specificity :=
  fun _ hj => List.le_of_mem_argmax hj h

/-- The winner is an Elsewhere winner of the shared core — with no
faithfulness hypothesis, since `VocabularyItem.specificity` is strictly
antitone outright. -/
theorem winner?_isElsewhereWinner (h : winner? items t = some i) : IsElsewhereWinner items t i :=
  selectBy_isElsewhereWinner (VocabularyItem.specificity_strictAnti.strictAntiOn _) h

theorem subsetPrinciple_realizes (h : subsetPrinciple items t = some e) : Realizes items t e :=
  realize_realizes (VocabularyItem.specificity_strictAnti.strictAntiOn _) h

/-- Applicability is monotone in the target bundle. -/
theorem applicable_mono (hsub : t' ⊆ t) : applicable items t' ⊆ applicable items t :=
  fun _ hi => mem_applicable.mpr
    ⟨(mem_applicable.mp hi).1, List.Subset.trans (mem_applicable.mp hi).2 hsub⟩

/-- **Retreat to the general case**: shrinking the target — deleting features
by Impoverishment — can only make the winner weakly less specific, which is
why impoverishment yields syncretism with a more general exponent rather than
a different specific one ([halle-marantz-1993], [arregi-nevins-2012]). -/
theorem winner?_retreat (hsub : t' ⊆ t) (h' : winner? items t' = some i') :
    ∃ i, winner? items t = some i ∧ i'.specificity ≤ i.specificity := by
  have hmem := applicable_mono hsub (winner?_mem h')
  obtain ⟨i, hi⟩ :=
    Option.isSome_iff_exists.mp (winner?_isSome_iff.mpr (List.ne_nil_of_mem hmem))
  exact ⟨i, hi, winner?_max hi _ hmem⟩

end SubsetPrinciple

end DistributedMorphology
