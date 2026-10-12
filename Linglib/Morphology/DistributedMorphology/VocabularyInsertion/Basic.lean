module

public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.Exponence.Select

/-!
# Vocabulary insertion

Vocabulary Insertion supplies syntactic terminals with phonological exponents: the Vocabulary
Items of List 2 compete for insertion at each terminal, and the Subset Principle picks the item
whose site is the largest one the terminal's neighborhood contains, its own features and, for a
contextual item, the features of the adjacent terminals. The competition is the shared
exponence engine's selection by specificity, so it inherits that engine's laws. Impoverishment
changes the winner only by deleting a feature the winning item mentions, and an antihomophonous
vocabulary realizes no ABA pattern across nested neighborhoods.

## Main definitions

* `winner?`, `subsetPrinciple`: the Subset Principle's winning item and its exponent.

## Main results

* `winner?_isElsewhereWinner`: the winner is an Elsewhere winner of the shared core.
* `winner?_eq_of_subset`: deleting features the winner does not mention leaves the winner.
* `winner?_retreat`: deleting features from the neighborhood can only make the winner less
  specific, retreat to the general case.
* `isContiguous_subsetPrinciple`: an antihomophonous vocabulary realizes contiguous patterns
  over neighborhoods ordered by inclusion.

## References

* [halle-marantz-1993]
* [arregi-nevins-2012]
-/

@[expose] public section

namespace DistributedMorphology

open Morphology.Exponence

/-! ### The Subset Principle -/

section SubsetPrinciple

variable {F E : Type*} [DecidableEq F] {items : List (VocabularyItem F E)}
  {n n' : Neighborhood (List F)} {i i' : VocabularyItem F E} {e : E}

/-- The Subset Principle's winning item is the applicable item of greatest `specificity`, the
earliest under ties. -/
def winner? (items : List (VocabularyItem F E)) (n : Neighborhood (List F)) :
    Option (VocabularyItem F E) :=
  selectBy VocabularyItem.specificity items n

/-- The **Subset Principle** yields the exponent of the most specific item whose site the
neighborhood contains, and `none` iff no item applies. -/
def subsetPrinciple (items : List (VocabularyItem F E)) (n : Neighborhood (List F)) : Option E :=
  realize VocabularyItem.specificity items n

/-- The Subset Principle's exponent comes from an applicable item, so the selection never draws on
features the neighborhood does not bear. -/
theorem subsetPrinciple_winner_mem (h : subsetPrinciple items n = some e) :
    ∃ i ∈ items, i.exponent = e ∧ i.site ⊆ n := by
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨i, selectBy_mem hi, rfl, selectBy_applies hi⟩

theorem winner?_isSome_iff : (winner? items n).isSome ↔ ∃ i ∈ items, i.site ⊆ n :=
  selectBy_isSome_iff

/-- The winner is an Elsewhere winner of the shared core, with no faithfulness hypothesis, since
`VocabularyItem.specificity` is strictly antitone outright. -/
theorem winner?_isElsewhereWinner (h : winner? items n = some i) : IsElsewhereWinner items n i :=
  selectBy_isElsewhereWinner (VocabularyItem.specificity_strictAnti.strictAntiOn _) h

theorem subsetPrinciple_realizes (h : subsetPrinciple items n = some e) : Realizes items n e :=
  realize_realizes (VocabularyItem.specificity_strictAnti.strictAntiOn _) h

/-- Impoverishment that deletes only features the winning item does not mention leaves the winner
in place, since every item applicable after the deletion was applicable before it. -/
theorem winner?_eq_of_subset (hsub : n' ⊆ n) (h : winner? items n = some i) (hi : i.site ⊆ n') :
    winner? items n' = some i :=
  selectBy_eq_some_of_applies (fun _ _ hs ↦ hs.trans hsub) h hi

/-- **Retreat to the general case.** Shrinking the neighborhood, deleting features by
Impoverishment, can only make the winner weakly less specific, which is why impoverishment yields
syncretism with a more general exponent rather than a different specific one. -/
theorem winner?_retreat (hsub : n' ⊆ n) (h' : winner? items n' = some i') :
    ∃ i, winner? items n = some i ∧ i'.specificity ≤ i.specificity := by
  have hi' : i'.site ⊆ n := (selectBy_applies h').trans hsub
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (winner?_isSome_iff.mpr ⟨i', selectBy_mem h', hi'⟩)
  exact ⟨i, hi, le_of_selectBy_eq_some hi (selectBy_mem h') hi'⟩

/-- An antihomophonous vocabulary realizes no ABA pattern over neighborhoods ordered by inclusion:
an exponent inserted at two nested neighborhoods is inserted at every neighborhood between
them. -/
theorem isContiguous_subsetPrinciple (hv : Antihomophonous items) :
    Morphology.IsContiguous (subsetPrinciple items) :=
  isContiguous_realize_of_monotone hv fun _ _ _ _ hn hs ↦ hs.trans hn

end SubsetPrinciple

end DistributedMorphology
