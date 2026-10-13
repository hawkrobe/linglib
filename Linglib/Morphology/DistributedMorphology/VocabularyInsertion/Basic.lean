module

public import Linglib.Morphology.DistributedMorphology.Neighborhood
public import Linglib.Morphology.Exponence.Select
public import Mathlib.Data.Finset.Card

/-!
# Vocabulary Insertion

A Vocabulary Item pairs its insertion site with the exponent that realizes it: the features of the
terminal it spells out, together with the features it requires of the neighboring terminals, its
contextual environment `/ __ ]X]`. Form and meaning share the type, an alloseme being an item whose
exponent is a denotation (`DistributedMorphology/Allosemy.lean`). The items of List 2 compete for
insertion at each terminal, and the Subset Principle picks the item whose site is the largest one
the terminal's neighborhood contains. The competition is the shared exponence engine's selection by
specificity, so it inherits that engine's laws: Impoverishment changes the winner only by deleting
a feature the winning item mentions, and an antihomophonous vocabulary realizes no ABA pattern
across nested neighborhoods.

## Main definitions

* `DistributedMorphology.VocabularyItem`: a site and its exponent.
* `DistributedMorphology.VocabularyItem.specificity`: the features an item puts on its terminal,
  then those it puts on the context.
* `DistributedMorphology.winner?`, `DistributedMorphology.subsetPrinciple`: the Subset
  Principle's winning item and its exponent.

## Main statements

* `DistributedMorphology.winner?_isElsewhereWinner`: the winner is an Elsewhere winner of the
  shared core.
* `DistributedMorphology.winner?_retreat`: deleting features from the neighborhood can only make
  the winner less specific, retreat to the general case.
* `DistributedMorphology.isContiguous_subsetPrinciple`: an antihomophonous vocabulary realizes
  contiguous patterns over neighborhoods ordered by inclusion.

## References

* [halle-marantz-1993]
* [halle-1997]
* [mcginnis-2013]
* [arregi-nevins-2012]
-/

@[expose] public section

namespace DistributedMorphology

/-- A Vocabulary Item pairs the site it is inserted at, the features it spells out and those it
requires of the adjacent terminals, with its exponent, and applies at any neighborhood containing
every feature it mentions. -/
structure VocabularyItem (F E : Type*) where
  /-- The features the item spells out, with those it requires of the
  adjacent terminals. -/
  site : Neighborhood (List F)
  /-- The exponent the item inserts. -/
  exponent : E
  deriving DecidableEq, Repr

variable {F E : Type*}

namespace VocabularyItem

/-- The features the item spells out at its own terminal. -/
def features (i : VocabularyItem F E) : List F := i.site.focus

/-- A context-free item: the features it spells out and its exponent. -/
def ofFeatures (fs : List F) (e : E) : VocabularyItem F E := ⟨fs, e⟩

end VocabularyItem

/-- `fs ⟷ e` is the context-free Vocabulary Item spelling out `fs` as `e`. -/
scoped infixr:25 " ⟷ " => VocabularyItem.ofFeatures

namespace VocabularyItem

@[simp] theorem site_ofFeatures (fs : List F) (e : E) : (fs ⟷ e).site = ↑fs := rfl

@[simp] theorem exponent_ofFeatures (fs : List F) (e : E) : (fs ⟷ e).exponent = e := rfl

end VocabularyItem

end DistributedMorphology

namespace DistributedMorphology.VocabularyItem

open Morphology.Exponence

variable {F E : Type*} {i j : VocabularyItem F E} {n : Neighborhood (List F)}

/-- A Vocabulary Item exposes the shared exponence interface, its contexts neighborhoods and its
applicability inclusion of its site. -/
instance : Rule (VocabularyItem F E) (Neighborhood (List F)) E := ⟨exponent, fun i n => i.site ⊆ n⟩

instance : Preorder (VocabularyItem F E) := toPreorder

theorem applies_iff : Applies i n ↔ i.site ⊆ n := Iff.rfl

/-- The Elsewhere item applies at every neighborhood. -/
theorem elsewhere_applies (e : E) (n : Neighborhood (List F)) :
    Applies (⟨∅, e⟩ : VocabularyItem F E) n :=
  Neighborhood.empty_subset n

theorem le_iff_applies : i ≤ j ↔ ∀ ⦃n : Neighborhood (List F)⦄, i.site ⊆ n → j.site ⊆ n :=
  Iff.rfl

/-- The engine's specificity order is reverse inclusion of sites. -/
theorem le_iff : i ≤ j ↔ j.site ⊆ i.site :=
  ⟨fun h ↦ le_iff_applies.mp h subset_rfl, fun h ↦ le_iff_applies.mpr fun _ hn ↦ h.trans hn⟩

/-- A strictly more specific item has a strictly larger site. -/
theorem site_strictAnti : StrictAnti (site : VocabularyItem F E → Neighborhood (List F)) :=
  strictAnti_of_le_iff_le fun _ _ ↦ le_iff

variable [DecidableEq F]

instance : DecidableRel (Applies : VocabularyItem F E → Neighborhood (List F) → Prop) :=
  fun i n => inferInstanceAs (Decidable (i.site ⊆ n))

/-- An item's specificity counts the distinct features its site puts on the terminal, then those
it puts on the context: the terminal's features decide, as the Subset Principle chooses the item
matching most of them ([halle-1997]), and context breaks ties ([mcginnis-2013]). -/
def specificity (i : VocabularyItem F E) : ℕ ×ₗ ℕ := i.site.weight

theorem specificity_strictAnti : StrictAnti (specificity : VocabularyItem F E → ℕ ×ₗ ℕ) :=
  Neighborhood.weight_strictMono.comp_strictAnti site_strictAnti

/-- No item is less specific than an Elsewhere item. -/
@[simp] theorem not_specificity_lt_elsewhere (i : VocabularyItem F E) (e : E) :
    ¬ i.specificity < (ofFeatures ([] : List F) e).specificity :=
  Neighborhood.not_weight_lt_empty i.site

end DistributedMorphology.VocabularyItem

namespace DistributedMorphology

open Morphology.Exponence

/-! ### The Subset Principle -/

section SubsetPrinciple

variable {F E : Type*} [DecidableEq F] {items : RuleSet (VocabularyItem F E)}
  {n n' : Neighborhood (List F)} {i i' : VocabularyItem F E} {e : E}

/-- The Subset Principle's winning item is the applicable item of greatest `specificity`, the
earliest under ties. -/
def winner? (items : RuleSet (VocabularyItem F E)) (n : Neighborhood (List F)) :
    Option (VocabularyItem F E) :=
  items.selectBy VocabularyItem.specificity n

/-- The **Subset Principle** yields the exponent of the most specific item whose site the
neighborhood contains, and `none` iff no item applies. -/
def subsetPrinciple (items : RuleSet (VocabularyItem F E)) (n : Neighborhood (List F)) :
    Option E :=
  items.realize VocabularyItem.specificity n

/-- The Subset Principle's exponent comes from an applicable item, so the selection never draws on
features the neighborhood does not bear. -/
theorem subsetPrinciple_winner_mem (h : subsetPrinciple items n = some e) :
    ∃ i ∈ items, i.exponent = e ∧ i.site ⊆ n := by
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨i, RuleSet.selectBy_mem hi, rfl, RuleSet.selectBy_applies hi⟩

theorem winner?_isSome_iff : (winner? items n).isSome ↔ ∃ i ∈ items, i.site ⊆ n :=
  RuleSet.selectBy_isSome_iff

/-- The winner is an Elsewhere winner of the shared core, with no faithfulness hypothesis, since
`VocabularyItem.specificity` is strictly antitone outright. -/
theorem winner?_isElsewhereWinner (h : winner? items n = some i) : items.IsElsewhereWinner n i :=
  RuleSet.selectBy_isElsewhereWinner (VocabularyItem.specificity_strictAnti.strictAntiOn _) h

theorem subsetPrinciple_realizes (h : subsetPrinciple items n = some e) : items.Realizes n e :=
  RuleSet.realize_realizes (VocabularyItem.specificity_strictAnti.strictAntiOn _) h

/-- Impoverishment that deletes only features the winning item does not mention leaves the winner
in place, since every item applicable after the deletion was applicable before it. -/
theorem winner?_eq_of_subset (hsub : n' ⊆ n) (h : winner? items n = some i) (hi : i.site ⊆ n') :
    winner? items n' = some i :=
  RuleSet.selectBy_eq_some_of_applies (fun _ _ hs ↦ hs.trans hsub) h hi

/-- **Retreat to the general case.** Shrinking the neighborhood, deleting features by
Impoverishment, can only make the winner weakly less specific, which is why impoverishment yields
syncretism with a more general exponent rather than a different specific one. -/
theorem winner?_retreat (hsub : n' ⊆ n) (h' : winner? items n' = some i') :
    ∃ i, winner? items n = some i ∧ i'.specificity ≤ i.specificity := by
  have hi' : i'.site ⊆ n := (RuleSet.selectBy_applies h').trans hsub
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp
    (winner?_isSome_iff.mpr ⟨i', RuleSet.selectBy_mem h', hi'⟩)
  exact ⟨i, hi, RuleSet.le_of_selectBy_eq_some hi (RuleSet.selectBy_mem h') hi'⟩

/-- An antihomophonous vocabulary realizes no ABA pattern over neighborhoods ordered by inclusion:
an exponent inserted at two nested neighborhoods is inserted at every neighborhood between
them. -/
theorem isContiguous_subsetPrinciple (hv : items.Antihomophonous) :
    Morphology.IsContiguous (subsetPrinciple items) :=
  RuleSet.isContiguous_realize_of_monotone hv fun _ _ _ _ hn hs ↦ hs.trans hn

end SubsetPrinciple

end DistributedMorphology
