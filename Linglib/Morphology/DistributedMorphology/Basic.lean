module

public import Linglib.Morphology.DistributedMorphology.Defs
public import Linglib.Morphology.Exponence.Select
public import Mathlib.Data.Finset.Card

/-!
# Vocabulary items as exponence rules

A `VocabularyItem` exposes the shared exponence interface
(`Morphology.Exponence.Rule`) over neighborhoods: it applies where its
site is included in the neighborhood, and its specificity, the features it
puts on the terminal and then those it puts on the context, is strictly
antitone in the engine's order, so score selection is Elsewhere selection.
-/

@[expose] public section

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
