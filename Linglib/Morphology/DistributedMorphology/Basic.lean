import Linglib.Morphology.DistributedMorphology.Defs
import Linglib.Morphology.Exponence.Select
import Mathlib.Data.Finset.Card

/-!
# Vocabulary items as exponence rules

A `VocabularyItem` exposes the shared exponence interface
(`Morphology.Exponence.Rule`) over neighborhoods: it applies where its
specification is included in the neighborhood, and its specificity — the
number of positioned features it mentions — is strictly antitone in the
engine's order, so score selection is Elsewhere selection.
-/

namespace DistributedMorphology.VocabularyItem

open Morphology.Exponence

variable {F E : Type*} {i j : VocabularyItem F E} {n : Neighborhood (List F)}

/-- A Vocabulary Item exposes the shared exponence interface: contexts are
neighborhoods, applicability is inclusion of the specification. -/
instance : Rule (VocabularyItem F E) (Neighborhood (List F)) E := ⟨exponent, fun i n => i.spec ⊆ n⟩

instance : Preorder (VocabularyItem F E) := toPreorder

theorem applies_iff : Applies i n ↔ i.spec ⊆ n := Iff.rfl

/-- The Elsewhere item applies at every neighborhood. -/
theorem elsewhere_applies (e : E) (n : Neighborhood (List F)) :
    Applies (⟨∅, e⟩ : VocabularyItem F E) n :=
  List.nil_subset _

theorem le_iff_applies : i ≤ j ↔ ∀ ⦃n : Neighborhood (List F)⦄, i.spec ⊆ n → j.spec ⊆ n :=
  Iff.rfl

/-- The engine's specificity order is reverse inclusion of specifications. -/
theorem le_iff : i ≤ j ↔ j.spec ⊆ i.spec :=
  ⟨fun h => le_iff_applies.mp h (Neighborhood.Subset.refl _),
    fun h => le_iff_applies.mpr fun _ hn => Neighborhood.Subset.trans h hn⟩

variable [DecidableEq F]

instance : DecidableRel (Applies : VocabularyItem F E → Neighborhood (List F) → Prop) :=
  fun i n => inferInstanceAs (Decidable (i.spec ⊆ n))

/-- The number of distinct positioned features an item mentions — the
Subset Principle's specificity score. -/
def specificity (i : VocabularyItem F E) : ℕ := i.spec.positioned.toFinset.card

theorem toFinset_subset_toFinset :
    i.spec.positioned.toFinset ⊆ j.spec.positioned.toFinset ↔ i.spec ⊆ j.spec :=
  Multiset.toFinset_subset.trans Multiset.coe_subset

theorem specificity_strictAnti : StrictAnti (specificity : VocabularyItem F E → ℕ) :=
  fun _ _ h => Finset.card_lt_card <| Finset.ssubset_def.mpr
    ⟨toFinset_subset_toFinset.mpr (le_iff.mp h.le),
      fun hc => (lt_iff_le_not_ge.mp h).2 (le_iff.mpr (toFinset_subset_toFinset.mp hc))⟩

end DistributedMorphology.VocabularyItem
