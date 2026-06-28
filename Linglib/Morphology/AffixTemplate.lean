import Linglib.Morphology.MorphRule

/-!
# Affix position-class templates

A language's verb (or word) affix template: the ordered morpheme-category slots
of its prefix and suffix strings. This is the per-language, Fragment-importable
substrate that `RespectsRelevanceHierarchy` (in `Morphology/MorphRule.lean`)
tests against [bybee-1985]'s relevance hierarchy — so a language's slot order
lives once, as Fragment data, and study files derive their checks from it rather
than re-typing the template.

## Main definitions

* `Morphology.AffixTemplate` — a language's prefix/suffix slots as `MorphCategory` lists.
* `Morphology.AffixTemplate.suffixRespectsRelevance` — the suffix slots are sorted by relevance.
-/

namespace Morphology

/-- A language's affix position-class template. `suffixSlots` runs stem-outward
(innermost suffix first); `prefixSlots` is listed as the source grammar writes
it, word-edge inward. Slots are `MorphCategory` tags, not exponents — the actual
morphemes live in the citing grammar. -/
structure AffixTemplate where
  /-- Suffix slots, ordered stem-outward (innermost suffix first). -/
  suffixSlots : List MorphCategory := []
  /-- Prefix slots, ordered word-edge inward (outermost prefix first). -/
  prefixSlots : List MorphCategory := []
  deriving Repr, DecidableEq

/-- The template's suffix order respects [bybee-1985]'s relevance hierarchy. -/
def AffixTemplate.suffixRespectsRelevance (t : AffixTemplate) : Prop :=
  RespectsRelevanceHierarchy t.suffixSlots

instance (t : AffixTemplate) : Decidable t.suffixRespectsRelevance :=
  inferInstanceAs (Decidable (RespectsRelevanceHierarchy _))

end Morphology
