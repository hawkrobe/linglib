import Linglib.Morphology.MorphRule

/-!
# Templates: word-skeletal morphotactic substrate

A **template** stipulates a word's positional skeleton directly — the
word-skeletal answer to where affix order comes from, rival to the
rule-combining answer on which templates are emergent patterns of rule
composition ([stump-2022]). `AffixTemplate` is the position-class species
(a prosodic/CV species would be its sibling); the rivalry itself is study
content, not settled here.

A word's affix template: the ordered position-class slots of its prefix and
suffix strings, parameterized by the slot type `Slot`. Instantiating at
`MorphCategory` gives a language's slot order as Fragment-importable substrate
that `RespectsRelevanceHierarchy` (in `Morphology/MorphRule.lean`) tests against
[bybee-1985]'s relevance hierarchy — so the order lives once, as Fragment data,
and study files derive their checks from it rather than re-typing the template.
Instantiating at a language-specific slot type carries finer position classes:
`Mayan.template` uses `Mayan.VerbSlot`, with the prefix/suffix split encoding a
morpheme's position relative to the verb stem.

## Main definitions

* `Morphology.AffixTemplate` — a word's prefix/suffix slots over an arbitrary slot type.
* `Morphology.AffixTemplate.suffixRespectsRelevance` — the `MorphCategory` suffix slots are sorted by relevance.
-/

namespace Morphology

/-- A word's affix position-class template. `suffixSlots` runs stem-outward
(innermost suffix first); `prefixSlots` is listed as the source grammar writes
it, word-edge inward. Slots are `Slot` tags, not exponents — the actual
morphemes live in the citing grammar. -/
structure AffixTemplate (Slot : Type*) where
  /-- Prefix slots, ordered word-edge inward (outermost prefix first). -/
  prefixSlots : List Slot := []
  /-- Suffix slots, ordered stem-outward (innermost suffix first). -/
  suffixSlots : List Slot := []
  deriving Repr, DecidableEq

/-- The template's suffix order respects [bybee-1985]'s relevance hierarchy. -/
def AffixTemplate.suffixRespectsRelevance (t : AffixTemplate MorphCategory) : Prop :=
  RespectsRelevanceHierarchy t.suffixSlots

instance (t : AffixTemplate MorphCategory) : Decidable t.suffixRespectsRelevance :=
  inferInstanceAs (Decidable (RespectsRelevanceHierarchy _))

end Morphology
