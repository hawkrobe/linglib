import Mathlib.Tactic.TypeStar

/-!
# Templates: word-skeletal morphotactic substrate

A **template** stipulates a word's positional skeleton directly — the
word-skeletal answer to where affix order comes from, rival to the
rule-combining answer on which templates are emergent patterns of rule
composition ([stump-2022]). The layered-vs-templatic *typological*
contrast and its diagnostics (long-distance slot dependencies,
non-functional slot assignment) are [bickel-nichols-2007] §6, with the
caveat that templatic vs layered properties "are likely to hold of
individual formatives rather than of the entire string" (p. 219).
`AffixTemplate` is the position-class species (a prosodic/CV species
would be its sibling); the rivalry itself is study content, not settled
here.

A word's affix template: the ordered position-class slots of its prefix and
suffix strings, parameterized by the slot type `Slot` — so the order lives
once, as Fragment data, and study files derive their checks from it rather
than re-typing the template. Instantiating at `MorphCategory` gives a
language's slot order in relevance-hierarchy vocabulary
(`AffixTemplate.suffixRespectsRelevance`, in
`Morphology/RelevanceHierarchy.lean`); a language-specific slot type carries
finer position classes: `Mayan.template` uses `Mayan.VerbSlot`, with the
prefix/suffix split encoding a morpheme's position relative to the verb stem.

## Main definitions

* `Morphology.AffixTemplate` — a word's prefix/suffix slots over an arbitrary slot type.
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

end Morphology
