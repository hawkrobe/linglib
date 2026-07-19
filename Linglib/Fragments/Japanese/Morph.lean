import Linglib.Morphology.Morphotactics.RelevanceHierarchy
import Linglib.Morphology.Morphotactics.Template

/-!
# Japanese Verb Suffix Template
[kaiser-yamamoto-2013]

The Japanese verb suffix template over Japanese's own slot inventory
(`VerbSlot`), following [kaiser-yamamoto-2013] and the UD segmentation:
seven slots, stem-outward. The comparison into [bybee-1985]'s inventory
is the hom `VerbSlot.toMorphCategory` — the analytical commitments
(politeness as subject agreement, desiderative as mood) live in the hom,
not in the slot data; `verbAffixTemplate` is the derived image.

| Slot | VerbSlot | Morpheme |
|------|----------|----------|
| 1 | derivation | -su (suru) |
| 2 | valence | -(s)ase (causative) |
| 3 | voice | -are, -rare (passive/potential) |
| 4 | desiderative | -ta |
| 5 | politeness | -mas |
| 6 | negation | -na |
| 7 | tense | -ta (past), -yoo (future) |
-/

namespace Japanese

open Morphology

/-- Japanese verb suffix slots, language-owned ([kaiser-yamamoto-2013],
UD segmentation). -/
inductive VerbSlot where
  | derivation   -- -su (suru)
  | valence      -- -(s)ase (causative)
  | voice        -- -are, -rare (passive/potential)
  | desiderative -- -ta
  | politeness   -- -mas
  | negation     -- -na
  | tense        -- -ta (past), -yoo (future)
  deriving DecidableEq, Repr

/-- The verb suffix template over Japanese's own slots, stem-outward.
Japanese is strongly suffixing, so there are no prefix slots. -/
def verbTemplate : AffixTemplate VerbSlot where
  suffixSlots :=
    [.derivation, .valence, .voice, .desiderative, .politeness, .negation, .tense]

/-- The comparison hom into [bybee-1985]'s inventory. The analytical
commitments are here, explicitly: `politeness ↦ agreement .subj`
(politeness *-mas* treated as subject agreement, per
[kaiser-yamamoto-2013]'s segmentation) and `desiderative ↦ mood`. -/
def VerbSlot.toMorphCategory : VerbSlot → MorphCategory
  | .derivation   => .derivation
  | .valence      => .valence
  | .voice        => .voice
  | .desiderative => .mood
  | .politeness   => .agreement .subj
  | .negation     => .negation
  | .tense        => .tense

/-- The template in comparative-concept vocabulary: the image of
`verbTemplate` under `VerbSlot.toMorphCategory`. Derived, not
stipulated. -/
def verbAffixTemplate : AffixTemplate MorphCategory where
  suffixSlots := verbTemplate.suffixSlots.map VerbSlot.toMorphCategory

end Japanese
