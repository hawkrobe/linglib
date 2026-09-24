module

public import Linglib.Morphology.Morphotactics.RelevanceHierarchy
public import Linglib.Morphology.Morphotactics.Template

/-!
# Japanese verb suffix template

The Japanese verb suffixes in their order from the stem outward, over Japanese's own slots
(`VerbSlot`), following [kaiser-yamamoto-2013] and the UD segmentation: a derivational *-su*
(*suru*), the causative *-(s)ase*, the passive and potential *-(r)are*, the desiderative
*-ta(i)*, the polite *-mas*, the negative *-na* and the tense endings, non-past *-(r)u* and past
*-ta*. The hortative *-(y)oo* stands where the tense endings do but is a mood ending, not a tense
([narrog-2010b]), and is not entered. The comparison into [bybee-1985]'s inventory is the hom
`VerbSlot.toMorphCategory`; its analytical commitments, politeness as subject agreement and the
desiderative as mood, live in the hom rather than the slots, and `verbAffixTemplate` is the
derived image.

## References

* [kaiser-yamamoto-2013]
* [narrog-2010b]
* [bybee-1985]
-/

@[expose] public section

namespace Japanese

open Morphology

/-- The Japanese verb suffix slots. -/
inductive VerbSlot where
  /-- *-su* (*suru*). -/
  | derivation
  /-- The causative *-(s)ase*. -/
  | valence
  /-- The passive and potential *-(r)are*. -/
  | voice
  /-- The desiderative *-ta(i)*. -/
  | desiderative
  /-- The polite *-mas*. -/
  | politeness
  /-- The negative *-na*. -/
  | negation
  /-- The non-past *-(r)u* and the past *-ta*. -/
  | tense
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
