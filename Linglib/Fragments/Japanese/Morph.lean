import Linglib.Morphology.RelevanceHierarchy
import Linglib.Morphology.Template

/-!
# Japanese Verb Suffix Template
[kaiser-yamamoto-2013]

The Japanese verb suffix template (`verbAffixTemplate`) follows
[kaiser-yamamoto-2013] and the UD segmentation: seven slots,
stem-outward.

| Slot | Category | Morpheme |
|------|----------|----------|
| 1 | derivation | -su (suru) |
| 2 | valence | -(s)ase (causative) |
| 3 | voice | -are, -rare (passive/potential) |
| 4 | mood | -ta (desiderative) |
| 5 | agreement | -mas (politeness, treated as subject agreement) |
| 6 | negation | -na |
| 7 | tense | -ta (past), -yoo (future) |
-/

namespace Japanese

open Morphology

/-- Japanese verb suffix template, stem-outward ([kaiser-yamamoto-2013], UD
segmentation). Japanese is strongly suffixing, so there are no prefix slots. -/
def verbAffixTemplate : AffixTemplate MorphCategory where
  suffixSlots :=
    [ .derivation       -- 1. -su (suru)
    , .valence          -- 2. -(s)ase (causative)
    , .voice            -- 3. -are, -rare (passive/potential)
    , .mood             -- 4. -ta (desiderative)
    , .agreement .subj  -- 5. -mas (politeness, treated as subject agreement)
    , .negation         -- 6. -na (negation)
    , .tense ]          -- 7. -ta, -yoo (past/future)

end Japanese
