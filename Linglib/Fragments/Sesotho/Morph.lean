import Linglib.Morphology.AffixTemplate

/-!
# Sesotho Morphological Profile
[demuth-1992] [doke-mofokeng-1967]

Verb affix template for Sesotho (Southern Sotho, ISO `sot`), from the reference
grammars [demuth-1992] and [doke-mofokeng-1967].

**Prefixes** (word-edge inward): subject agreement, negation, tense/aspect/mood,
object agreement.

**Suffixes** (stem-outward): a valence-changing inner layer (reversive,
causative, neuter, applicative, completive), then voice (reciprocal, passive),
then tense (perfect `-il-`), mood (imperative/subjunctive/indicative), and a
final interrogative/relative (nonfinite) slot.
-/

namespace Sesotho

open Morphology

/-- Sesotho verb affix template ([demuth-1992], [doke-mofokeng-1967]). The
suffix slots run stem-outward; the prefix slots run word-edge inward. -/
def verbAffixTemplate : AffixTemplate MorphCategory where
  suffixSlots :=
    [ .valence    -- 1. reversive
    , .valence    -- 2. causative
    , .valence    -- 3. neuter
    , .valence    -- 4. applicative
    , .valence    -- 5. completive (applicative reduplication)
    , .voice      -- 6. reciprocal
    , .voice      -- 7. passive
    , .tense      -- 8. perfect (-il-)
    , .mood       -- 9. imperative/subjunctive/indicative
    , .nonfinite ] -- 10. interrogative/relative
  prefixSlots :=
    [ .agreement .subj  -- 1. subject agreement
    , .negation         -- 2. negation
    , .tense            -- 3. tense/aspect/mood
    , .agreement .obj ] -- 4. object agreement

end Sesotho
