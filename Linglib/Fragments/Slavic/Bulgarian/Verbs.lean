import Linglib.Morphology.Morph
import Linglib.Fragments.Slavic.Params

/-!
# Bulgarian Verbal Lexicon

Prefix morphs and verb-stem entries for the Bulgarian multiple-
prefixation data of [istratkova-2004]. Citation forms are first-person
singular present (Bulgarian has no infinitive). Simplex homogeneous
verbs (her ex. (2)) carry `aspect := none`: they have no perfective
counterparts and behave as imperfective only by default. Analytical
classification of prefix occurrences lives in
`Studies/Istratkova2004.lean`.
-/

namespace Bulgarian.Verbs

open Morphology Slavic

/-! ### Prefixes -/

/-- The prefix *za-*. -/
def za : Morph := .pref "za"

/-- The prefix *iz-*. -/
def iz : Morph := .pref "iz"

/-- The prefix *po-*. -/
def po : Morph := .pref "po"

/-- The prefix *pro-*. -/
def pro : Morph := .pref "pro"

/-- The prefix *na-*. -/
def na : Morph := .pref "na"

/-- The prefix *pre-*. -/
def pre : Morph := .pref "pre"

/-! ### Verb stems

The aspectless entries are [istratkova-2004]'s homogeneous simplex
class (her ex. (2)). -/

/-- *piša* 'write' (aspectless homogeneous simplex). -/
def pisha : VerbStem := ⟨"piša", none, "write"⟩

/-- *misl'a* 'think' (aspectless homogeneous simplex). -/
def misla : VerbStem := ⟨"misl'a", none, "think"⟩

/-- *znam* 'know' (aspectless homogeneous simplex). -/
def znam : VerbStem := ⟨"znam", none, "know"⟩

/-- *blest'a* 'glitter' (aspectless homogeneous simplex). -/
def blesta : VerbStem := ⟨"blest'a", none, "glitter"⟩

/-- *običam* 'love' (aspectless homogeneous simplex). -/
def obicham : VerbStem := ⟨"običam", none, "love"⟩

/-- *četa* 'read' (aspectless homogeneous simplex). -/
def cheta : VerbStem := ⟨"četa", none, "read"⟩

/-- *razkaža* 'narrate' (quantized perfective; etymologically
    *raz-kaža* 'around-say'). -/
def razkazha : VerbStem := ⟨"razkaža", some .perfective, "narrate"⟩

/-- *dam* 'give' (simplex quantized perfective; host of *pro-dam*
    'sell' and its prefix stacks). -/
def dam : VerbStem := ⟨"dam", some .perfective, "give"⟩

end Bulgarian.Verbs
