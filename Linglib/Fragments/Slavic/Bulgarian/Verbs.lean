import Linglib.Morphology.Morph
import Linglib.Fragments.Slavic.Params

/-!
# Bulgarian Verbal Lexicon

Prefix morphs and verb-stem entries for the Bulgarian multiple-
prefixation data of [istratkova-2004]. Citation forms are first-person
singular present (Bulgarian has no infinitive). Aspect values are the
dictionary-consensus ones; her analytical reclassification of the
simplex imperfectives as aspectless homogeneous verbs (her ex. (2)),
like the classification of prefix occurrences, lives in
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

/-! ### Verb stems -/

/-- *piša* 'write' (imperfective simplex). -/
def pisha : VerbStem := ⟨"piša", .imperfective, "write"⟩

/-- *misl'a* 'think' (imperfective simplex). -/
def misla : VerbStem := ⟨"misl'a", .imperfective, "think"⟩

/-- *znam* 'know' (imperfective simplex). -/
def znam : VerbStem := ⟨"znam", .imperfective, "know"⟩

/-- *blest'a* 'glitter' (imperfective simplex). -/
def blesta : VerbStem := ⟨"blest'a", .imperfective, "glitter"⟩

/-- *običam* 'love' (imperfective simplex). -/
def obicham : VerbStem := ⟨"običam", .imperfective, "love"⟩

/-- *četa* 'read' (imperfective simplex). -/
def cheta : VerbStem := ⟨"četa", .imperfective, "read"⟩

/-- *razkaža* 'narrate' (perfective; etymologically *raz-kaža*
    'around-say'). -/
def razkazha : VerbStem := ⟨"razkaža", .perfective, "narrate"⟩

/-- *dam* 'give' (perfective simplex; host of *pro-dam* 'sell' and
    its prefix stacks). -/
def dam : VerbStem := ⟨"dam", .perfective, "give"⟩

end Bulgarian.Verbs
