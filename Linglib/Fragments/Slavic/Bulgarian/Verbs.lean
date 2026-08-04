import Linglib.Morphology.Morph
import Linglib.Syntax.Category.Verb.Stem

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

open Morphology
open Verb (Stem)

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
def pisha : Stem := ⟨"piša", .imperfective, "write"⟩

/-- *misl'a* 'think' (imperfective simplex). -/
def misla : Stem := ⟨"misl'a", .imperfective, "think"⟩

/-- *znam* 'know' (imperfective simplex). -/
def znam : Stem := ⟨"znam", .imperfective, "know"⟩

/-- *blest'a* 'glitter' (imperfective simplex). -/
def blesta : Stem := ⟨"blest'a", .imperfective, "glitter"⟩

/-- *običam* 'love' (imperfective simplex). -/
def obicham : Stem := ⟨"običam", .imperfective, "love"⟩

/-- *četa* 'read' (imperfective simplex). -/
def cheta : Stem := ⟨"četa", .imperfective, "read"⟩

/-- *razkaža* 'narrate' (perfective; etymologically *raz-kaža*
    'around-say'). -/
def razkazha : Stem := ⟨"razkaža", .perfective, "narrate"⟩

/-- *dam* 'give' (perfective simplex; host of *pro-dam* 'sell' and
    its prefix stacks). -/
def dam : Stem := ⟨"dam", .perfective, "give"⟩

end Bulgarian.Verbs
