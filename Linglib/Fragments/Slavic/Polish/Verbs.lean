import Linglib.Morphology.Morph
import Linglib.Semantics.Verb.Stem

/-!
# Polish Verbal Lexicon

Prefix morphs and verb-stem entries for the Polish verbal-prefix data
of [jablonska-2004] (and the Polish examples of [svenonius-2004]).
Prefixes carry only their form; the reading of *po-* per occurrence
(delimitative vs distributive vs inceptive) is [jablonska-2004]'s
central analytical question and lives in `Studies/Jablonska2004.lean`.
-/

namespace Polish.Verbs

open Morphology
open Verb (Stem)

/-! ### Prefixes -/

/-- The prefix *po-*. -/
def po : Morph := .pref "po"

/-- The prefix *za-*. -/
def za : Morph := .pref "za"

/-- The prefix *w-* 'in'. -/
def w : Morph := .pref "w"

/-! ### Verb stems -/

/-- *siedzieć* 'sit' (imperfective, stative). -/
def siedziec : Stem := ⟨"siedzieć", .imperfective, "sit"⟩

/-- *kochać* 'love' (imperfective, stative). -/
def kochac : Stem := ⟨"kochać", .imperfective, "love"⟩

/-- *jaśnieć* 'be bright' (imperfective, low -ej- verbalizer stem). -/
def jasniec : Stem := ⟨"jaśnieć", .imperfective, "be bright"⟩

/-- *chodzić* 'walk' (imperfective, non-directed motion). -/
def chodzic : Stem := ⟨"chodzić", .imperfective, "walk"⟩

end Polish.Verbs
