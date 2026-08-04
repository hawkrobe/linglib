import Linglib.Morphology.Morph
import Linglib.Syntax.Category.Verb.Stem

/-!
# Russian Verbal Lexicon

Prefix morphs and verb-stem entries for the Russian verbal-prefix data
of [svenonius-2004]. Prefixes carry only their form (`Morph.pref`);
stems carry citation form, aspect, and gloss. Analytical classification
(lexical vs superlexical) lives in `Studies/Svenonius2004.lean`.

Transliteration follows [svenonius-2004] (*j* for palatalization, as in
*brositj*).
-/

namespace Russian.Verbs

open Morphology
open Verb (Stem)

/-! ### Prefixes -/

/-- The prefix *za-*. -/
def za : Morph := .pref "za"

/-- The prefix *vy-* 'out'. -/
def vy : Morph := .pref "vy"

/-- The prefix *po-*. -/
def po : Morph := .pref "po"

/-! ### Verb stems -/

/-- *brositj* 'throw' (perfective). -/
def brosit : Stem := ⟨"brositj", .perfective, "throw"⟩

/-- *brosatj* 'throw' (imperfective). -/
def brosat : Stem := ⟨"brosatj", .imperfective, "throw"⟩

/-- *brasyvatj* — the secondary-imperfective stem of *brositj* /
    *brosatj*, host of further prefixation in [svenonius-2004] ex. (4a). -/
def brasyvat : Stem := ⟨"brasyvatj", .imperfective, "throw"⟩

/-- *kuritj* 'smoke' (imperfective). -/
def kurit : Stem := ⟨"kuritj", .imperfective, "smoke"⟩

/-- *čitatj* 'read' (imperfective). -/
def chitat : Stem := ⟨"čitatj", .imperfective, "read"⟩

end Russian.Verbs
