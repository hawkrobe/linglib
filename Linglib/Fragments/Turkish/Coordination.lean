import Linglib.Syntax.Category.Coordinator

/-!
# Turkish Coordination Morphemes
[kornfilt-1997] [haspelmath-2007]

Turkish has:

- *ve* — J, free, prepositive: "A ve B" (Arabic-origin loan)
- *de* — MU, bound clitic, postpositive on first word of second coordinand:
  "Hasan ıstakoz-u pisirdi, Ali de balığ-ı" — monosyndetic A B-co
  ([haspelmath-2007] (23), [kornfilt-1997]:120). Also bisyndetic
  *de…de* as a marked emphatic variant ('also A, also B').

The original `Haspelmath2007.turkish` record had *de* as free; corrected
here per [kornfilt-1997]'s enclitic analysis.

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.turkish`).
-/

namespace Turkish.Coordination

/-- *ve* — J particle (Arabic loan). Free, prepositive medial. -/
def ve : Coordinator :=
  { form := "ve", gloss := "and"
  , role := .j, kind := .free
  , note := "Arabic-origin loan" }

/-- *de* — MU clitic, also additive. Bound enclitic on first word of
    non-initial coordinand (monosyndetic A B-co); bisyndetic *de…de* as
    a marked emphatic variant. -/
def de : Coordinator :=
  { form := "de", gloss := "also; and (MU)"
  , role := .mu, kind := .bound .after .clitic, alsoAdditive := true
  , note := "enclitic per Kornfilt 1997; also vowel-harmony variant 'da'" }

def allEntries : List Coordinator := [ve, de]

end Turkish.Coordination
