
/-!
# Doyayo Auxiliary Verb Fragment
[anderson-2006]

Doyayo (Adamawa, Niger-Congo; Cameroon) appears in [anderson-2006]
under **two** distinct AVC patterns:

- **Ch 3 (LEX-headed), ex. (15a-b), p. 121.** Auxiliary uninflected
  (or marked only by tone for subject person); lexical verb carries
  TAM and argument-structure morphology. Sources: Wiering and
  Wiering 1994: 55, 77.
- **Ch 5 (SPLIT/DOUBLED), ex. (128-129), pp. 222-223.** Subjects
  doubly marked on AUX and LV; objects only on LV; the auxiliary
  is a grammaticalized motion verb encoding TAM. Sources: Wiering
  and Wiering 1994: 217, 221, 222.

This Fragment exposes BOTH patterns; the `Studies/Anderson2006.lean`
study file consumes them as two separate `AVCDatum`s.

The earlier single-pattern entry (W&W 1994: 75 'they will be
catching him for me' classified as `.split`) was removed in the
2026-04-30 audit: Anderson never classifies Doyayo as plain split,
and the cited W&W p. 75 example does not appear in any of Anderson's
Doyayo passages (Anderson cites W&W pp. 55, 77, 217, 221, 222).
-/

namespace Doyayo.AuxiliaryVerbs


def family : String := "Adamawa, Niger-Congo"
def location : String := "Cameroon"

/-! ## Lex-headed pattern (Anderson 2006, Ch 3 ex. 15a, p. 121) -/

/-- Lex-headed AVC form (Anderson Ch 3 ex. 15a, p. 121).
    *mi¹ (gi²) kpel¹-ko¹*
    'I AUX pour-PROX'
    'I'm going to pour'
    (Wiering and Wiering 1994: 55, cited in [anderson-2006]).
    AUX `gi²` is parenthesized in Anderson's gloss; per Anderson p. 120
    it "partially encodes person of the subject through the tone associated
    with the auxiliary". The LV `kpel¹-ko¹` carries the proximate-future
    TAM marker. -/
def lexHeadedForm : String := "mi¹ (gi²) kpel¹-ko¹"

def lexHeadedGloss : String := "I AUX pour-PROX 'I'm going to pour'"


/-! ## Split/doubled pattern (Anderson 2006, Ch 5 ex. 128-129, pp. 222-223) -/

/-- Split/doubled AVC form (Anderson Ch 5 ex. 129, p. 223).
    *hi¹-za¹ hi¹-zaa¹³ hi¹-lɔ-mɔ*
    '3PL-POT 3PL-come 3PL-bite-2'
    'they might come bite you'
    (Wiering and Wiering 1994: 221, cited in [anderson-2006]).
    Subject `hi¹` is doubly marked on AUX and LV (each prefixed with
    `hi¹-`); object `-mɔ` (2nd person) appears only on the LV.
    Anderson p. 223: "this pattern, consisting of an object found on
    the lexical verb with doubled subject inflection, is common in
    Doyayo." Note `hi¹-zaa¹³` carries a contour tone (1+3); the
    earlier single-tone `hi¹-zaa³` rendering was a transcription
    error caught in the 0.230.576 meta-audit. -/
def splitDoubledForm : String := "hi¹-za¹ hi¹-zaa¹³ hi¹-lɔ-mɔ"

def splitDoubledGloss : String :=
  "3PL-POT 3PL-come 3PL-bite-2 'they might come bite you'"


/-! ## Primary pattern alias

The Ch 3 lex-headed pattern is the chronologically earlier, simpler
construction; the split/doubled pattern derives diachronically from
serialization (Anderson p. 222-223). For consumers needing a single
`form`/`distribution` pair, the lex-headed entries are the default. -/

def form : String := lexHeadedForm
def gloss : String := lexHeadedGloss

end Doyayo.AuxiliaryVerbs
