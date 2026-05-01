import Linglib.Core.Morphology.MorphRule

/-!
# Pipil Auxiliary Verb Fragment
@cite{anderson-2006}

Pipil (Uto-Aztecan; El Salvador) appears in @cite{anderson-2006}
under **two** distinct AVC patterns:

- **LEX-headed** (Ch 3 vicinity, also Ch 5 fn. 6 p. 220-221).
  Capability auxiliary *weli* uninflected; LV carries subject
  agreement. Source: Campbell 1985: 139, cited in @cite{anderson-2006}.
- **SPLIT/DOUBLED** (Ch 5 §5.2.2, ex. 133a-c, p. 224). Subjects
  doubly marked on AUX and LV; objects only on LV. AUX root *yu*
  (← 'go') encodes prospective TAM lexically. Source: Campbell
  1985: 137-138, cited in @cite{anderson-2006}; cf. footnote 6
  on p. 220-221 explicitly contrasting these two Pipil patterns.

The earlier classification of the second pattern as plain `.split`
with distribution `{onAux := [.tense], onLex := [.agreement]}` was
incorrect on two counts: (i) Anderson p. 224 explicitly classifies
it as split/doubled with subjects "doubly marked"; (ii) the
distribution {onAux := [.tense], onLex := [.agreement]} contradicts
the gloss `1-AUX 1-2PL-show` which shows the `1` (subject) prefix
on BOTH elements. Audit fix: 2026-04-30.
-/

namespace Fragments.Pipil.AuxiliaryVerbs

open Core.Morphology (InflDistribution MorphCategory)

def family : String := "Uto-Aztecan"
def location : String := "El Salvador"

/-! ## Lex-headed pattern (Anderson 2006; Campbell 1985: 139) -/

/-- Lex-headed AVC form: capability auxiliary *weli* uninflected;
    subject marking on the lexical verb.
    *weli ni-nehnemi wehka*
    'CAP 1-walk far'
    'I can walk far'
    (Campbell 1985: 139, cited in @cite{anderson-2006}). -/
def lexHeadedForm : String := "weli ni-nehnemi wehka"

def lexHeadedGloss : String := "CAP 1-walk far 'I can walk far'"

/-- Lex-headed inflection: AUX uninflected, LV hosts subject agreement. -/
def lexHeadedDistribution : InflDistribution :=
  { onAux := [], onLex := [.agreement] }

/-! ## Split/doubled pattern (Anderson 2006 Ch 5 ex. 133a, p. 224) -/

/-- Split/doubled AVC form (Anderson Ch 5 ex. 133b, p. 224).
    *n-yu ni-mitsin-ilwitia*
    '1-AUX 1-2PL-show'
    'I'm going to show you'
    (Campbell 1985: 137, cited in @cite{anderson-2006}).
    Subject `1` (1sg) is doubly marked: as `n-` on AUX and as `ni-`
    on LV. Object `-mitsin-` (2pl) appears only on the LV. The AUX
    root *yu* (a grammaticalized form of the motion verb 'go')
    encodes the prospective-future TAM lexically. Anderson p. 224:
    "Subjects are doubly marked... while objects occur only on
    lexical verbs." -/
def splitDoubledForm : String := "n-yu ni-mitsin-ilwitia"

def splitDoubledGloss : String :=
  "1-AUX 1-2PL-show 'I'm going to show you'"

/-- Split/doubled inflection: subject agreement doubled on both AUX
    and LV; object valence appears only on LV. -/
def splitDoubledDistribution : InflDistribution :=
  { onAux := [.agreement], onLex := [.agreement, .valence] }

/-! ## Primary pattern alias

The split/doubled pattern is what Anderson Ch 5 §5.2.2 highlights
for Pipil; the lex-headed *weli* pattern is the chapter-3 alternative
flagged in Anderson's footnote 6 on p. 220-221 as a co-existing
construction. The Anderson 2006 study file consumes both. -/

def form : String := splitDoubledForm
def gloss : String := splitDoubledGloss
def inflDistribution : InflDistribution := splitDoubledDistribution

end Fragments.Pipil.AuxiliaryVerbs
