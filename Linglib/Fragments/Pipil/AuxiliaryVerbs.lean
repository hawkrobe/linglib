import Linglib.Morphology.Periphrasis

/-!
# Pipil Auxiliary Verb Fragment
[anderson-2006]

Pipil (Uto-Aztecan; El Salvador) has two distinct AVC constructions
in [anderson-2006], with **different auxiliaries**:

- **LEX-headed CAPABILITY AVC** (Ch 3 ex. 49, p. 130; Campbell
  1985: 139). Capability auxiliary *weli* uninflected; LV carries
  subject agreement.
- **SPLIT/DOUBLED PROGRESSIVE AVC** (Ch 5 §5.2.2, ex. 133a-c, p. 224).
  Progressive auxiliary *yu* (← 'go'); subjects doubly marked on AUX
  and LV; objects only on LV. AUX root *yu* encodes prospective TAM
  lexically. Source: Campbell 1985: 137-138, cited in [anderson-2006].

The 0.230.576 meta-audit caught an earlier docstring overreading of
Anderson p. 220-221 fn. 6: that footnote contrasts two variants of the
*progressive* AVC (lex-headed vs split/doubled, both with *yu*-class
auxiliaries) — NOT *weli* (CAP) vs *yu* (PROG). The *weli* and *yu*
forms are different AVCs entirely, not two patterns of the same AVC.

The earlier classification of the second pattern as plain `.split`
with distribution `{onAux := [.tense], onLex := [.agreement]}` was
incorrect on two counts: (i) Anderson p. 224 explicitly classifies
it as split/doubled with subjects "doubly marked"; (ii) the
distribution {onAux := [.tense], onLex := [.agreement]} contradicts
the gloss `1-AUX 1-2PL-show` which shows the `1` (subject) prefix
on BOTH elements. Audit fix: 2026-04-30.
-/

namespace Pipil.AuxiliaryVerbs

open Morphology (InflDistribution MorphCategory)

def family : String := "Uto-Aztecan"
def location : String := "El Salvador"

/-! ## Lex-headed pattern (Anderson 2006; Campbell 1985: 139) -/

/-- Lex-headed AVC form ([anderson-2006] Ch 3 ex. 49, p. 130):
    capability auxiliary *weli* uninflected; subject marking on the
    lexical verb.
    *weli ni-nehnemi wehka*
    'CAP 1-walk far'
    'I can walk far'
    (Campbell 1985: 139, cited in [anderson-2006]). -/
def lexHeadedForm : String := "weli ni-nehnemi wehka"

def lexHeadedGloss : String := "CAP 1-walk far 'I can walk far'"

/-- Lex-headed inflection: AUX uninflected, LV hosts subject agreement. -/
def lexHeadedDistribution : InflDistribution :=
  { onAux := [], onLex := [.agreement .subj] }

/-! ## Split/doubled pattern (Anderson 2006 Ch 5 ex. 133a, p. 224) -/

/-- Split/doubled AVC form (Anderson Ch 5 ex. 133b, p. 224).
    *n-yu ni-mitsin-ilwitia*
    '1-AUX 1-2PL-show'
    'I'm going to show you'
    (Campbell 1985: 137, cited in [anderson-2006]).
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
    and LV; object agreement appears only on LV. The role-typed
    encoding (subj vs obj) makes the Anderson Ch 5 §5.2 "objects on
    LV only" generalization directly Lean-checkable: see
    `Studies/Anderson2006.lean`. -/
def splitDoubledDistribution : InflDistribution :=
  { onAux := [.agreement .subj]
  , onLex := [.agreement .subj, .agreement .obj] }

/-! ## Primary pattern alias

The split/doubled pattern is what Anderson Ch 5 §5.2.2 highlights
for Pipil; the lex-headed *weli* pattern is Anderson's chapter-3
capability construction (ex. 49, p. 130). The Anderson 2006 study
file consumes both. -/

def form : String := splitDoubledForm
def gloss : String := splitDoubledGloss
def inflDistribution : InflDistribution := splitDoubledDistribution

end Pipil.AuxiliaryVerbs
