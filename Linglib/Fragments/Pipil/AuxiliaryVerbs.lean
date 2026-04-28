import Linglib.Core.Morphology.MorphRule

/-!
# Pipil Auxiliary Verb Fragment
@cite{anderson-2006}

Pipil (Uto-Aztecan; El Salvador) has auxiliary verb constructions that
exhibit BOTH **lex-headed** and **split** patterns, depending on the
construction.

In the lex-headed pattern, the capability auxiliary *weli* is uninflected
and the lexical verb carries subject marking. In the split pattern,
auxiliaries mark tense while subject and object are encoded on lexical verbs.

Source: Campbell 1985, cited in @cite{anderson-2006}.
-/

namespace Fragments.Pipil.AuxiliaryVerbs

open Core.Morphology (InflDistribution MorphCategory)

/-- Lex-headed AVC form: the capability auxiliary *weli* is uninflected;
    subject marking appears on the lexical verb.
    *weli ni-nehnemi wehka*
    'CAP 1-walk far'
    'I can walk far'
    (Campbell 1985: 139, cited in @cite{anderson-2006}). -/
def lexHeadedForm : String := "weli ni-nehnemi wehka"

def lexHeadedGloss : String := "CAP 1-walk far 'I can walk far'"

/-- Lex-headed inflection: AUX is uninflected, LV hosts subject agreement. -/
def lexHeadedDistribution : InflDistribution :=
  { onAux := [], onLex := [.agreement] }

/-- Split AVC form: auxiliaries mark tense; subject and object on LV.
    *te: weli-k ni-k-namaka ...*
    'NEG CAP-PRET 1-it-sell ...'
    'I could not sell the broom which they brought'
    (Campbell 1985: 139, cited in @cite{anderson-2006}). -/
def splitForm : String := "te: weli-k ni-k-namaka"

def splitGloss : String := "NEG CAP-PRET 1-it-sell 'I could not sell...'"

/-- Split inflection: AUX hosts tense, LV hosts subject/object agreement. -/
def splitDistribution : InflDistribution :=
  { onAux := [.tense], onLex := [.agreement] }

/-- The primary citation form uses the split pattern. -/
def form : String := splitForm
def gloss : String := splitGloss

/-- Primary distribution (split pattern). -/
def inflDistribution : InflDistribution := splitDistribution

def family : String := "Uto-Aztecan"
def location : String := "El Salvador"

end Fragments.Pipil.AuxiliaryVerbs
