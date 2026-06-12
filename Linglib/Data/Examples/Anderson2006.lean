import Linglib.Data.Examples.Schema

/-!
# `Anderson2006` — typed example data

Auto-generated from `Linglib/Data/Examples/Anderson2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Anderson2006.Examples`.
-/

namespace Anderson2006.Examples

open Data.Examples

def komi_neg_pres : LinguisticExample :=
  { id := "anderson2006_komi_neg_pres"
    source := ⟨"anderson-2006", "(47a)"⟩
    reportedIn := none
    language := "komi1268"
    primaryText := "o-g mun"
    discourseSegments := []
    glossedTokens := [("o-g", "NEG:PRES-1"), ("mun", "go")]
    translation := "I don't go"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("tense", "present")]
    comment := "Komi negative auxiliary o- inflects for tense and person while the lexical verb is uninflected (the Uralic connegative construction, Anderson sect. 1.7.2). Anderson cites Hausenberg 1998: 315."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def komi_neg_past : LinguisticExample :=
  { id := "anderson2006_komi_neg_past"
    source := ⟨"anderson-2006", "(47b)"⟩
    reportedIn := none
    language := "komi1268"
    primaryText := "e-g mun"
    discourseSegments := []
    glossedTokens := [("e-g", "NEG:PST-1"), ("mun", "go")]
    translation := "I didn't go"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("tense", "past")]
    comment := "Past-tense counterpart of (47a): the tense alternation o-/e- is carried entirely by the negative auxiliary. Anderson cites Hausenberg 1998: 315."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def udihe_neg : LinguisticExample :=
  { id := "anderson2006_udihe_neg"
    source := ⟨"anderson-2006", "(49)"⟩
    reportedIn := none
    language := "udih1248"
    primaryText := "bi ei-mi sa:"
    discourseSegments := []
    glossedTokens := [("bi", "I"), ("ei-mi", "NEG-1"), ("sa:", "know")]
    translation := "I don't know"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "auxHeaded")]
    comment := "Anderson sect. 1.7.2 classifies the Udihe negative-auxiliary construction as aux-headed. Anderson cites Nikolaeva and Tolskaja 2001: 214."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kwerba_neg_fut : LinguisticExample :=
  { id := "anderson2006_kwerba_neg_fut"
    source := ⟨"anderson-2006", "(52a)"⟩
    reportedIn := none
    language := "kwer1242"
    primaryText := "co kwai kot-ri-m"
    discourseSegments := []
    glossedTokens := [("co", "I"), ("kwai", "NEG:FUT"), ("kot-ri-m", "cut-AUG-IRR")]
    translation := "I will not cut it"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "lexHeaded")]
    comment := "Anderson sect. 1.7.2 lists Kwerba as the lex-headed exemplar among negative-auxiliary constructions: the lexical verb hosts the inflection. Anderson cites de Vries and de Vries 1997: 12-13."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kwerba_neg_past : LinguisticExample :=
  { id := "anderson2006_kwerba_neg_past"
    source := ⟨"anderson-2006", "(52b)"⟩
    reportedIn := none
    language := "kwer1242"
    primaryText := "co kot-ri-m-o baye"
    discourseSegments := []
    glossedTokens := [("co", "I"), ("kot-ri-m-o", "cut-AUG-IRR-NEG"), ("baye", "NEG:PST")]
    translation := "I did not cut it"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "lexHeaded")]
    comment := "Past-tense Kwerba negation: negative suffix -o on the inflected lexical verb plus postverbal baye. Anderson cites de Vries and de Vries 1997: 12-13."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [komi_neg_pres, komi_neg_past, udihe_neg, kwerba_neg_fut, kwerba_neg_past]

end Anderson2006.Examples
