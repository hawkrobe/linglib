module

public import Linglib.Data.Examples.Schema

/-!
# `Anderson2006a` — typed example data

Auto-generated from `Linglib/Data/Examples/Anderson2006a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Anderson2006a.Examples`.
-/

@[expose] public section

namespace Anderson2006a.Examples

open Data.Examples

def komi_neg_pres : LinguisticExample :=
  { id := "anderson2006a_komi_neg_pres"
    source := ⟨"anderson-2006a", "(47a)"⟩
    reportedIn := none
    language := "komi1268"
    primaryText := "o-g mun"
    glossedTokens := [("o-g", "NEG:PRES-1"), ("mun", "go")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("tense", "present"), ("on_aux", "negation"), ("on_aux", "tense"), ("on_aux", "subj")] }

def komi_neg_past : LinguisticExample :=
  { id := "anderson2006a_komi_neg_past"
    source := ⟨"anderson-2006a", "(47b)"⟩
    reportedIn := none
    language := "komi1268"
    primaryText := "e-g mun"
    glossedTokens := [("e-g", "NEG:PST-1"), ("mun", "go")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("tense", "past"), ("on_aux", "negation"), ("on_aux", "tense"), ("on_aux", "subj")] }

def udihe_neg : LinguisticExample :=
  { id := "anderson2006a_udihe_neg"
    source := ⟨"anderson-2006a", "(49)"⟩
    reportedIn := none
    language := "udih1248"
    primaryText := "bi ei-mi sa:"
    glossedTokens := [("bi", "I"), ("ei-mi", "NEG-1"), ("sa:", "know")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "auxHeaded"), ("on_aux", "negation"), ("on_aux", "subj")] }

def kwerba_neg_fut : LinguisticExample :=
  { id := "anderson2006a_kwerba_neg_fut"
    source := ⟨"anderson-2006a", "(52a)"⟩
    reportedIn := none
    language := "kwer1242"
    primaryText := "co kwai kot-ri-m"
    glossedTokens := [("co", "I"), ("kwai", "NEG:FUT"), ("kot-ri-m", "cut-AUG-IRR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "lexHeaded")] }

def kwerba_neg_past : LinguisticExample :=
  { id := "anderson2006a_kwerba_neg_past"
    source := ⟨"anderson-2006a", "(52b)"⟩
    reportedIn := none
    language := "kwer1242"
    primaryText := "co kot-ri-m-o baye"
    glossedTokens := [("co", "I"), ("kot-ri-m-o", "cut-AUG-IRR-NEG"), ("baye", "NEG:PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "lexHeaded")] }

def doyayo_lexheaded : LinguisticExample :=
  { id := "anderson2006a_doyayo_lexheaded"
    source := ⟨"anderson-2006a", "(15a)"⟩
    reportedIn := none
    language := "doya1240"
    primaryText := "mi¹ (gi²) kpel¹-ko¹"
    glossedTokens := [("mi¹", "I"), ("(gi²)", "AUX"), ("kpel¹-ko¹", "pour-PROX")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "lexHeaded"), ("on_aux", "subj"), ("on_lex", "tense"), ("aux_marking", "partial (tone)")] }

def doyayo_splitdoubled : LinguisticExample :=
  { id := "anderson2006a_doyayo_splitdoubled"
    source := ⟨"anderson-2006a", "(129)"⟩
    reportedIn := none
    language := "doya1240"
    primaryText := "hi¹-za¹ hi¹-zaa¹³ hi¹-lɔ-mɔ"
    glossedTokens := [("hi¹-za¹", "3PL-POT"), ("hi¹-zaa¹³", "3PL-come"), ("hi¹-lɔ-mɔ", "3PL-bite-2")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "splitDoubled"), ("on_aux", "subj"), ("on_lex", "subj"), ("on_lex", "obj")] }

def gorum_tiger : LinguisticExample :=
  { id := "anderson2006a_gorum_tiger"
    source := ⟨"anderson-2006a", "(63a)"⟩
    reportedIn := none
    language := "pare1266"
    primaryText := "kula ne-giʔ-sun miŋ ne-butoŋ-tuʔ ne-i-tuʔ"
    glossedTokens := [("kula", "tiger"), ("ne-giʔ-sun", "1-see-when"), ("miŋ", "I"), ("ne-butoŋ-tuʔ", "1-fear-NPST:AFF"), ("ne-i-tuʔ", "1-AUX-NPST:AFF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "doubled"), ("on_aux", "subj"), ("on_aux", "tense"), ("on_aux", "affectedness"), ("on_lex", "subj"), ("on_lex", "tense"), ("on_lex", "affectedness")] }

def gorum_vigorously : LinguisticExample :=
  { id := "anderson2006a_gorum_vigorously"
    source := ⟨"anderson-2006a", "(63b)"⟩
    reportedIn := none
    language := "pare1266"
    primaryText := "miŋ ne-gaʔ-ru ne-laʔ-ru"
    glossedTokens := [("miŋ", "I"), ("ne-gaʔ-ru", "1-eat-PST"), ("ne-laʔ-ru", "1-AUX-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "doubled"), ("on_aux", "subj"), ("on_aux", "tense"), ("on_lex", "subj"), ("on_lex", "tense")] }

def hemba_progressive : LinguisticExample :=
  { id := "anderson2006a_hemba_progressive"
    source := ⟨"anderson-2006a", "(105)"⟩
    reportedIn := none
    language := "hemb1242"
    primaryText := "tw-a-li tu-tib-a muti"
    glossedTokens := [("tw-a-li", "1PL-TNS-AUX"), ("tu-tib-a", "1PL-cut-FV/IND"), ("muti", "tree")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "splitDoubled"), ("on_aux", "subj"), ("on_aux", "tense"), ("on_lex", "subj"), ("on_lex", "mood")] }

def pipil_capability : LinguisticExample :=
  { id := "anderson2006a_pipil_capability"
    source := ⟨"anderson-2006a", "(49)"⟩
    reportedIn := none
    language := "pipi1250"
    primaryText := "weli ni-nehnemi wehka"
    glossedTokens := [("weli", "CAP"), ("ni-nehnemi", "1-walk"), ("wehka", "far")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "lexHeaded"), ("on_lex", "subj")] }

def pipil_progressive : LinguisticExample :=
  { id := "anderson2006a_pipil_progressive"
    source := ⟨"anderson-2006a", "(133b)"⟩
    reportedIn := none
    language := "pipi1250"
    primaryText := "n-yu ni-mitsin-ilwitia"
    glossedTokens := [("n-yu", "1-AUX"), ("ni-mitsin-ilwitia", "1-2PL-show")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "splitDoubled"), ("on_aux", "subj"), ("on_lex", "subj"), ("on_lex", "obj")] }

def jakaltek_completive : LinguisticExample :=
  { id := "anderson2006a_jakaltek_completive"
    source := ⟨"anderson-2006a", "(87a)"⟩
    reportedIn := none
    language := "popt1235"
    primaryText := "šk-ach w-ila"
    glossedTokens := [("šk-ach", "COMPL-ABS2"), ("w-ila", "ERG1-see")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "split"), ("on_aux", "aspect"), ("on_aux", "obj"), ("on_lex", "subj")] }

def all : List LinguisticExample := [komi_neg_pres, komi_neg_past, udihe_neg, kwerba_neg_fut, kwerba_neg_past, doyayo_lexheaded, doyayo_splitdoubled, gorum_tiger, gorum_vigorously, hemba_progressive, pipil_capability, pipil_progressive, jakaltek_completive]

end Anderson2006a.Examples
