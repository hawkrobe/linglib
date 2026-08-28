import Linglib.Data.Examples.Schema

/-!
# `Anderson2006a` — typed example data

Auto-generated from `Linglib/Data/Examples/Anderson2006a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Anderson2006a.Examples`.
-/

namespace Anderson2006a.Examples

open Data.Examples

def komi_neg_pres : LinguisticExample :=
  { id := "anderson2006a_komi_neg_pres"
    source := ⟨"anderson-2006a", "(47a)"⟩
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
    paperFeatures := [("strategy", "negVerb"), ("tense", "present"), ("on_aux", "negation"), ("on_aux", "tense"), ("on_aux", "subj")]
    comment := "Komi negative auxiliary o- inflects for tense and person while the lexical verb is uninflected (the Uralic connegative construction, Anderson sect. 1.7.2). Anderson cites Hausenberg 1998: 315."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def komi_neg_past : LinguisticExample :=
  { id := "anderson2006a_komi_neg_past"
    source := ⟨"anderson-2006a", "(47b)"⟩
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
    paperFeatures := [("strategy", "negVerb"), ("tense", "past"), ("on_aux", "negation"), ("on_aux", "tense"), ("on_aux", "subj")]
    comment := "Past-tense counterpart of (47a): the tense alternation o-/e- is carried entirely by the negative auxiliary. Anderson cites Hausenberg 1998: 315."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def udihe_neg : LinguisticExample :=
  { id := "anderson2006a_udihe_neg"
    source := ⟨"anderson-2006a", "(49)"⟩
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
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "auxHeaded"), ("on_aux", "negation"), ("on_aux", "subj")]
    comment := "Anderson sect. 1.7.2 classifies the Udihe negative-auxiliary construction as aux-headed. Anderson cites Nikolaeva and Tolskaja 2001: 214."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kwerba_neg_fut : LinguisticExample :=
  { id := "anderson2006a_kwerba_neg_fut"
    source := ⟨"anderson-2006a", "(52a)"⟩
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
  { id := "anderson2006a_kwerba_neg_past"
    source := ⟨"anderson-2006a", "(52b)"⟩
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

def doyayo_lexheaded : LinguisticExample :=
  { id := "anderson2006a_doyayo_lexheaded"
    source := ⟨"anderson-2006a", "(15a)"⟩
    reportedIn := none
    language := "doya1240"
    primaryText := "mi¹ (gi²) kpel¹-ko¹"
    discourseSegments := []
    glossedTokens := [("mi¹", "I"), ("(gi²)", "AUX"), ("kpel¹-ko¹", "pour-PROX")]
    translation := "I'm going to pour"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "lexHeaded"), ("on_aux", "subj"), ("on_lex", "tense"), ("aux_marking", "partial (tone)")]
    comment := "The auxiliary is parenthesized in Anderson's gloss; p. 120 notes it \"partially encodes person of the subject through the tone associated with the auxiliary\". Anderson cites Wiering and Wiering 1994: 55."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def doyayo_splitdoubled : LinguisticExample :=
  { id := "anderson2006a_doyayo_splitdoubled"
    source := ⟨"anderson-2006a", "(129)"⟩
    reportedIn := none
    language := "doya1240"
    primaryText := "hi¹-za¹ hi¹-zaa¹³ hi¹-lɔ-mɔ"
    discourseSegments := []
    glossedTokens := [("hi¹-za¹", "3PL-POT"), ("hi¹-zaa¹³", "3PL-come"), ("hi¹-lɔ-mɔ", "3PL-bite-2")]
    translation := "they might come bite you"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "splitDoubled"), ("on_aux", "subj"), ("on_lex", "subj"), ("on_lex", "obj")]
    comment := "Subject hi¹ is marked on both elements, object -mɔ only on the lexical verb. Anderson p. 223: \"this pattern, consisting of an object found on the lexical verb with doubled subject inflection, is common in Doyayo.\" Anderson cites Wiering and Wiering 1994: 221."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gorum_tiger : LinguisticExample :=
  { id := "anderson2006a_gorum_tiger"
    source := ⟨"anderson-2006a", "(63a)"⟩
    reportedIn := none
    language := "pare1266"
    primaryText := "kula ne-giʔ-sun miŋ ne-butoŋ-tuʔ ne-i-tuʔ"
    discourseSegments := []
    glossedTokens := [("kula", "tiger"), ("ne-giʔ-sun", "1-see-when"), ("miŋ", "I"), ("ne-butoŋ-tuʔ", "1-fear-NPST:AFF"), ("ne-i-tuʔ", "1-AUX-NPST:AFF")]
    translation := "when I see the tiger, I'll be afraid"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "doubled"), ("on_aux", "subj"), ("on_aux", "tense"), ("on_aux", "affectedness"), ("on_lex", "subj"), ("on_lex", "tense"), ("on_lex", "affectedness")]
    comment := "Both verbs carry non-past tense and the Gorum category of affectedness (version). Anderson cites Aze 1973."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gorum_vigorously : LinguisticExample :=
  { id := "anderson2006a_gorum_vigorously"
    source := ⟨"anderson-2006a", "(63b)"⟩
    reportedIn := none
    language := "pare1266"
    primaryText := "miŋ ne-gaʔ-ru ne-laʔ-ru"
    discourseSegments := []
    glossedTokens := [("miŋ", "I"), ("ne-gaʔ-ru", "1-eat-PST"), ("ne-laʔ-ru", "1-AUX-PST")]
    translation := "I ate vigorously"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "doubled"), ("on_aux", "subj"), ("on_aux", "tense"), ("on_lex", "subj"), ("on_lex", "tense")]
    comment := "Also given as ex. (17) in ch. 1. Anderson cites Aze 1973: 279."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def hemba_progressive : LinguisticExample :=
  { id := "anderson2006a_hemba_progressive"
    source := ⟨"anderson-2006a", "(105)"⟩
    reportedIn := none
    language := "hemb1242"
    primaryText := "tw-a-li tu-tib-a muti"
    discourseSegments := []
    glossedTokens := [("tw-a-li", "1PL-TNS-AUX"), ("tu-tib-a", "1PL-cut-FV/IND"), ("muti", "tree")]
    translation := "we were cutting the tree"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "splitDoubled"), ("on_aux", "subj"), ("on_aux", "tense"), ("on_lex", "subj"), ("on_lex", "mood")]
    comment := "Subject agreement on both elements, tense on the auxiliary only, indicative mood on the lexical verb only. Anderson cites Aksenova 1997: 27."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def pipil_capability : LinguisticExample :=
  { id := "anderson2006a_pipil_capability"
    source := ⟨"anderson-2006a", "(49)"⟩
    reportedIn := none
    language := "pipi1250"
    primaryText := "weli ni-nehnemi wehka"
    discourseSegments := []
    glossedTokens := [("weli", "CAP"), ("ni-nehnemi", "1-walk"), ("wehka", "far")]
    translation := "I can walk far"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "lexHeaded"), ("on_lex", "subj")]
    comment := "The capability auxiliary weli is uninflected. Anderson cites Campbell 1985: 139."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def pipil_progressive : LinguisticExample :=
  { id := "anderson2006a_pipil_progressive"
    source := ⟨"anderson-2006a", "(133b)"⟩
    reportedIn := none
    language := "pipi1250"
    primaryText := "n-yu ni-mitsin-ilwitia"
    discourseSegments := []
    glossedTokens := [("n-yu", "1-AUX"), ("ni-mitsin-ilwitia", "1-2PL-show")]
    translation := "I'm going to show you"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "splitDoubled"), ("on_aux", "subj"), ("on_lex", "subj"), ("on_lex", "obj")]
    comment := "Subject 1sg is marked on both elements (n- on AUX, ni- on LV); object -mitsin- (2pl) only on the lexical verb. The auxiliary root yu, a grammaticalized motion verb 'go', carries prospective TAM lexically. Anderson p. 224: \"Subjects are doubly marked... while objects occur only on lexical verbs.\" Anderson cites Campbell 1985: 137. Also given as ex. (21) in ch. 1."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def jakaltek_completive : LinguisticExample :=
  { id := "anderson2006a_jakaltek_completive"
    source := ⟨"anderson-2006a", "(87a)"⟩
    reportedIn := none
    language := "popt1235"
    primaryText := "šk-ach w-ila"
    discourseSegments := []
    glossedTokens := [("šk-ach", "COMPL-ABS2"), ("w-ila", "ERG1-see")]
    translation := "I saw you"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "split"), ("on_aux", "aspect"), ("on_aux", "obj"), ("on_lex", "subj")]
    comment := "Absolutive marking sits on the aspectual auxiliary, ergative on the lexical verb - the reverse of the commoner split where the subject appears on the auxiliary. Also given as ex. (19) in ch. 1. Anderson cites Craig 1977: 60."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [komi_neg_pres, komi_neg_past, udihe_neg, kwerba_neg_fut, kwerba_neg_past, doyayo_lexheaded, doyayo_splitdoubled, gorum_tiger, gorum_vigorously, hemba_progressive, pipil_capability, pipil_progressive, jakaltek_completive]

end Anderson2006a.Examples
