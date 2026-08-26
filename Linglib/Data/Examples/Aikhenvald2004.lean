import Linglib.Data.Examples.Schema

/-!
# `Aikhenvald2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Aikhenvald2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Aikhenvald2004.Examples`.
-/

namespace Aikhenvald2004.Examples

open Data.Examples

def ex1_1 : LinguisticExample :=
  { id := "aikhenvald2004_ex1_1"
    source := ⟨"aikhenvald-2004", "(1.1)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-ka"
    discourseSegments := []
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-ka", "3sgnf-play-REC.P.VIS")]
    translation := "José has played football (we saw it)"
    context := "The speaker saw José play."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "visual"), ("source", "visual")]
    comment := "Tariana's five-choice system: the evidential -ka is fused with recent past tense; omitting an evidential is ungrammatical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex1_2 : LinguisticExample :=
  { id := "aikhenvald2004_ex1_2"
    source := ⟨"aikhenvald-2004", "(1.2)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-mahka"
    discourseSegments := []
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-mahka", "3sgnf-play-REC.P.NONVIS")]
    translation := "José has played football (we heard it)"
    context := "The speaker heard the noise of a game but could not see it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "sensory"), ("source", "nonvisual")]
    comment := "Tariana's five-choice system: the evidential -mahka is fused with recent past tense; omitting an evidential is ungrammatical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex1_3 : LinguisticExample :=
  { id := "aikhenvald2004_ex1_3"
    source := ⟨"aikhenvald-2004", "(1.3)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-nihka"
    discourseSegments := []
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-nihka", "3sgnf-play-REC.P.INFR")]
    translation := "José has played football (we infer it from visual evidence)"
    context := "The football and José's boots are gone and crowds return from the ground."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "inferred"), ("source", "inference")]
    comment := "Tariana's five-choice system: the evidential -nihka is fused with recent past tense; omitting an evidential is ungrammatical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex1_4 : LinguisticExample :=
  { id := "aikhenvald2004_ex1_4"
    source := ⟨"aikhenvald-2004", "(1.4)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-sika"
    discourseSegments := []
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-sika", "3sgnf-play-REC.P.ASSUM")]
    translation := "José has played football (we assume this on the basis of what we already know)"
    context := "José is out on a Sunday afternoon, when he usually plays."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "assumed"), ("source", "assumption")]
    comment := "Tariana's five-choice system: the evidential -sika is fused with recent past tense; omitting an evidential is ungrammatical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex1_5 : LinguisticExample :=
  { id := "aikhenvald2004_ex1_5"
    source := ⟨"aikhenvald-2004", "(1.5)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-pidaka"
    discourseSegments := []
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-pidaka", "3sgnf-play-REC.P.REP")]
    translation := "José has played football (we were told)"
    context := "Someone told the speaker."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "reported"), ("source", "report")]
    comment := "Tariana's five-choice system: the evidential -pidaka is fused with recent past tense; omitting an evidential is ungrammatical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2_16 : LinguisticExample :=
  { id := "aikhenvald2004_ex2_16"
    source := ⟨"aikhenvald-2004", "(2.16)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "bakan hasta-ymış"
    discourseSegments := []
    glossedTokens := [("bakan", "minister"), ("hasta-ymış", "sick-NONFIRSTH.COP")]
    translation := "The minister is reportedly sick"
    context := "Said by somebody told about the sickness."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "report")]
    comment := "The Turkish non-firsthand covers report, inference and non-visual perception; examples after Johanson."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2_17 : LinguisticExample :=
  { id := "aikhenvald2004_ex2_17"
    source := ⟨"aikhenvald-2004", "(2.17)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "uyu-muş-um"
    discourseSegments := []
    glossedTokens := [("uyu-muş-um", "sleep-NONFIRSTH.PAST-1sg")]
    translation := "I have obviously slept"
    context := "Said by somebody who has just woken up."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "inference")]
    comment := "The Turkish non-firsthand covers report, inference and non-visual perception; examples after Johanson."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2_18 : LinguisticExample :=
  { id := "aikhenvald2004_ex2_18"
    source := ⟨"aikhenvald-2004", "(2.18)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "iyi çal-ıyor-muş"
    discourseSegments := []
    glossedTokens := [("iyi", "good"), ("çal-ıyor-muş", "play-INTRATERM.ASP-NONFIRSTH.COP")]
    translation := "She is, as I hear, playing well"
    context := "Said by somebody listening to her play."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "nonvisual")]
    comment := "The Turkish non-firsthand covers report, inference and non-visual perception; examples after Johanson."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2_40 : LinguisticExample :=
  { id := "aikhenvald2004_ex2_40"
    source := ⟨"aikhenvald-2004", "(2.40)"⟩
    reportedIn := none
    language := "jauj1238"
    primaryText := "Chay-chruu-mi achka wamla-pis walashr-pis alma-ku-lkaa-ña"
    discourseSegments := []
    glossedTokens := [("Chay-chruu-mi", "this-LOC-DIR.EV"), ("achka", "many"), ("wamla-pis", "girl-TOO"), ("walashr-pis", "boy-TOO"), ("alma-ku-lkaa-ña", "bathe-REFL-IMPF.PL-NARR.PAST")]
    translation := "Many girls and boys were swimming (I saw them)"
    context := "The speaker saw them."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "B1"), ("term", "visual"), ("source", "visual")]
    comment := "Wanka Quechua's three-choice system: direct -mi, inferred (conjectural) -chr(a), reported -shi; examples after Floyd."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2_41 : LinguisticExample :=
  { id := "aikhenvald2004_ex2_41"
    source := ⟨"aikhenvald-2004", "(2.41)"⟩
    reportedIn := none
    language := "jauj1238"
    primaryText := "Daañu pawa-shra-si ka-ya-n-chr-ari"
    discourseSegments := []
    glossedTokens := [("Daañu", "field"), ("pawa-shra-si", "finish-PART-EVEN"), ("ka-ya-n-chr-ari", "be-IMPF-3-INFR-EMPH")]
    translation := "It (the field) might be completely destroyed (I infer)"
    context := "The speaker infers it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "B1"), ("term", "inferred"), ("source", "inference")]
    comment := "Wanka Quechua's three-choice system: direct -mi, inferred (conjectural) -chr(a), reported -shi; examples after Floyd."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2_42 : LinguisticExample :=
  { id := "aikhenvald2004_ex2_42"
    source := ⟨"aikhenvald-2004", "(2.42)"⟩
    reportedIn := none
    language := "jauj1238"
    primaryText := "Ancha-p-shi wa'a-chi-nki wamla-a-ta"
    discourseSegments := []
    glossedTokens := [("Ancha-p-shi", "too.much-GEN-REP"), ("wa'a-chi-nki", "cry-CAUS-2"), ("wamla-a-ta", "girl-1p-ACC")]
    translation := "You make my daughter cry too much (they tell me)"
    context := "The speaker was told."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "B1"), ("term", "reported"), ("source", "report")]
    comment := "Wanka Quechua's three-choice system: direct -mi, inferred (conjectural) -chr(a), reported -shi; examples after Floyd."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_7 : LinguisticExample :=
  { id := "aikhenvald2004_ex4_7"
    source := ⟨"aikhenvald-2004", "(4.7)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "varsken-s ianvr-is rva-s p'irvel-ad u-c'am-eb-i-a susanik'-i"
    discourseSegments := []
    glossedTokens := [("varsken-s", "Varsken-DAT"), ("ianvr-is", "January-GEN"), ("rva-s", "8-DAT"), ("p'irvel-ad", "first-ADV"), ("u-c'am-eb-i-a", "OV-torture-TS-PERF-her"), ("susanik'-i", "Shushanik'-NOM")]
    translation := "Varsken apparently first tortured Shushanik on 8th January"
    context := "A past action the speaker did not witness but assumes from a present result or a report."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "perfect"), ("source", "nonfirsthand")]
    comment := "The Georgian perfect's non-firsthand use is an extension of its resultative meaning, alongside present-perfect, negated-past and optative uses, so the perfect is an evidentiality strategy rather than an evidential; example after Hewitt."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_55 : LinguisticExample :=
  { id := "aikhenvald2004_ex4_55"
    source := ⟨"aikhenvald-2004", "(4.55)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Dumat, zmejat sljazăl v našata niva"
    discourseSegments := []
    glossedTokens := [("Dumat", "think.PRES.3PL"), ("zmejat", "dragon"), ("sljazăl", "come.down.REPORTIVE.SG"), ("v", "into"), ("našata", "our"), ("niva", "field")]
    translation := "They think that the dragon would seem to have come down into our field (not very likely)"
    context := "Reported information the speaker distances themself from."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "report"), ("extension", "epistemic")]
    comment := "The Bulgarian non-firsthand carries an epistemic overtone of distance: the speaker is unwilling to bear responsibility for the claim; example after Gvozdanović."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex1_1, ex1_2, ex1_3, ex1_4, ex1_5, ex2_16, ex2_17, ex2_18, ex2_40, ex2_41, ex2_42, ex4_7, ex4_55]

end Aikhenvald2004.Examples
