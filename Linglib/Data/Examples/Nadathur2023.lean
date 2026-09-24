module

public import Linglib.Data.Examples.Schema

/-!
# `Nadathur2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Nadathur2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Nadathur2023.Examples`.
-/

@[expose] public section

namespace Nadathur2023.Examples

open Data.Examples

def ex_2a : LinguisticExample :=
  { id := "nadathur2023_2a"
    source := ⟨"nadathur-2023-implicatives", "(2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Eman onnistu-i kuitenkin pakenema-an."
    discourseSegments := []
    glossedTokens := [("Eman", "Eman"), ("onnistu-i", "succeed-PST.3SG"), ("kuitenkin", "however"), ("pakenema-an", "flee-INF.ILL")]
    translation := "Eman managed to flee."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "onnistua"), ("matrix", "positive"), ("entails", "complement")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_2b : LinguisticExample :=
  { id := "nadathur2023_2b"
    source := ⟨"nadathur-2023-implicatives", "(2b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Eman e-i onnistu-nut kuitenkaan pakenema-an."
    discourseSegments := []
    glossedTokens := [("Eman", "Eman"), ("e-i", "NEG-3SG"), ("onnistu-nut", "succeed-SG.PP"), ("kuitenkaan", "however"), ("pakenema-an", "flee-INF.ILL")]
    translation := "Eman did not manage to flee."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "onnistua"), ("matrix", "negated"), ("entails", "negation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_4a : LinguisticExample :=
  { id := "nadathur2023_4a"
    source := ⟨"nadathur-2023-implicatives", "(4a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno uskals-i avat-a ove-n."
    discourseSegments := []
    glossedTokens := [("Juno", "Juno"), ("uskals-i", "dare-PST.3SG"), ("avat-a", "open-INF"), ("ove-n", "door-GEN/ACC")]
    translation := "Juno dared to open the door."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "uskaltaa"), ("matrix", "positive"), ("entails", "complement")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_4b : LinguisticExample :=
  { id := "nadathur2023_4b"
    source := ⟨"nadathur-2023-implicatives", "(4b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno e-i uskalta-nut avat-a ove-a."
    discourseSegments := []
    glossedTokens := [("Juno", "Juno"), ("e-i", "NEG-3SG"), ("uskalta-nut", "dare-SG.PP"), ("avat-a", "open-INF"), ("ove-a", "door-PART")]
    translation := "Juno did not dare to open the door."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "uskaltaa"), ("matrix", "negated"), ("entails", "negation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_5a : LinguisticExample :=
  { id := "nadathur2023_5a"
    source := ⟨"nadathur-2023-implicatives", "(5a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Sampo jakso-i noust-a."
    discourseSegments := []
    glossedTokens := [("Sampo", "Sampo"), ("jakso-i", "have.strength-PST.3SG"), ("noust-a", "rise-INF")]
    translation := "Sampo had strength to rise."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "jaksaa"), ("matrix", "positive"), ("entails", "nothing")]
    comment := "The complement is implicated, not entailed."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_5b : LinguisticExample :=
  { id := "nadathur2023_5b"
    source := ⟨"nadathur-2023-implicatives", "(5b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Sampo e-i jaksa-nut noust-a."
    discourseSegments := []
    glossedTokens := [("Sampo", "Sampo"), ("e-i", "NEG-3SG"), ("jaksa-nut", "have.strength-PP.SG"), ("noust-a", "rise-INF")]
    translation := "Sampo did not have strength to rise."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "jaksaa"), ("matrix", "negated"), ("entails", "negation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_10a : LinguisticExample :=
  { id := "nadathur2023_10a"
    source := ⟨"nadathur-2023-implicatives", "(10a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän viits-i vastat-a."
    discourseSegments := []
    glossedTokens := [("Hän", "he.NOM"), ("viits-i", "bother-PST.3SG"), ("vastat-a", "answer-INF")]
    translation := "He bothered to answer."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "viitsiä"), ("matrix", "positive"), ("entails", "complement")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_10b : LinguisticExample :=
  { id := "nadathur2023_10b"
    source := ⟨"nadathur-2023-implicatives", "(10b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i viitsi-nyt vastat-a."
    discourseSegments := []
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("viitsi-nyt", "bother-PP.SG"), ("vastat-a", "answer-INF")]
    translation := "He didn't bother to answer."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "viitsiä"), ("matrix", "negated"), ("entails", "negation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_11a : LinguisticExample :=
  { id := "nadathur2023_11a"
    source := ⟨"nadathur-2023-implicatives", "(11a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Marja maltto-i odotta-a."
    discourseSegments := []
    glossedTokens := [("Marja", "Marja"), ("maltto-i", "have.patience-PST.3SG"), ("odotta-a", "wait-INF")]
    translation := "Marja had the patience to wait."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "malttaa"), ("matrix", "positive"), ("entails", "complement")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_11b : LinguisticExample :=
  { id := "nadathur2023_11b"
    source := ⟨"nadathur-2023-implicatives", "(11b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Marja e-i maltta-nut odotta-a."
    discourseSegments := []
    glossedTokens := [("Marja", "Marja"), ("e-i", "NEG-3SG"), ("maltta-nut", "have.patience-SG.PP"), ("odotta-a", "wait-INF")]
    translation := "Marja did not have the patience to wait."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "malttaa"), ("matrix", "negated"), ("entails", "negation")]
    comment := "The source prints no final period."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_27a : LinguisticExample :=
  { id := "nadathur2023_27a"
    source := ⟨"nadathur-2023-implicatives", "(27a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän henno-i tappa-a kissa-n."
    discourseSegments := []
    glossedTokens := [("Hän", "he.NOM"), ("henno-i", "have.heart-PST.3SG"), ("tappa-a", "kill-INF"), ("kissa-n", "cat-GEN/ACC")]
    translation := "He had the heart to kill the cat."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hennoa"), ("matrix", "positive"), ("entails", "complement")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_27b : LinguisticExample :=
  { id := "nadathur2023_27b"
    source := ⟨"nadathur-2023-implicatives", "(27b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i henno-nut tappa-a kissa-a."
    discourseSegments := []
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("henno-nut", "have.heart-SG.PP"), ("tappa-a", "kill-INF"), ("kissa-a", "cat-PART")]
    translation := "He didn't have the heart to kill the cat."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hennoa"), ("matrix", "negated"), ("entails", "negation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_29a : LinguisticExample :=
  { id := "nadathur2023_29a"
    source := ⟨"nadathur-2023-implicatives", "(29a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Maarit pysty-i tappelema-an."
    discourseSegments := []
    glossedTokens := [("Maarit", "Maarit"), ("pysty-i", "able-PST.3SG"), ("tappelema-an", "fight-INF")]
    translation := "Maarit was able to fight."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "pystyä"), ("matrix", "positive"), ("entails", "nothing")]
    comment := "The complement is implicated, not entailed."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_29b : LinguisticExample :=
  { id := "nadathur2023_29b"
    source := ⟨"nadathur-2023-implicatives", "(29b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Maarit e-i pysty-nyt tappelema-an."
    discourseSegments := []
    glossedTokens := [("Maarit", "Maarit"), ("e-i", "NEG-3SG"), ("pysty-nyt", "able-SG.PP"), ("tappelema-an", "fight-INF")]
    translation := "Maarit was not able to fight."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "pystyä"), ("matrix", "negated"), ("entails", "negation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_30a : LinguisticExample :=
  { id := "nadathur2023_30a"
    source := ⟨"nadathur-2023-implicatives", "(30a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Freija mahtu-i kulke-ma-an ove-sta."
    discourseSegments := []
    glossedTokens := [("Freija", "Freija"), ("mahtu-i", "fit-PST.3SG"), ("kulke-ma-an", "go-INF-ILL"), ("ove-sta", "door-ELA")]
    translation := "Freija fit through the door."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "mahtua"), ("matrix", "positive"), ("entails", "nothing")]
    comment := "The complement is implicated, not entailed."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_30b : LinguisticExample :=
  { id := "nadathur2023_30b"
    source := ⟨"nadathur-2023-implicatives", "(30b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Freija e-i mahtu-nut kulke-ma-an ove-sta."
    discourseSegments := []
    glossedTokens := [("Freija", "Freija"), ("e-i", "NEG-3SG"), ("mahtu-nut", "fit-PP.SG"), ("kulke-ma-an", "go-INF-ILL"), ("ove-sta", "door-ELA")]
    translation := "Freija did not fit through the door."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "mahtua"), ("matrix", "negated"), ("entails", "negation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_44a : LinguisticExample :=
  { id := "nadathur2023_44a"
    source := ⟨"nadathur-2023-implicatives", "(44a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän laiminlö-i korjat-a virhee-n."
    discourseSegments := []
    glossedTokens := [("Hän", "he.NOM"), ("laiminlö-i", "neglect-PST.3SG"), ("korjat-a", "repair-INF"), ("virhee-n", "error-GEN/ACC")]
    translation := "He neglected to correct the error."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "laiminlyödä"), ("matrix", "positive"), ("entails", "negation")]
    comment := "The source prints the pair under (43) without its number, which the text gives as (44)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_44b : LinguisticExample :=
  { id := "nadathur2023_44b"
    source := ⟨"nadathur-2023-implicatives", "(44b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i laiminlyö-nyt korjat-a virhe-ttä."
    discourseSegments := []
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("laiminlyö-nyt", "neglect-PP.SG"), ("korjat-a", "repair-INF"), ("virhe-ttä", "error-PART")]
    translation := "He did not neglect to repair the error."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "laiminlyödä"), ("matrix", "negated"), ("entails", "complement")]
    comment := "The source prints the pair under (43) without its number, which the text gives as (44)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_46a : LinguisticExample :=
  { id := "nadathur2023_46a"
    source := ⟨"nadathur-2023-implicatives", "(46a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno epärö-i otta-a osa-a kilpailu-un."
    discourseSegments := []
    glossedTokens := [("Juno", "Juno"), ("epärö-i", "hesitate-PST.3SG"), ("otta-a", "take-INF"), ("osa-a", "part-PART"), ("kilpailu-un", "race-ILL")]
    translation := "Juno hesitated to take part in the race."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "epäröidä"), ("matrix", "positive"), ("entails", "nothing")]
    comment := "The source prints no final period."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_46b : LinguisticExample :=
  { id := "nadathur2023_46b"
    source := ⟨"nadathur-2023-implicatives", "(46b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno e-i epäröi-nyt otta-a osa-a kilpailu-un."
    discourseSegments := []
    glossedTokens := [("Juno", "Juno"), ("e-i", "NEG-3SG"), ("epäröi-nyt", "hesitate-PP.SG"), ("otta-a", "take-INF"), ("osa-a", "part-PART"), ("kilpailu-un", "race-ILL")]
    translation := "Juno did not hesitate to take part in the race."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "epäröidä"), ("matrix", "negated"), ("entails", "complement")]
    comment := "The source prints no final period."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [ex_2a, ex_2b, ex_4a, ex_4b, ex_5a, ex_5b, ex_10a, ex_10b, ex_11a, ex_11b, ex_27a, ex_27b, ex_29a, ex_29b, ex_30a, ex_30b, ex_44a, ex_44b, ex_46a, ex_46b]

end Nadathur2023.Examples
