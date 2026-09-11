import Linglib.Data.Examples.Schema

/-!
# `Hudson2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Hudson2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hudson2010.Examples`.
-/

namespace Hudson2010.Examples

open Data.Examples

def ch7_11 : LinguisticExample :=
  { id := "hudson2010_ch7_11"
    source := ⟨"hudson-2010", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has swum."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.6"), ("triangle", "he is the subject of has and of swum"), ("verb", "HAVE")]
    comment := "The swimmer is he, so he depends as subject on swum as well as on has."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch7_12 : LinguisticExample :=
  { id := "hudson2010_ch7_12"
    source := ⟨"hudson-2010", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There was an accident."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.6"), ("subject", "meaningless there"), ("verb", "BE")]
    comment := "Meaningless there is licensed only by the valency of BE."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch7_13 : LinguisticExample :=
  { id := "hudson2010_ch7_13"
    source := ⟨"hudson-2010", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Was there an accident?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.6"), ("subject", "there"), ("construction", "inversion test for subjecthood")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch7_14 : LinguisticExample :=
  { id := "hudson2010_ch7_14"
    source := ⟨"hudson-2010", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There has been an accident."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.6"), ("triangle", "there is the subject of has and of been"), ("verb", "HAVE")]
    comment := "Syntactic evidence for the triangle: there must be the subject of a form of BE."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch7_8 : LinguisticExample :=
  { id := "hudson2010_ch7_8"
    source := ⟨"hudson-2010", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He keeps talking."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.4.4"), ("triangle", "he is the subject of keeps and of talking"), ("landmark", "keeps")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch7_9 : LinguisticExample :=
  { id := "hudson2010_ch7_9"
    source := ⟨"hudson-2010", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Keeps he talking."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.4.4"), ("landmark", "talking"), ("rule", "a verb's subject stands just before it")]
    comment := "The subject's landmark is the higher verb keeps, not talking."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch7_10 : LinguisticExample :=
  { id := "hudson2010_ch7_10"
    source := ⟨"hudson-2010", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He never keeps talking."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.4.4"), ("adverb", "never between the subject and its landmark verb")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch7_11b : LinguisticExample :=
  { id := "hudson2010_ch7_11b"
    source := ⟨"hudson-2010", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He keeps never talking."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.4.4"), ("adverb", "never between the subject and the lower verb")]
    comment := "Section 7.4.4's second (11), the adverb test for the landmark."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def fig7_12 : LinguisticExample :=
  { id := "hudson2010_fig7_12"
    source := ⟨"hudson-2010", "Figure 7.12"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He keeps seeming to have forgotten to go."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.4.4"), ("triangle", "he is the subject of every verb in the valent chain"), ("recursion", "triangles multiplied freely")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ch7_11, ch7_12, ch7_13, ch7_14, ch7_8, ch7_9, ch7_10, ch7_11b, fig7_12]

end Hudson2010.Examples
