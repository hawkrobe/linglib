import Linglib.Data.Examples.Schema

/-!
# `Jaeger2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Jaeger2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Jaeger2014.Examples`.
-/

namespace Jaeger2014.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "jaeger2014_1a"
    source := ⟨"jaeger-2014", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some boys came in."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not all boys came in", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "Q"), ("implicature", "Not all boys came in.")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1b : LinguisticExample :=
  { id := "jaeger2014_1b"
    source := ⟨"jaeger-2014", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three boys came in."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("exactly three boys came in", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "Q"), ("implicature", "Exactly three boys came in.")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3a : LinguisticExample :=
  { id := "jaeger2014_3a"
    source := ⟨"jaeger-2014", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's book is good."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the book that John is reading or that he has written is good", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "I")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3b : LinguisticExample :=
  { id := "jaeger2014_3b"
    source := ⟨"jaeger-2014", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a secretary"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("a female secretary", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "I")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3c : LinguisticExample :=
  { id := "jaeger2014_3c"
    source := ⟨"jaeger-2014", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "road"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("hard-surfaced road", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "I")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4a : LinguisticExample :=
  { id := "jaeger2014_4a"
    source := ⟨"jaeger-2014", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John stopped the car."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("John stopped the car in a regular way, using the foot brake", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "M"), ("signal", "f"), ("cost", "0"), ("world", "w1")]
    comment := "The cheap synonym of Example 6, read as the frequent world."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4b : LinguisticExample :=
  { id := "jaeger2014_4b"
    source := ⟨"jaeger-2014", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John made the car stop."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("John stopped the car in an abnormal way", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "M"), ("signal", "f'"), ("cost", "1"), ("world", "w2")]
    comment := "The costly synonym of Example 6, read as the rare world."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "jaeger2014_5"
    source := ⟨"jaeger-2014", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John brought the car to a stop."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("John stopped the car in a non-stereotypical way", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "M")]
    comment := "A third, still more complex form; pragmatic rationalizability predicts no further specialization between (4b) and (5), unlike bidirectional OT."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6a : LinguisticExample :=
  { id := "jaeger2014_6a"
    source := ⟨"jaeger-2014", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The distance is one hundred meter."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("vague, between 90 and 110 meter", .acceptable), ("precise", .acceptable)]
    paperFeatures := [("section", "5"), ("principle", "RN/RI"), ("precision", "low")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6b : LinguisticExample :=
  { id := "jaeger2014_6b"
    source := ⟨"jaeger-2014", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The distance is one hundred and one meter."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("precise, with a slack of at most 50 cm", .acceptable)]
    paperFeatures := [("section", "5"), ("principle", "RN/RI"), ("precision", "high")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "jaeger2014_7"
    source := ⟨"jaeger-2014", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The distance is exactly one hundred meter."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("precise", .acceptable)]
    paperFeatures := [("section", "5"), ("principle", "RN/RI"), ("precision", "high")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_1b, ex_3a, ex_3b, ex_3c, ex_4a, ex_4b, ex_5, ex_6a, ex_6b, ex_7]

end Jaeger2014.Examples
