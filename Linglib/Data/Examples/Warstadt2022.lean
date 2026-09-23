module

public import Linglib.Data.Examples.Schema

/-!
# `Warstadt2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Warstadt2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Warstadt2022.Examples`.
-/

@[expose] public section

namespace Warstadt2022.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "warstadt2022_1"
    source := ⟨"warstadt-2022", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom doesn't have a green card."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Does Tom need a visa?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("presupposition", "Tom is a non-US citizen"), ("projection", "projects"), ("qud", "need visa")]
    comment := "Negating the species predicate triggers the defeasible genus inference under this question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "warstadt2022_2"
    source := ⟨"warstadt-2022", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom doesn't have a green card."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Can Tom get a free drink? The local bar is giving free drinks to anyone with a green card."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("presupposition", "Tom is a non-US citizen"), ("projection", "absent"), ("qud", "free drink")]
    comment := "Under the free-drink question the genus inference is reported to be absent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "warstadt2022_3"
    source := ⟨"warstadt-2022", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of the new hires has a green card."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("presupposition", "the new hires are non-US citizens"), ("projection", "universal")]
    comment := "The genus inference projects universally out of the quantifier."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "warstadt2022_4"
    source := ⟨"warstadt-2022", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom is not an Olympic sprinter."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("level", "species"), ("inference", "Tom is an athlete"), ("strength", "stronger")]
    comment := "Negating the species predicate projects the family predicate more strongly than negating the genus."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "warstadt2022_5"
    source := ⟨"warstadt-2022", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom is not a runner."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("level", "genus"), ("inference", "Tom is an athlete"), ("strength", "weaker")]
    comment := "Negating the genus predicate projects the family predicate only weakly."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "warstadt2022_6"
    source := ⟨"warstadt-2022", "(4c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom is an athlete."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("level", "family")]
    comment := "The family-level inference of (4a) and (4b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "warstadt2022_7"
    source := ⟨"warstadt-2022", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did he recently stop smoking?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Why is Tom chewing on his pencil?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "stop"), ("projection", "reduced")]
    comment := "Geurts's example: under this question there is less need to accommodate that Tom smoked."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7]

end Warstadt2022.Examples
