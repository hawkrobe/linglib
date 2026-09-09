import Linglib.Data.Examples.Schema

/-!
# `Fox2007` — typed example data

Auto-generated from `Linglib/Data/Examples/Fox2007.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Fox2007.Examples`.
-/

namespace Fox2007.Examples

open Data.Examples

def ex16 : LinguisticExample :=
  { id := "fox2007_ex16"
    source := ⟨"kamp-1973", "free choice permission"⟩
    reportedIn := some ⟨"fox-2007", "(16)"⟩
    language := "stan1293"
    primaryText := "You're allowed to eat the cake or the ice-cream."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "possibility"), ("number", "none"), ("connective", "or"), ("scope", "narrow"), ("fc", "yes"), ("status", "accounted")]
    comment := "Free choice permission (17), Kamp's inference."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex21 : LinguisticExample :=
  { id := "fox2007_ex21"
    source := ⟨"fox-2007", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No one is allowed to eat the cake or the ice-cream."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("quantifier", "negatedPossibility"), ("number", "none"), ("connective", "or"), ("scope", "narrow"), ("fc", "no"), ("status", "accounted")]
    comment := "The negation of the standard meaning, not of free choice: no trace of FC under a downward-entailing operator."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex25 : LinguisticExample :=
  { id := "fox2007_ex25"
    source := ⟨"fox-2007", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are not required to both clear the table and do the dishes."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "negatedNecessity"), ("number", "none"), ("connective", "and"), ("scope", "narrow"), ("fc", "yes"), ("status", "accounted")]
    comment := "Inference (26): not required to clear the table and not required to do the dishes."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex28a : LinguisticExample :=
  { id := "fox2007_ex28a"
    source := ⟨"fox-2007", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book might be on the desk or in the drawer."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "possibility"), ("number", "none"), ("connective", "or"), ("scope", "narrow"), ("fc", "yes"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex28b : LinguisticExample :=
  { id := "fox2007_ex28b"
    source := ⟨"fox-2007", "(28b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He can climb Mt. Everest or ski the Matterhorn."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "possibility"), ("number", "none"), ("connective", "or"), ("scope", "narrow"), ("fc", "yes"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29a : LinguisticExample :=
  { id := "fox2007_ex29a"
    source := ⟨"fox-2007", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is beer in the fridge or the ice-bucket."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "existential"), ("number", "mass"), ("connective", "or"), ("scope", "narrow"), ("fc", "yes"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29b : LinguisticExample :=
  { id := "fox2007_ex29b"
    source := ⟨"fox-2007", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most people walk to the park, but some people take the highway or the scenic route."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "existential"), ("number", "plural"), ("connective", "or"), ("scope", "narrow"), ("fc", "yes"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29c : LinguisticExample :=
  { id := "fox2007_ex29c"
    source := ⟨"fox-2007", "(29c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This course is very difficult. In the past, some students waited 3 semesters to complete it or never finished it at all."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "existential"), ("number", "plural"), ("connective", "or"), ("scope", "narrow"), ("fc", "yes"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex30a : LinguisticExample :=
  { id := "fox2007_ex30a"
    source := ⟨"fox-2007", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a bottle of beer in the fridge or the ice-bucket."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("quantifier", "existential"), ("number", "singular"), ("connective", "or"), ("scope", "narrow"), ("fc", "no"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex30c : LinguisticExample :=
  { id := "fox2007_ex30c"
    source := ⟨"fox-2007", "(30c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone took the highway or the scenic route."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("quantifier", "existential"), ("number", "singular"), ("connective", "or"), ("scope", "narrow"), ("fc", "no"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex30d : LinguisticExample :=
  { id := "fox2007_ex30d"
    source := ⟨"fox-2007", "(30d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This course is very difficult. In the past, some student waited 3 semesters to complete it or never finished it at all."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("quantifier", "existential"), ("number", "singular"), ("connective", "or"), ("scope", "narrow"), ("fc", "no"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex32 : LinguisticExample :=
  { id := "fox2007_ex32"
    source := ⟨"fox-2007", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We didn't give every student of ours both a stipend and a tuition waiver."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "negatedUniversal"), ("number", "none"), ("connective", "and"), ("scope", "narrow"), ("fc", "yes"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex34a : LinguisticExample :=
  { id := "fox2007_ex34a"
    source := ⟨"fox-2007", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I didn't talk to both John and Bill."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("quantifier", "negation"), ("number", "none"), ("connective", "and"), ("scope", "narrow"), ("fc", "no"), ("status", "accounted")]
    comment := "Conjunction does not outscope negation without an intervening universal."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex34b : LinguisticExample :=
  { id := "fox2007_ex34b"
    source := ⟨"fox-2007", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We didn't give both a stipend and a tuition waiver to every student."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("quantifier", "negation"), ("number", "none"), ("connective", "and"), ("scope", "narrow"), ("fc", "no"), ("status", "accounted")]
    comment := "Surface scope of the conjunction above the universal."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex91a : LinguisticExample :=
  { id := "fox2007_ex91a"
    source := ⟨"fox-2007", "(91a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We may either eat the cake or the ice-cream."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "possibility"), ("number", "none"), ("connective", "or"), ("scope", "narrow"), ("fc", "yes"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex91b : LinguisticExample :=
  { id := "fox2007_ex91b"
    source := ⟨"fox-2007", "(91b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either we may eat the cake or the ice-cream."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("quantifier", "possibility"), ("number", "none"), ("connective", "or"), ("scope", "wide"), ("fc", "no"), ("status", "accounted")]
    comment := "Either marks wide scope of the disjunction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex92 : LinguisticExample :=
  { id := "fox2007_ex92"
    source := ⟨"zimmermann-2000", "free choice disjunction"⟩
    reportedIn := some ⟨"fox-2007", "(92)"⟩
    language := "stan1293"
    primaryText := "You may eat the cake or you may eat the ice-cream."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "possibility"), ("number", "none"), ("connective", "or"), ("scope", "wide"), ("fc", "yes"), ("status", "open")]
    comment := "Zimmermann's observation; the paper leaves it unresolved."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex93a : LinguisticExample :=
  { id := "fox2007_ex93a"
    source := ⟨"fox-2007", "(93a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some students waited 3 semesters to complete this course or never finished it at all."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "existential"), ("number", "plural"), ("connective", "or"), ("scope", "narrow"), ("fc", "yes"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex93b : LinguisticExample :=
  { id := "fox2007_ex93b"
    source := ⟨"fox-2007", "(93b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some students either waited 3 semesters to complete this course or never finished it at all."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("quantifier", "existential"), ("number", "plural"), ("connective", "or"), ("scope", "narrow"), ("fc", "yes"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex93c : LinguisticExample :=
  { id := "fox2007_ex93c"
    source := ⟨"fox-2007", "(93c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either some students waited 3 semesters to complete this course or some students never finished it at all."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("quantifier", "existential"), ("number", "plural"), ("connective", "or"), ("scope", "wide"), ("fc", "no"), ("status", "accounted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex16, ex21, ex25, ex28a, ex28b, ex29a, ex29b, ex29c, ex30a, ex30c, ex30d, ex32, ex34a, ex34b, ex91a, ex91b, ex92, ex93a, ex93b, ex93c]

end Fox2007.Examples
