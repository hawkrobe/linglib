import Linglib.Data.Examples.Schema

/-!
# `HahnDegenFutrell2021` — typed example data

Auto-generated from `Linglib/Data/Examples/HahnDegenFutrell2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HahnDegenFutrell2021.Examples`.
-/

namespace HahnDegenFutrell2021.Examples

open Data.Examples

def ex2a : LinguisticExample :=
  { id := "hahndegenfutrell2021_ex2a"
    source := ⟨"hahn-degen-futrell-2021", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate the broccoli with a fork."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")]
    comment := "NP objects ordinarily precede PPs; the paper takes the example from Staub et al. (2006)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2b : LinguisticExample :=
  { id := "hahndegenfutrell2021_ex2b"
    source := ⟨"hahn-degen-futrell-2021", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate with a fork the broccoli."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2c : LinguisticExample :=
  { id := "hahndegenfutrell2021_ex2c"
    source := ⟨"hahn-degen-futrell-2021", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate the extremely delicious, bright green broccoli with a fork."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")]
    comment := "Less preferred with a long NP: the verb and the PP are far apart."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2d : LinguisticExample :=
  { id := "hahndegenfutrell2021_ex2d"
    source := ⟨"hahn-degen-futrell-2021", "(2d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate with a fork the extremely delicious, bright green broccoli."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")]
    comment := "Heavy NP shift: shortens the verb-to-PP dependency while only modestly lengthening the verb-to-object one."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex2a, ex2b, ex2c, ex2d]

end HahnDegenFutrell2021.Examples
