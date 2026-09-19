import Linglib.Data.Examples.Schema

/-!
# `CoppockWechsler2018` — typed example data

Auto-generated from `Linglib/Data/Examples/CoppockWechsler2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace CoppockWechsler2018.Examples`.
-/

namespace CoppockWechsler2018.Examples

open Data.Examples

def ex_27 : LinguisticExample :=
  { id := "coppockwechsler2018_27"
    source := ⟨"coppock-wechsler-2018", "(27)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "jĩ: a:pwa twan-ā"
    discourseSegments := []
    glossedTokens := [("jĩ:", "1.ERG"), ("a:pwa", "much"), ("twan-ā", "drink-PAST.EGO")]
    translation := "I drank-EGO a lot"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("clause", "declarative"), ("marking", "ego")]
    comment := "Repeated from the paper's (1a), after Hargreaves 2005."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_28 : LinguisticExample :=
  { id := "coppockwechsler2018_28"
    source := ⟨"coppock-wechsler-2018", "(28)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "chã a:pwa twan-ā"
    discourseSegments := []
    glossedTokens := [("chã", "2.ERG"), ("a:pwa", "much"), ("twan-ā", "drink-PAST.EGO")]
    translation := "You drank-EGO a lot."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("clause", "declarative"), ("marking", "ego")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_34a : LinguisticExample :=
  { id := "coppockwechsler2018_34a"
    source := ⟨"coppock-wechsler-2018", "(34a)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "jĩ a:pwa twan-ā lā"
    discourseSegments := []
    glossedTokens := [("jĩ", "1.ERG"), ("a:pwa", "much"), ("twan-ā", "drink-PAST.EGO"), ("lā", "Q")]
    translation := "Did I drink-EGO a lot?"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("clause", "interrogative"), ("marking", "ego")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_34b : LinguisticExample :=
  { id := "coppockwechsler2018_34b"
    source := ⟨"coppock-wechsler-2018", "(34b)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "jĩ: a:pwa twan-a lā"
    discourseSegments := []
    glossedTokens := [("jĩ:", "1.ERG"), ("a:pwa", "much"), ("twan-a", "drink-PERF"), ("lā", "Q")]
    translation := "Did I drink a lot?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("clause", "interrogative"), ("marking", "plain")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_35a : LinguisticExample :=
  { id := "coppockwechsler2018_35a"
    source := ⟨"coppock-wechsler-2018", "(35a)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "chã a:pwa twan-ā lā"
    discourseSegments := []
    glossedTokens := [("chã", "2.ERG"), ("a:pwa", "much"), ("twan-ā", "drink-PAST.EGO"), ("lā", "Q")]
    translation := "Did you drink-EGO a lot?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("clause", "interrogative"), ("marking", "ego")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_35b : LinguisticExample :=
  { id := "coppockwechsler2018_35b"
    source := ⟨"coppock-wechsler-2018", "(35b)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "chã a:pwa twan-a lā"
    discourseSegments := []
    glossedTokens := [("chã", "2.ERG"), ("a:pwa", "much"), ("twan-a", "drink-PERF"), ("lā", "Q")]
    translation := "Did you drink a lot?"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("clause", "interrogative"), ("marking", "plain")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_27, ex_28, ex_34a, ex_34b, ex_35a, ex_35b]

end CoppockWechsler2018.Examples
