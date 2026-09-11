import Linglib.Data.Examples.Schema

/-!
# `HeimKratzer1998` — typed example data

Auto-generated from `Linglib/Data/Examples/HeimKratzer1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HeimKratzer1998.Examples`.
-/

namespace HeimKratzer1998.Examples

open Data.Examples

def ch7_1a : LinguisticExample :=
  { id := "heimkratzer1998_ch7_1a"
    source := ⟨"heim-kratzer-1998", "Ch. 7 (1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every linguist offended John."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.1"), ("quantifier", "subject")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch7_1b : LinguisticExample :=
  { id := "heimkratzer1998_ch7_1b"
    source := ⟨"heim-kratzer-1998", "Ch. 7 (1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John offended every linguist."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.1"), ("quantifier", "object")]
    comment := "The type mismatch in object position that Quantifier Raising repairs (§7.3)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch7_2 : LinguisticExample :=
  { id := "heimkratzer1998_ch7_2"
    source := ⟨"heim-kratzer-1998", "Ch. 7 (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some publisher offended every linguist."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.1"), ("readings", "some > every; every > some")]
    comment := "Scope ambiguity: two Quantifier Raising derivations."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ch7_1a, ch7_1b, ch7_2]

end HeimKratzer1998.Examples
