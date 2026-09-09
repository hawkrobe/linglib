import Linglib.Data.Examples.Schema

/-!
# `Gajewski2011` — typed example data

Auto-generated from `Linglib/Data/Examples/Gajewski2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gajewski2011.Examples`.
-/

namespace Gajewski2011.Examples

open Data.Examples

def ex20a : LinguisticExample :=
  { id := "gajewski2011_ex20a"
    source := ⟨"gajewski-2011", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No doctor has seen anyone."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "no"), ("strength", "weak"), ("npi", "anyone"), ("grammatical", "yes")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex21a : LinguisticExample :=
  { id := "gajewski2011_ex21a"
    source := ⟨"gajewski-2011", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No doctor has seen Mary in weeks."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "no"), ("strength", "strong"), ("npi", "in weeks"), ("grammatical", "yes")]
    comment := "No sits at the end of its scale, so its enriched meaning is its plain, downward-entailing meaning."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex20b : LinguisticExample :=
  { id := "gajewski2011_ex20b"
    source := ⟨"gajewski-2011", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most five doctors have seen anyone."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "atMostFive"), ("strength", "weak"), ("npi", "anyone"), ("grammatical", "yes")]
    comment := "Downward entailing but not anti-additive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex21b : LinguisticExample :=
  { id := "gajewski2011_ex21b"
    source := ⟨"gajewski-2011", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most five doctors have seen Mary in weeks."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "atMostFive"), ("strength", "strong"), ("npi", "in weeks"), ("grammatical", "no")]
    comment := "Excluding the stronger alternative at most four leaves exactly five, which is not downward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex1f : LinguisticExample :=
  { id := "gajewski2011_ex1f"
    source := ⟨"gajewski-2011", "(1f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some student ever said anything."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "some"), ("strength", "weak"), ("npi", "ever"), ("grammatical", "no")]
    comment := "Upward entailing in its scope."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2f : LinguisticExample :=
  { id := "gajewski2011_ex2f"
    source := ⟨"gajewski-2011", "(2f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some students left until their birthdays."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "some"), ("strength", "strong"), ("npi", "until"), ("grammatical", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex26a : LinguisticExample :=
  { id := "gajewski2011_ex26a"
    source := ⟨"gajewski-2011", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John has ever seen anyone."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "only"), ("strength", "weak"), ("npi", "ever, anyone"), ("grammatical", "yes")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex26b : LinguisticExample :=
  { id := "gajewski2011_ex26b"
    source := ⟨"gajewski-2011", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John has seen Mary in weeks."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "only"), ("strength", "strong"), ("npi", "in weeks"), ("grammatical", "no")]
    comment := "Only's presupposition that the focus satisfies the scope is upward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex26c : LinguisticExample :=
  { id := "gajewski2011_ex26c"
    source := ⟨"gajewski-2011", "(26c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John likes pancakes, either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "only"), ("strength", "strong"), ("npi", "either"), ("grammatical", "no")]
    comment := "Only's presupposition that the focus satisfies the scope is upward entailing. The paper credits the example to Nathan (1999)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex26d : LinguisticExample :=
  { id := "gajewski2011_ex26d"
    source := ⟨"gajewski-2011", "(26d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John arrived until his birthday."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "only"), ("strength", "strong"), ("npi", "until"), ("grammatical", "no")]
    comment := "Only's presupposition that the focus satisfies the scope is upward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex27a : LinguisticExample :=
  { id := "gajewski2011_ex27a"
    source := ⟨"gajewski-2011", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill has ever seen anyone, he is keeping it a secret."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "conditional"), ("strength", "weak"), ("npi", "ever, anyone"), ("grammatical", "yes")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex27b : LinguisticExample :=
  { id := "gajewski2011_ex27b"
    source := ⟨"gajewski-2011", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill has seen Mary in weeks, he is keeping it a secret."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "conditional"), ("strength", "strong"), ("npi", "in weeks"), ("grammatical", "no")]
    comment := "The conditional's presupposition that its antecedent is possible is upward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex27c : LinguisticExample :=
  { id := "gajewski2011_ex27c"
    source := ⟨"gajewski-2011", "(27c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill likes pancakes, either, he is keeping it a secret."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "conditional"), ("strength", "strong"), ("npi", "either"), ("grammatical", "no")]
    comment := "The conditional's presupposition that its antecedent is possible is upward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex27d : LinguisticExample :=
  { id := "gajewski2011_ex27d"
    source := ⟨"gajewski-2011", "(27d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill arrived until Friday, he is keeping it a secret."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "conditional"), ("strength", "strong"), ("npi", "until"), ("grammatical", "no")]
    comment := "The conditional's presupposition that its antecedent is possible is upward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex28a : LinguisticExample :=
  { id := "gajewski2011_ex28a"
    source := ⟨"gajewski-2011", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is sorry that she ever talked to anyone."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "sorry"), ("strength", "weak"), ("npi", "ever, anyone"), ("grammatical", "yes")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex28b : LinguisticExample :=
  { id := "gajewski2011_ex28b"
    source := ⟨"gajewski-2011", "(28b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is sorry that she has talked to Bill in weeks."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "sorry"), ("strength", "strong"), ("npi", "in weeks"), ("grammatical", "no")]
    comment := "The factive presupposition of sorry is upward entailing in the complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex28c : LinguisticExample :=
  { id := "gajewski2011_ex28c"
    source := ⟨"gajewski-2011", "(28c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is sorry that she likes pancakes, either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "sorry"), ("strength", "strong"), ("npi", "either"), ("grammatical", "no")]
    comment := "The factive presupposition of sorry is upward entailing in the complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex28d : LinguisticExample :=
  { id := "gajewski2011_ex28d"
    source := ⟨"gajewski-2011", "(28d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is sorry that she arrived until Friday."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "sorry"), ("strength", "strong"), ("npi", "until"), ("grammatical", "no")]
    comment := "The factive presupposition of sorry is upward entailing in the complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex20a, ex21a, ex20b, ex21b, ex1f, ex2f, ex26a, ex26b, ex26c, ex26d, ex27a, ex27b, ex27c, ex27d, ex28a, ex28b, ex28c, ex28d]

end Gajewski2011.Examples
