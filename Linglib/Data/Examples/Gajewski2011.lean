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

def ex14a : LinguisticExample :=
  { id := "gajewski2011_ex14a"
    source := ⟨"gajewski-2011", "(14a)"⟩
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
    paperFeatures := [("licenser", "no"), ("strength", "weak"), ("npi", "anyone")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex15a : LinguisticExample :=
  { id := "gajewski2011_ex15a"
    source := ⟨"gajewski-2011", "(15a)"⟩
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
    paperFeatures := [("licenser", "no"), ("strength", "strong"), ("npi", "in weeks")]
    comment := "No sits at the end of its scale, so its enriched meaning is its plain, downward-entailing meaning."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex14b : LinguisticExample :=
  { id := "gajewski2011_ex14b"
    source := ⟨"gajewski-2011", "(14b)"⟩
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
    paperFeatures := [("licenser", "atMostFive"), ("strength", "weak"), ("npi", "anyone")]
    comment := "Downward entailing but not anti-additive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex15b : LinguisticExample :=
  { id := "gajewski2011_ex15b"
    source := ⟨"gajewski-2011", "(15b)"⟩
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
    paperFeatures := [("licenser", "atMostFive"), ("strength", "strong"), ("npi", "in weeks")]
    comment := "Excluding the stronger alternative at most four leaves exactly five, which is not downward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex1f : LinguisticExample :=
  { id := "gajewski2011_ex1f"
    source := ⟨"gajewski-2011", "(1f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some students ever said anything."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "some"), ("strength", "weak"), ("npi", "ever")]
    comment := "Upward entailing in its scope."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7f : LinguisticExample :=
  { id := "gajewski2011_ex7f"
    source := ⟨"gajewski-2011", "(7f)"⟩
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
    paperFeatures := [("licenser", "some"), ("strength", "strong"), ("npi", "until")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39a : LinguisticExample :=
  { id := "gajewski2011_ex39a"
    source := ⟨"gajewski-2011", "(39a)"⟩
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
    paperFeatures := [("licenser", "only"), ("strength", "weak"), ("npi", "ever, anyone")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39b : LinguisticExample :=
  { id := "gajewski2011_ex39b"
    source := ⟨"gajewski-2011", "(39b)"⟩
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
    paperFeatures := [("licenser", "only"), ("strength", "strong"), ("npi", "in weeks")]
    comment := "Only's presupposition that the focus satisfies the scope is upward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39c : LinguisticExample :=
  { id := "gajewski2011_ex39c"
    source := ⟨"gajewski-2011", "(39c)"⟩
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
    paperFeatures := [("licenser", "only"), ("strength", "strong"), ("npi", "either")]
    comment := "Only's presupposition that the focus satisfies the scope is upward entailing. The paper credits the example to Nathan (1999)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39d : LinguisticExample :=
  { id := "gajewski2011_ex39d"
    source := ⟨"gajewski-2011", "(39d)"⟩
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
    paperFeatures := [("licenser", "only"), ("strength", "strong"), ("npi", "until")]
    comment := "Only's presupposition that the focus satisfies the scope is upward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40a : LinguisticExample :=
  { id := "gajewski2011_ex40a"
    source := ⟨"gajewski-2011", "(40a)"⟩
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
    paperFeatures := [("licenser", "conditional"), ("strength", "weak"), ("npi", "ever, anyone")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40b : LinguisticExample :=
  { id := "gajewski2011_ex40b"
    source := ⟨"gajewski-2011", "(40b)"⟩
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
    paperFeatures := [("licenser", "conditional"), ("strength", "strong"), ("npi", "in weeks")]
    comment := "The conditional's presupposition that its antecedent is possible is upward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40c : LinguisticExample :=
  { id := "gajewski2011_ex40c"
    source := ⟨"gajewski-2011", "(40c)"⟩
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
    paperFeatures := [("licenser", "conditional"), ("strength", "strong"), ("npi", "either")]
    comment := "The conditional's presupposition that its antecedent is possible is upward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40d : LinguisticExample :=
  { id := "gajewski2011_ex40d"
    source := ⟨"gajewski-2011", "(40d)"⟩
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
    paperFeatures := [("licenser", "conditional"), ("strength", "strong"), ("npi", "until")]
    comment := "The conditional's presupposition that its antecedent is possible is upward entailing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41a : LinguisticExample :=
  { id := "gajewski2011_ex41a"
    source := ⟨"gajewski-2011", "(41a)"⟩
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
    paperFeatures := [("licenser", "sorry"), ("strength", "weak"), ("npi", "ever, anyone")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41b : LinguisticExample :=
  { id := "gajewski2011_ex41b"
    source := ⟨"gajewski-2011", "(41b)"⟩
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
    paperFeatures := [("licenser", "sorry"), ("strength", "strong"), ("npi", "in weeks")]
    comment := "The factive presupposition of sorry is upward entailing in the complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41c : LinguisticExample :=
  { id := "gajewski2011_ex41c"
    source := ⟨"gajewski-2011", "(41c)"⟩
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
    paperFeatures := [("licenser", "sorry"), ("strength", "strong"), ("npi", "either")]
    comment := "The factive presupposition of sorry is upward entailing in the complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41d : LinguisticExample :=
  { id := "gajewski2011_ex41d"
    source := ⟨"gajewski-2011", "(41d)"⟩
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
    paperFeatures := [("licenser", "sorry"), ("strength", "strong"), ("npi", "until")]
    comment := "The factive presupposition of sorry is upward entailing in the complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex14a, ex15a, ex14b, ex15b, ex1f, ex7f, ex39a, ex39b, ex39c, ex39d, ex40a, ex40b, ex40c, ex40d, ex41a, ex41b, ex41c, ex41d]

end Gajewski2011.Examples
