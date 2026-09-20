import Linglib.Data.Examples.Schema

/-!
# `Blok2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Blok2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Blok2015.Examples`.
-/

namespace Blok2015.Examples

open Data.Examples

def ex_3a : LinguisticExample :=
  { id := "blok2015_3a"
    source := ⟨"blok-2015", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most three students will show up to the lecture, if any."
    discourseSegments := []
    glossedTokens := []
    translation := "At most three students will show up to the lecture, if any."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "-"), ("test", "ifAny"), ("numeral", "3")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3b : LinguisticExample :=
  { id := "blok2015_3b"
    source := ⟨"blok-2015", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Up to three students will show up to the lecture, if any."
    discourseSegments := []
    glossedTokens := []
    translation := "Up to three students will show up to the lecture, if any."
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "+"), ("test", "ifAny"), ("numeral", "3")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4a : LinguisticExample :=
  { id := "blok2015_4a"
    source := ⟨"blok-2015", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I expect to see at most ten people, but maybe no-one will show up."
    discourseSegments := []
    glossedTokens := []
    translation := "I expect to see at most ten people, but maybe no-one will show up."
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "-"), ("test", "butNone"), ("numeral", "10")]
    comment := "Provided by a reviewer."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4b : LinguisticExample :=
  { id := "blok2015_4b"
    source := ⟨"blok-2015", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I expect to see up to ten people, but maybe no-one will show up."
    discourseSegments := []
    glossedTokens := []
    translation := "I expect to see up to ten people, but maybe no-one will show up."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "+"), ("test", "butNone"), ("numeral", "10")]
    comment := "Provided by a reviewer."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7a : LinguisticExample :=
  { id := "blok2015_7a"
    source := ⟨"blok-2015", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most ten people died in the crash, perhaps even more."
    discourseSegments := []
    glossedTokens := []
    translation := "At most ten people died in the crash, perhaps even more."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "-"), ("test", "evenMore"), ("numeral", "10")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7b : LinguisticExample :=
  { id := "blok2015_7b"
    source := ⟨"blok-2015", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Up to ten people died in the crash, perhaps even more."
    discourseSegments := []
    glossedTokens := []
    translation := "Up to ten people died in the crash, perhaps even more."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "+"), ("test", "evenMore"), ("numeral", "10")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11a : LinguisticExample :=
  { id := "blok2015_11a"
    source := ⟨"blok-2015", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You're allowed to choose at most ten presents, but no more than that."
    discourseSegments := []
    glossedTokens := []
    translation := "You're allowed to choose at most ten presents, but no more than that."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "-"), ("test", "noMore"), ("numeral", "10")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11b : LinguisticExample :=
  { id := "blok2015_11b"
    source := ⟨"blok-2015", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You're allowed to choose up to ten presents, but no more than that."
    discourseSegments := []
    glossedTokens := []
    translation := "You're allowed to choose up to ten presents, but no more than that."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "+"), ("test", "noMore"), ("numeral", "10")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22a : LinguisticExample :=
  { id := "blok2015_22a"
    source := ⟨"schwarz-buccola-hamilton-2012", "(21a)"⟩
    reportedIn := some ⟨"blok-2015", "(22a)"⟩
    language := "stan1293"
    primaryText := "At most ten people died in the crash."
    discourseSegments := []
    glossedTokens := []
    translation := "At most ten people died in the crash."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "-"), ("test", "range"), ("numeral", "10")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22b : LinguisticExample :=
  { id := "blok2015_22b"
    source := ⟨"schwarz-buccola-hamilton-2012", "(22a)"⟩
    reportedIn := some ⟨"blok-2015", "(22b)"⟩
    language := "stan1293"
    primaryText := "At most one person died in the crash."
    discourseSegments := []
    glossedTokens := []
    translation := "At most one person died in the crash."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "-"), ("test", "range"), ("numeral", "1")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23a : LinguisticExample :=
  { id := "blok2015_23a"
    source := ⟨"schwarz-buccola-hamilton-2012", "(21b)"⟩
    reportedIn := some ⟨"blok-2015", "(23a)"⟩
    language := "stan1293"
    primaryText := "Up to ten people died in the crash."
    discourseSegments := []
    glossedTokens := []
    translation := "Up to ten people died in the crash."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "+"), ("test", "range"), ("numeral", "10")]
    comment := "Cited in the source from Nouwen 2008."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23b : LinguisticExample :=
  { id := "blok2015_23b"
    source := ⟨"schwarz-buccola-hamilton-2012", "(22b)"⟩
    reportedIn := some ⟨"blok-2015", "(23b)"⟩
    language := "stan1293"
    primaryText := "Up to one person died in the crash."
    discourseSegments := []
    glossedTokens := []
    translation := "Up to one person died in the crash."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "+"), ("test", "range"), ("numeral", "1")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_29 : LinguisticExample :=
  { id := "blok2015_29"
    source := ⟨"blok-2015", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most 0 people died in the crash."
    discourseSegments := []
    glossedTokens := []
    translation := "At most 0 people died in the crash."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "-"), ("test", "range"), ("numeral", "0")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_34a : LinguisticExample :=
  { id := "blok2015_34a"
    source := ⟨"blok-2015", "(34a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Er hoeven maximaal vijf studenten te komen."
    discourseSegments := []
    glossedTokens := [("Er", "there"), ("hoeven", "must.NPI"), ("maximaal", "maximally"), ("vijf", "five"), ("studenten", "students"), ("te", "to"), ("komen", "come")]
    translation := "At most five students have to show up."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("directional", "-"), ("test", "npi"), ("numeral", "5")]
    comment := "The modal hoeven is a negative polarity item."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_34b : LinguisticExample :=
  { id := "blok2015_34b"
    source := ⟨"blok-2015", "(34b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Er hoeven tot vijf studenten te komen."
    discourseSegments := []
    glossedTokens := [("Er", "there"), ("hoeven", "must.NPI"), ("tot", "TOT"), ("vijf", "five"), ("studenten", "students"), ("te", "to"), ("komen", "come")]
    translation := "Up to five students have to show up."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("directional", "+"), ("test", "npi"), ("numeral", "5")]
    comment := "The modal hoeven is a negative polarity item."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex_3a, ex_3b, ex_4a, ex_4b, ex_7a, ex_7b, ex_11a, ex_11b, ex_22a, ex_22b, ex_23a, ex_23b, ex_29, ex_34a, ex_34b]

end Blok2015.Examples
