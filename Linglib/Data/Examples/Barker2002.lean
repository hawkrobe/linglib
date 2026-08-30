import Linglib.Data.Examples.Schema

/-!
# `Barker2002` — typed example data

Auto-generated from `Linglib/Data/Examples/Barker2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Barker2002.Examples`.
-/

namespace Barker2002.Examples

open Data.Examples

def ex_4a : LinguisticExample :=
  { id := "barker2002_4a"
    source := ⟨"barker-2002", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left."
    discourseSegments := []
    glossedTokens := []
    translation := "John left."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("translation", "left j")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4b : LinguisticExample :=
  { id := "barker2002_4b"
    source := ⟨"barker-2002", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw Mary."
    discourseSegments := []
    glossedTokens := []
    translation := "John saw Mary."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("translation", "saw m j")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "barker2002_14"
    source := ⟨"barker-2002", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw everyone."
    discourseSegments := []
    glossedTokens := []
    translation := "John saw everyone."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("translation", "∀x.saw x j"), ("quantifiers", "everyone")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17a : LinguisticExample :=
  { id := "barker2002_17a"
    source := ⟨"barker-2002", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw every man."
    discourseSegments := []
    glossedTokens := []
    translation := "John saw every man."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("translation", "∀x.man x → saw x j"), ("quantifiers", "every")]
    comment := "Printed 'every men'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17b : LinguisticExample :=
  { id := "barker2002_17b"
    source := ⟨"barker-2002", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw most men."
    discourseSegments := []
    glossedTokens := []
    translation := "John saw most men."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("translation", "most(man)(λx.saw x j)"), ("quantifiers", "most")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17c : LinguisticExample :=
  { id := "barker2002_17c"
    source := ⟨"barker-2002", "(17c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man saw a woman."
    discourseSegments := []
    glossedTokens := []
    translation := "Every man saw a woman."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("a > every", .acceptable), ("every > a", .acceptable)]
    paperFeatures := [("quantifiers", "every a")]
    comment := "(17c) prints the inverse scoping; the surface scoping arrives with subject priority."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19a : LinguisticExample :=
  { id := "barker2002_19a"
    source := ⟨"barker-2002", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A raindrop fell on every car."
    discourseSegments := []
    glossedTokens := []
    translation := "A raindrop fell on every car."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifiers", "a every"), ("natural_reading", "every > a")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19b : LinguisticExample :=
  { id := "barker2002_19b"
    source := ⟨"barker-2002", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A raindrop fell on the hood of every car."
    discourseSegments := []
    glossedTokens := []
    translation := "A raindrop fell on the hood of every car."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifiers", "a every"), ("natural_reading", "every > a")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19c : LinguisticExample :=
  { id := "barker2002_19c"
    source := ⟨"barker-2002", "(19c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A raindrop fell on the top of the hood of every car."
    discourseSegments := []
    glossedTokens := []
    translation := "A raindrop fell on the top of the hood of every car."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifiers", "a every"), ("natural_reading", "every > a")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21a : LinguisticExample :=
  { id := "barker2002_21a"
    source := ⟨"barker-2002", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A man thought everyone saw Mary."
    discourseSegments := []
    glossedTokens := []
    translation := "A man thought everyone saw Mary."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifiers", "a everyone"), ("translation", "∃y.man y ∧ thought(∀x.saw m x) y"), ("island", "tensed S")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22a : LinguisticExample :=
  { id := "barker2002_22a"
    source := ⟨"barker-2002", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No man from a foreign country was admitted."
    discourseSegments := []
    glossedTokens := []
    translation := "No man from a foreign country was admitted."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("no > a", .acceptable), ("a > no", .acceptable)]
    paperFeatures := [("quantifiers", "no a")]
    comment := "(22b) linear, (22c) inverse linking."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23a : LinguisticExample :=
  { id := "barker2002_23a"
    source := ⟨"barker-2002", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two politicians spy on someone from every city."
    discourseSegments := []
    glossedTokens := []
    translation := "Two politicians spy on someone from every city."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("every > two > someone", .unacceptable)]
    paperFeatures := [("quantifiers", "two someone every"), ("constituent", "someone every")]
    comment := "May's observation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_26a : LinguisticExample :=
  { id := "barker2002_26a"
    source := ⟨"barker-2002", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most subjects put an object in every box."
    discourseSegments := []
    glossedTokens := []
    translation := "Most subjects put an object in every box."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("every > most > an", .unacceptable)]
    paperFeatures := [("quantifiers", "most an every"), ("constituent", "an every")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_27a : LinguisticExample :=
  { id := "barker2002_27a"
    source := ⟨"barker-2002", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left and John slept."
    discourseSegments := []
    glossedTokens := []
    translation := "John left and John slept."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "S"), ("translation", "and(left j)(slept j)")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_27b : LinguisticExample :=
  { id := "barker2002_27b"
    source := ⟨"barker-2002", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left and slept."
    discourseSegments := []
    glossedTokens := []
    translation := "John left and slept."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "VP"), ("translation", "and(left j)(slept j)")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_27c : LinguisticExample :=
  { id := "barker2002_27c"
    source := ⟨"barker-2002", "(27c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw and liked Mary."
    discourseSegments := []
    glossedTokens := []
    translation := "John saw and liked Mary."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "Vt"), ("translation", "and(saw m j)(liked m j)")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_27d : LinguisticExample :=
  { id := "barker2002_27d"
    source := ⟨"barker-2002", "(27d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary left."
    discourseSegments := []
    glossedTokens := []
    translation := "John and Mary left."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "NP"), ("translation", "and(left j)(left m)")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_42a : LinguisticExample :=
  { id := "barker2002_42a"
    source := ⟨"barker-2002", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone saw the friend of the friend of everyone."
    discourseSegments := []
    glossedTokens := []
    translation := "Someone saw the friend of the friend of everyone."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("someone > everyone", .acceptable), ("everyone > someone", .acceptable)]
    paperFeatures := [("quantifiers", "someone everyone")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_43 : LinguisticExample :=
  { id := "barker2002_43"
    source := ⟨"barker-2002", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone saw a friend of everyone."
    discourseSegments := []
    glossedTokens := []
    translation := "Someone saw a friend of everyone."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("someone > a > everyone", .acceptable), ("someone > everyone > a", .acceptable), ("a > everyone > someone", .acceptable), ("everyone > a > someone", .acceptable), ("everyone > someone > a", .unacceptable), ("a > someone > everyone", .unacceptable)]
    paperFeatures := [("quantifiers", "someone a everyone"), ("constituent", "a everyone"), ("derivation", "someone saw a friend of everyone")]
    comment := "Four of the six orders; the two splitting the object's quantifiers are excluded by Integrity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_4a, ex_4b, ex_14, ex_17a, ex_17b, ex_17c, ex_19a, ex_19b, ex_19c, ex_21a, ex_22a, ex_23a, ex_26a, ex_27a, ex_27b, ex_27c, ex_27d, ex_42a, ex_43]

end Barker2002.Examples
