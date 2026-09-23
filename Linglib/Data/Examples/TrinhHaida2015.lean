module

public import Linglib.Data.Examples.Schema

/-!
# `TrinhHaida2015` — typed example data

Auto-generated from `Linglib/Data/Examples/TrinhHaida2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TrinhHaida2015.Examples`.
-/

@[expose] public section

namespace TrinhHaida2015.Examples

open Data.Examples

def ex_5 : LinguisticExample :=
  { id := "trinhhaida2015_5"
    source := ⟨"trinh-haida-2015", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill went for a run and didn't smoke. John (only) went for a run."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill went for a run and didn't smoke. John (only) went for a run."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: not [John went for a run and didn't smoke], so John smoked", .acceptable)]
    paperFeatures := [("case", "symmetry breaking"), ("prejacent", "run"), ("contextual alternative", "run and not smoke")]
    comment := "What is true of Bill is inferred not to be true of John."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "trinhhaida2015_6"
    source := ⟨"trinh-haida-2015", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill passed some of the tests and failed some. John (only) passed some of the tests."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill passed some of the tests and failed some. John (only) passed some of the tests."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: not [John passed some and failed some], so John passed all", .unacceptable)]
    paperFeatures := [("case", "symmetry preserving"), ("prejacent", "pass some"), ("contextual alternative", "pass some and fail some")]
    comment := "The sequence is odd precisely because it cannot mean that what is true of Bill is not true of John (footnote 4)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "trinhhaida2015_9"
    source := ⟨"trinh-haida-2015", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John (only) has three chairs."
    discourseSegments := []
    glossedTokens := []
    translation := "John (only) has three chairs."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John does not have four chairs", .acceptable)]
    paperFeatures := [("case", "symmetry problem"), ("symmetric alternatives", "four; exactly three")]
    comment := "The symmetry problem: *four* and *exactly three* are of the same type, so relevance keeps both or neither, yet the inference negates only *four*."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "trinhhaida2015_10"
    source := ⟨"trinh-haida-2015", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John (only) did some of the homework."
    discourseSegments := []
    glossedTokens := []
    translation := "John (only) did some of the homework."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John did not do all of the homework", .acceptable)]
    paperFeatures := [("case", "symmetry problem"), ("symmetric alternatives", "all; some but not all")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20b : LinguisticExample :=
  { id := "trinhhaida2015_20b"
    source := ⟨"trinh-haida-2015", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill works hard and doesn't watch TV. John (only) works hard."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill works hard and doesn't watch TV. John (only) works hard."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: not [John works hard and doesn't watch TV]", .acceptable)]
    paperFeatures := [("case", "symmetry breaking"), ("prejacent", "work hard"), ("contextual alternative", "work hard and not watch TV")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20c : LinguisticExample :=
  { id := "trinhhaida2015_20c"
    source := ⟨"trinh-haida-2015", "(20c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill is tall and not bald. John is (only) tall."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill is tall and not bald. John is (only) tall."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: not [John is tall and not bald]", .acceptable)]
    paperFeatures := [("case", "symmetry breaking"), ("prejacent", "tall"), ("contextual alternative", "tall and not bald")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21a : LinguisticExample :=
  { id := "trinhhaida2015_21a"
    source := ⟨"trinh-haida-2015", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill ate exactly three cookies. John (only) ate three cookies."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill ate exactly three cookies. John (only) ate three cookies."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: not [John ate exactly three cookies]", .unacceptable)]
    paperFeatures := [("case", "symmetry preserving"), ("prejacent", "three"), ("contextual alternative", "exactly three"), ("lexical alternative", "four")]
    comment := "Atomicity is vacuous: *four* is derived by lexical replacement and, being *three* without *exactly three*, lies in the Boolean closure of {three, exactly three}."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21b : LinguisticExample :=
  { id := "trinhhaida2015_21b"
    source := ⟨"trinh-haida-2015", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill fathered children and no twins. John (only) fathered children."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill fathered children and no twins. John (only) fathered children."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: not [John fathered children and no twins]", .unacceptable)]
    paperFeatures := [("case", "symmetry preserving"), ("prejacent", "children"), ("contextual alternative", "children and no twins"), ("lexical alternative", "twins")]
    comment := "*Twins* is *children* without *children and no twins*, so it is in the Boolean closure of the restricted domain."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21c : LinguisticExample :=
  { id := "trinhhaida2015_21c"
    source := ⟨"trinh-haida-2015", "(21c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill passed some of the fitness tests and failed some. John (only) passed some of the fitness tests."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill passed some of the fitness tests and failed some. John (only) passed some of the fitness tests."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: not [John passed some of the fitness tests and failed some]", .unacceptable)]
    paperFeatures := [("case", "symmetry preserving"), ("prejacent", "pass some"), ("contextual alternative", "pass some and fail some"), ("lexical alternative", "pass all")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_50 : LinguisticExample :=
  { id := "trinhhaida2015_50"
    source := ⟨"trinh-haida-2015", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Detective A concluded that the robbers stole the book and not the jewelry. Detective B (only) concluded that they stole the book."
    discourseSegments := []
    glossedTokens := []
    translation := "Detective A concluded that the robbers stole the book and not the jewelry. Detective B (only) concluded that they stole the book."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: Detective B did not conclude that they stole the book and not the jewelry", .acceptable), ("inference: Detective B did not conclude that they stole the book and the jewelry", .acceptable)]
    paperFeatures := [("case", "apparent problem"), ("prejacent", "concluded book")]
    comment := "Under Atomicity the alternative *book and the jewelry* is underivable; the second inference comes from the derivable *concluded that they stole the jewelry*, since attitude verbs distribute over conjunction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_54 : LinguisticExample :=
  { id := "trinhhaida2015_54"
    source := ⟨"trinh-haida-2015", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The committee didn't pass all of my students."
    discourseSegments := []
    glossedTokens := []
    translation := "The committee didn't pass all of my students."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: the committee passed some of my students", .acceptable)]
    paperFeatures := [("case", "indirect implicature"), ("prejacent", "not all")]
    comment := "Atomicity rules out the symmetric *passed some*: the VP substituted for NegP is atomic, so *all* inside it cannot then be replaced."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_56 : LinguisticExample :=
  { id := "trinhhaida2015_56"
    source := ⟨"trinh-haida-2015", "(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of my students did all of the readings."
    discourseSegments := []
    glossedTokens := []
    translation := "Some of my students did all of the readings."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: not [all of my students did some of the readings]", .unacceptable)]
    paperFeatures := [("case", "switching problem"), ("prejacent", "some all")]
    comment := "The switching problem: *some* and *all* switch places only under negation, (58); the constraints (60b) and (60c) on the order and monotonicity of replacements block the derivation here."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_58 : LinguisticExample :=
  { id := "trinhhaida2015_58"
    source := ⟨"trinh-haida-2015", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of my students did all of the readings."
    discourseSegments := []
    glossedTokens := []
    translation := "None of my students did all of the readings."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: all of my students did some of the readings", .acceptable)]
    paperFeatures := [("case", "switching problem"), ("prejacent", "not some all")]
    comment := "A weak inference; under negation the bottom-up, non-weakening replacements of (60) derive the alternative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_5, ex_6, ex_9, ex_10, ex_20b, ex_20c, ex_21a, ex_21b, ex_21c, ex_50, ex_54, ex_56, ex_58]

end TrinhHaida2015.Examples
