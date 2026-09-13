import Linglib.Data.Examples.Schema

/-!
# `Rooth1992` — typed example data

Auto-generated from `Linglib/Data/Examples/Rooth1992.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rooth1992.Examples`.
-/

namespace Rooth1992.Examples

open Data.Examples

def ex_3a : LinguisticExample :=
  { id := "rooth1992_3a"
    source := ⟨"rooth-1992", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary only introduced [Bill]F to Sue."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Mary introduced Bill and Tom to Sue, and there were no other introductions."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "only"), ("focus", "Bill"), ("truth", "false")]
    comment := "False in the introduction scenario: the domain of only is constrained to properties of the form 'introducing y to Sue', and Mary also introduced Tom to Sue."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3b : LinguisticExample :=
  { id := "rooth1992_3b"
    source := ⟨"rooth-1992", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary only introduced Bill to [Sue]F."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Mary introduced Bill and Tom to Sue, and there were no other introductions."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "only"), ("focus", "Sue"), ("truth", "true")]
    comment := "True in the introduction scenario: among properties of the form 'introducing Bill to z', Mary has only 'introducing Bill to Sue'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "rooth1992_7"
    source := ⟨"rooth-1992", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary only [read]F The Recognitions."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "only"), ("focus", "read")]
    comment := "With a focused transitive verb the focus semantic value of the VP contains every property of the form 'R-ing The Recognitions', trivial relations included; fixing the domain of only to it gives unsatisfiable truth conditions, though the sentence can be true."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "rooth1992_11"
    source := ⟨"rooth-1992", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An [American]F farmer was talking to a [Canadian]F farmer ..."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "contrast")]
    comment := "Symmetric contrast: each N' is construed as contrasting with the other, the ordinary value of each being a member of the focus semantic value of the other."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16 : LinguisticExample :=
  { id := "rooth1992_16"
    source := ⟨"rooth-1992", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Well, I [passed]F."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The speaker and roommates Steve and Paul took a quiz; George asks how it went."
    judgment := .acceptable
    alternatives := []
    readings := [("the speaker did not ace the quiz", .acceptable)]
    paperFeatures := [("construction", "scale"), ("focus", "passed")]
    comment := "Suggests that the speaker did no better than passing, and nothing about whether the roommates passed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17 : LinguisticExample :=
  { id := "rooth1992_17"
    source := ⟨"rooth-1992", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Well, [I]F passed."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The speaker and roommates Steve and Paul took a quiz; George asks how it went."
    judgment := .acceptable
    alternatives := []
    readings := [("the roommates did not pass", .acceptable)]
    paperFeatures := [("construction", "scale"), ("focus", "I")]
    comment := "Suggests that the roommates did not pass, via a scale of group propositions of the form 'x passed'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23Aa_Qa : LinguisticExample :=
  { id := "rooth1992_23Aa_Qa"
    source := ⟨"rooth-1992", "(23Aa) answering (23Qa)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[Mary]F cut Bill down to size."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Who cut Bill down to size?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qa"), ("question", "whoCutBill"), ("focus", "Mary")]
    comment := "An appropriate answer: the question denotation is a subset of the answer's focus semantic value."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23Ab_Qa : LinguisticExample :=
  { id := "rooth1992_23Ab_Qa"
    source := ⟨"rooth-1992", "(23Ab) answering (23Qa)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary cut [Bill]F down to size."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Who cut Bill down to size?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qa"), ("question", "whoCutBill"), ("focus", "Bill")]
    comment := "Inappropriate: the propositions of the form 'x cut Bill down to size' are not all of the form 'Mary cut y down to size'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23Ab_Qb : LinguisticExample :=
  { id := "rooth1992_23Ab_Qb"
    source := ⟨"rooth-1992", "(23Ab) answering (23Qb)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary cut [Bill]F down to size."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Who did Mary cut down to size?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qa"), ("question", "whoDidMaryCut"), ("focus", "Bill")]
    comment := "An appropriate answer to the object question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23Aa_Qb : LinguisticExample :=
  { id := "rooth1992_23Aa_Qb"
    source := ⟨"rooth-1992", "(23Aa) answering (23Qb)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[Mary]F cut Bill down to size."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Who did Mary cut down to size?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qa"), ("question", "whoDidMaryCut"), ("focus", "Mary")]
    comment := "Inappropriate as an answer to the object question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_59a : LinguisticExample :=
  { id := "rooth1992_59a"
    source := ⟨"rooth-1992", "(59a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "she beats [me]F more often than Sue"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("than she beats Sue", .acceptable), ("than Sue beats me", .unacceptable)]
    paperFeatures := [("construction", "ellipsis"), ("focus", "me")]
    comment := "Bare remnant ellipsis: focus on the object correlate selects the reading in which the remnant corresponds to the object."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_59b : LinguisticExample :=
  { id := "rooth1992_59b"
    source := ⟨"rooth-1992", "(59b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[she]F beats me more often than Sue"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("than she beats Sue", .unacceptable), ("than Sue beats me", .acceptable)]
    paperFeatures := [("construction", "ellipsis"), ("focus", "she")]
    comment := "Focus on the subject correlate selects the reading in which the remnant corresponds to the subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_70 : LinguisticExample :=
  { id := "rooth1992_70"
    source := ⟨"rooth-1992", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People who [grow]F rice generally only [eat]F rice."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "only"), ("focus", "eat")]
    comment := "The focus on the verb is anaphoric to the other verb phrase rather than associated with only, whose domain is then fixed pragmatically: what is excluded is eating staples other than rice."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_72a : LinguisticExample :=
  { id := "rooth1992_72a"
    source := ⟨"rooth-1992", "(72a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An American farmer was talking to a [Canadian]F farmer ..."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "contrast")]
    comment := "The anticipatory first focus of (11) is optional: no focus interpretation operator at the level of the first N'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_3a, ex_3b, ex_7, ex_11, ex_16, ex_17, ex_23Aa_Qa, ex_23Ab_Qa, ex_23Ab_Qb, ex_23Aa_Qb, ex_59a, ex_59b, ex_70, ex_72a]

end Rooth1992.Examples
