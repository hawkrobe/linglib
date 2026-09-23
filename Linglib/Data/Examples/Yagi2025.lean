module

public import Linglib.Data.Examples.Schema

/-!
# `Yagi2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Yagi2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Yagi2025.Examples`.
-/

@[expose] public section

namespace Yagi2025.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "yagi2025_1"
    source := ⟨"yagi-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The liquid in this tank has either stopped fermenting or it has not yet begun to ferment."
    discourseSegments := []
    glossedTokens := []
    translation := "The liquid in this tank has either stopped fermenting or it has not yet begun to ferment."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("presuppositions", "conflicting")]
    comment := "Hausser 1976. The disjunctive presupposition is a tautology; false if the liquid is fermenting."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "yagi2025_2"
    source := ⟨"yagi-2025", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suzan either met the king or the president of Bessarabia."
    discourseSegments := []
    glossedTokens := []
    translation := "Suzan either met the king or the president of Bessarabia."
    context := "Bessarabia has a head of state, who is either a king or a president."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("presuppositions", "conflicting")]
    comment := "Landman 1986. False if Suzan did not meet the head of the nation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "yagi2025_3"
    source := ⟨"yagi-2025", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either the King of Buganda is now opening parliament or the President of Buganda is conducting the ceremony."
    discourseSegments := []
    glossedTokens := []
    translation := "Either the King of Buganda is now opening parliament or the President of Buganda is conducting the ceremony."
    context := "The state has either a king or a president."
    judgment := .acceptable
    alternatives := []
    readings := [("presupposes a king or a president", .acceptable), ("false if the head of state is not opening parliament", .acceptable)]
    paperFeatures := [("presuppositions", "conflicting")]
    comment := "Beaver 2001."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "yagi2025_4"
    source := ⟨"yagi-2025", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not the case that the liquid in this tank has either stopped fermenting or it has not yet begun to ferment."
    discourseSegments := []
    glossedTokens := []
    translation := "It is not the case that the liquid in this tank has either stopped fermenting or it has not yet begun to ferment."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("true if the liquid is fermenting", .acceptable)]
    paperFeatures := [("negation", "of conflicting disjunction")]
    comment := "Hausser 1976."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "yagi2025_5"
    source := ⟨"yagi-2025", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Neither is the King of Buganda now opening parliament nor is the President of Buganda conducting the ceremony."
    discourseSegments := []
    glossedTokens := []
    translation := "Neither is the King of Buganda now opening parliament nor is the President of Buganda conducting the ceremony."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("true if the head of the nation is not opening parliament", .acceptable)]
    paperFeatures := [("negation", "of conflicting disjunction")]
    comment := "Beaver 2001."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "yagi2025_6"
    source := ⟨"yagi-2025", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either baldness is not hereditary, or all of Bill's children are bald."
    discourseSegments := []
    glossedTokens := []
    translation := "Either baldness is not hereditary, or all of Bill's children are bald."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("presupposes that Bill has children", .acceptable)]
    paperFeatures := [("presupposition", "projects")]
    comment := "Karttunen 1974. The disjunction-of-presuppositions modification predicts a tautologous presupposition here."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "yagi2025_7"
    source := ⟨"yagi-2025", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Bill has no child or all of Bill's children are bald."
    discourseSegments := []
    glossedTokens := []
    translation := "Either Bill has no child or all of Bill's children are bald."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("accommodation", "non-tautological")]
    comment := "The first assertion contradicts the second presupposition, so the default accommodation violates genuineness."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "yagi2025_8"
    source := ⟨"yagi-2025", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either John didn't solve the problem or Mary realized that the problem is solved."
    discourseSegments := []
    glossedTokens := []
    translation := "Either John didn't solve the problem or Mary realized that the problem is solved."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the factive presupposition need not project", .acceptable)]
    paperFeatures := [("presupposition", "filtered")]
    comment := "Beaver 2001. The standard update predicts the lack of projection; the default accommodation does not."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "yagi2025_9"
    source := ⟨"yagi-2025", "(ia)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be here or (else) it must be there."
    discourseSegments := []
    glossedTokens := []
    translation := "It must be here or (else) it must be there."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("one of the following obtains: it must be here; it must be there", .acceptable)]
    paperFeatures := [("reading", "modal split")]
    comment := "Geurts 2005."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "yagi2025_10"
    source := ⟨"yagi-2025", "(iiib)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The doctor can tell you right away what's the matter with you, or the nurse can make an appointment for you."
    discourseSegments := []
    glossedTokens := []
    translation := "The doctor can tell you right away what's the matter with you, or the nurse can make an appointment for you."
    context := "The phone will be answered by either a doctor or a secretary."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "modal split")]
    comment := "Landman 1986. Each disjunct is interpreted against one disjunct of the preceding sentence."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "yagi2025_11"
    source := ⟨"yagi-2025", "(ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either John is not a scuba diver, or his wetsuit is blue."
    discourseSegments := []
    glossedTokens := []
    translation := "Either John is not a scuba diver, or his wetsuit is blue."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("presupposes that if John is a scuba diver he has a wetsuit", .acceptable)]
    paperFeatures := [("presupposition", "conditional")]
    comment := "Katzir and Singh 2012."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11]

end Yagi2025.Examples
