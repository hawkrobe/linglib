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
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("presuppositions", "conflicting")] }

def ex_2 : LinguisticExample :=
  { id := "yagi2025_2"
    source := ⟨"yagi-2025", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suzan either met the king or the president of Bessarabia."
    glossedTokens := []
    context := "Bessarabia has a head of state, who is either a king or a president."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("presuppositions", "conflicting")] }

def ex_3 : LinguisticExample :=
  { id := "yagi2025_3"
    source := ⟨"yagi-2025", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either the King of Buganda is now opening parliament or the President of Buganda is conducting the ceremony."
    glossedTokens := []
    context := "The state has either a king or a president."
    judgment := .acceptable
    alternatives := []
    readings := [("presupposes a king or a president", .acceptable), ("false if the head of state is not opening parliament", .acceptable)]
    paperFeatures := [("presuppositions", "conflicting")] }

def ex_4 : LinguisticExample :=
  { id := "yagi2025_4"
    source := ⟨"yagi-2025", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not the case that the liquid in this tank has either stopped fermenting or it has not yet begun to ferment."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("true if the liquid is fermenting", .acceptable)]
    paperFeatures := [("negation", "of conflicting disjunction")] }

def ex_5 : LinguisticExample :=
  { id := "yagi2025_5"
    source := ⟨"yagi-2025", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Neither is the King of Buganda now opening parliament nor is the President of Buganda conducting the ceremony."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("true if the head of the nation is not opening parliament", .acceptable)]
    paperFeatures := [("negation", "of conflicting disjunction")] }

def ex_6 : LinguisticExample :=
  { id := "yagi2025_6"
    source := ⟨"yagi-2025", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either baldness is not hereditary, or all of Bill's children are bald."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("presupposes that Bill has children", .acceptable)]
    paperFeatures := [("presupposition", "projects")] }

def ex_7 : LinguisticExample :=
  { id := "yagi2025_7"
    source := ⟨"yagi-2025", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Bill has no child or all of Bill's children are bald."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("accommodation", "non-tautological")] }

def ex_8 : LinguisticExample :=
  { id := "yagi2025_8"
    source := ⟨"yagi-2025", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either John didn't solve the problem or Mary realized that the problem is solved."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the factive presupposition need not project", .acceptable)]
    paperFeatures := [("presupposition", "filtered")] }

def ex_9 : LinguisticExample :=
  { id := "yagi2025_9"
    source := ⟨"yagi-2025", "(ia)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be here or (else) it must be there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("one of the following obtains: it must be here; it must be there", .acceptable)]
    paperFeatures := [("reading", "modal split")] }

def ex_10 : LinguisticExample :=
  { id := "yagi2025_10"
    source := ⟨"yagi-2025", "(iiib)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The doctor can tell you right away what's the matter with you, or the nurse can make an appointment for you."
    glossedTokens := []
    context := "The phone will be answered by either a doctor or a secretary."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "modal split")] }

def ex_11 : LinguisticExample :=
  { id := "yagi2025_11"
    source := ⟨"yagi-2025", "(ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either John is not a scuba diver, or his wetsuit is blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("presupposes that if John is a scuba diver he has a wetsuit", .acceptable)]
    paperFeatures := [("presupposition", "conditional")] }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11]

end Yagi2025.Examples
