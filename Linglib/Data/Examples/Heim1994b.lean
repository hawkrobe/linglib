module

public import Linglib.Data.Examples.Schema

/-!
# `Heim1994b` — typed example data

Auto-generated from `Linglib/Data/Examples/Heim1994b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heim1994b.Examples`.
-/

@[expose] public section

namespace Heim1994b.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "heim1994b_ex1"
    source := ⟨"heim-1994", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which students called."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "0"), ("question", "which students called")] }

def ex6 : LinguisticExample :=
  { id := "heim1994b_ex6"
    source := ⟨"heim-1994", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows who called."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("question", "who called")] }

def ex17 : LinguisticExample :=
  { id := "heim1994b_ex17"
    source := ⟨"heim-1994", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows the answer to the question which students called."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")] }

def ex18 : LinguisticExample :=
  { id := "heim1994b_ex18"
    source := ⟨"heim-1994", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows that Bill and Sue called. That Bill and Sue called happens to be the answer to the question which students called. So John knows the answer to the question which students called."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")] }

def ex19 : LinguisticExample :=
  { id := "heim1994b_ex19"
    source := ⟨"heim-1994", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I didn't find your house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")] }

def ex20a : LinguisticExample :=
  { id := "heim1994b_ex20a"
    source := ⟨"heim-1994", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I identified the culprit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")] }

def ex20b : LinguisticExample :=
  { id := "heim1994b_ex20b"
    source := ⟨"heim-1994", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I identified the striped animal in your drawing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")] }

def ex21 : LinguisticExample :=
  { id := "heim1994b_ex21"
    source := ⟨"heim-1994", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which students are identical with themselves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7"), ("gs", "John knows what students there are"), ("generalizedKarttunen", "John knows whether there are students")] }

def ex24 : LinguisticExample :=
  { id := "heim1994b_ex24"
    source := ⟨"heim-1994", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which students live with their actual spouses."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7"), ("gs", "false when John believes Sue not to be a student"), ("generalizedKarttunen", "true")] }

def all : List LinguisticExample := [ex1, ex6, ex17, ex18, ex19, ex20a, ex20b, ex21, ex24]

end Heim1994b.Examples
