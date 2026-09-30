module

public import Linglib.Data.Examples.Schema

/-!
# `Beaver2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Beaver2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beaver2001.Examples`.
-/

@[expose] public section

namespace Beaver2001.Examples

open Data.Examples

def e52 : LinguisticExample :=
  { id := "beaver2001_e52"
    source := ⟨"beaver-2001", "E52"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I go to London, my sister will pick me up at the airport."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "definite (my sister)"), ("embedding", "consequent of conditional")] }

def e154 : LinguisticExample :=
  { id := "beaver2001_e154"
    source := ⟨"beaver-2001", "E154"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Spaceman Spiff lands on Planet X, he will be bothered by the fact that his weight is greater than it would be on Earth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "the fact that + factive bothered by"), ("embedding", "consequent of conditional")] }

def e155 : LinguisticExample :=
  { id := "beaver2001_e155"
    source := ⟨"beaver-2001", "E155"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is unlikely that if Spaceman Spiff lands on Planet X, he will be bothered by the fact that his weight is greater than it would be on Earth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "the fact that + factive bothered by"), ("embedding", "conditional under unlikely")] }

def e156 : LinguisticExample :=
  { id := "beaver2001_e156"
    source := ⟨"beaver-2001", "E156"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Spaceman Spiff lands on Planet X and is bothered by the fact that his weight is greater than it would be on Earth, he won't stay long."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "the fact that + factive bothered by"), ("embedding", "second conjunct of conditional antecedent")] }

def e198 : LinguisticExample :=
  { id := "beaver2001_e198"
    source := ⟨"beaver-2001", "E198"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bertha is hiding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "presupposed content for E168'-E173")] }

def e168prime : LinguisticExample :=
  { id := "beaver2001_e168prime"
    source := ⟨"beaver-2001", "E168'"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anna realises that Bertha is hiding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "none")] }

def e169prime : LinguisticExample :=
  { id := "beaver2001_e169prime"
    source := ⟨"beaver-2001", "E169'"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anna does not realise that Bertha is hiding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "negation")] }

def e172prime : LinguisticExample :=
  { id := "beaver2001_e172prime"
    source := ⟨"beaver-2001", "E172'"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Anna realises that Bertha is hiding, then she will find her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "antecedent of conditional")] }

def e173 : LinguisticExample :=
  { id := "beaver2001_e173"
    source := ⟨"beaver-2001", "E173"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anna might realise that Bertha is hiding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "might")] }

def e175 : LinguisticExample :=
  { id := "beaver2001_e175"
    source := ⟨"beaver-2001", "E175"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bertha is not in the kitchen, then Anna realises that Bertha is in the attic."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "consequent of conditional")] }

def e206 : LinguisticExample :=
  { id := "beaver2001_e206"
    source := ⟨"beaver-2001", "E206"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible there is a happy farmer, but, then again, it is possible that there are no happy farmers."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "might phi and might not phi")] }

def e207 : LinguisticExample :=
  { id := "beaver2001_e207"
    source := ⟨"beaver-2001", "E207"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No farmer is happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "plain assertion")] }

def all : List LinguisticExample := [e52, e154, e155, e156, e198, e168prime, e169prime, e172prime, e173, e175, e206, e207]

end Beaver2001.Examples
