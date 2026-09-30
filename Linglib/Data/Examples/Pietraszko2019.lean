module

public import Linglib.Data.Examples.Schema

/-!
# `Pietraszko2019` — typed example data

Auto-generated from `Linglib/Data/Examples/Pietraszko2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Pietraszko2019.Examples`.
-/

@[expose] public section

namespace Pietraszko2019.Examples

open Data.Examples

def ex_4 : LinguisticExample :=
  { id := "pietraszko2019_4"
    source := ⟨"pietraszko-2019", "(4)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Ngicabanga ukuthi usukile."
    glossedTokens := [("Ngicabanga", "1SG.thought"), ("ukuthi", "AUG.COMP"), ("usukile", "1.left")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cabanga"), ("role", "complement"), ("mood", "indicative")] }

def ex_7a : LinguisticExample :=
  { id := "pietraszko2019_7a"
    source := ⟨"pietraszko-2019", "(7a)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Ngi-ya-ku-funa ukudla."
    glossedTokens := [("Ngi-ya-ku-funa", "1SG.SBJ-DSJ-15.OBJ-want"), ("ukudla", "15.food")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ngi-ku-funa ukudla.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "funa"), ("role", "complement"), ("diagnostic", "objectMarking")] }

def ex_7b : LinguisticExample :=
  { id := "pietraszko2019_7b"
    source := ⟨"pietraszko-2019", "(7b)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Ngi-ya-ku-funa ukuthi uZodwa a-pheke."
    glossedTokens := [("Ngi-ya-ku-funa", "1SG.SBJ-DSJ-15.OBJ-want"), ("ukuthi", "15.COMP"), ("uZodwa", "1.Zodwa"), ("a-pheke", "1.SBJ-cook")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ngi-ku-funa ukuthi uZodwa a-pheke.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "funa"), ("role", "complement"), ("mood", "subjunctive"), ("diagnostic", "objectMarking")] }

def ex_14 : LinguisticExample :=
  { id := "pietraszko2019_14"
    source := ⟨"pietraszko-2019", "(14)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Ngi-dan-is-w-e yi-kuthi u-sukile."
    glossedTokens := [("Ngi-dan-is-w-e", "1SG.SBJ-worry-CAUS-PASS-PST"), ("yi-kuthi", "OBL-15.COMP"), ("u-sukile", "2SG.SBJ-left")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "danisa"), ("role", "obliquePassiveSubject")] }

def ex_20b : LinguisticExample :=
  { id := "pietraszko2019_20b"
    source := ⟨"pietraszko-2019", "(20b)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Si-khuluma nga u-kuthi abantu babambane."
    glossedTokens := [("Si-khuluma", "1PL.SBJ-talk"), ("nga", "about"), ("u-kuthi", "AUG-15.COMP"), ("abantu", "people"), ("babambane", "be.united")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "khuluma nga"), ("role", "prepositionObject")] }

def ex_22 : LinguisticExample :=
  { id := "pietraszko2019_22"
    source := ⟨"pietraszko-2019", "(22)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Ukuthi izitha zi-za-buya ku-bal-iw-e e-roof-ini."
    glossedTokens := [("Ukuthi", "15.COMP"), ("izitha", "10.enemies"), ("zi-za-buya", "10.SBJ-FUT-come"), ("ku-bal-iw-e", "15.SBJ-write-PASS-PST"), ("e-roof-ini", "LOC-roof-LOC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "bala"), ("role", "subject")] }

def all : List LinguisticExample := [ex_4, ex_7a, ex_7b, ex_14, ex_20b, ex_22]

end Pietraszko2019.Examples
