module

public import Linglib.Data.Examples.Schema

/-!
# `AugurzkyEtAl2023` — typed example data

Auto-generated from `Linglib/Data/Examples/AugurzkyEtAl2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AugurzkyEtAl2023.Examples`.
-/

@[expose] public section

namespace AugurzkyEtAl2023.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "augurzkyetal2023_1"
    source := ⟨"augurzky-etal-2023", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Frank opened his presents."
    discourseSegments := []
    glossedTokens := [("Frank", "Frank"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_3 : LinguisticExample :=
  { id := "augurzkyetal2023_3"
    source := ⟨"augurzky-etal-2023", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Frank didn't open his presents."
    discourseSegments := []
    glossedTokens := [("Frank", "Frank"), ("didn't", "do.PST.NEG"), ("open", "open"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_14 : LinguisticExample :=
  { id := "augurzkyetal2023_14"
    source := ⟨"augurzky-etal-2023", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy opened his presents."
    discourseSegments := []
    glossedTokens := [("Every", "every"), ("boy", "boy"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_15 : LinguisticExample :=
  { id := "augurzkyetal2023_15"
    source := ⟨"augurzky-etal-2023", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy opened his presents."
    discourseSegments := []
    glossedTokens := [("No", "no"), ("boy", "boy"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def notEvery : LinguisticExample :=
  { id := "augurzkyetal2023_notEvery"
    source := ⟨"augurzky-etal-2023", "Experiment 2, not every"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every boy opened his presents."
    discourseSegments := []
    glossedTokens := [("Not", "not"), ("every", "every"), ("boy", "boy"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_20 : LinguisticExample :=
  { id := "augurzkyetal2023_20"
    source := ⟨"augurzky-etal-2023", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly two boys opened their presents."
    discourseSegments := []
    glossedTokens := [("Exactly", "exactly"), ("two", "two"), ("boys", "boy.PL"), ("opened", "open.PST"), ("their", "3PL.POSS"), ("presents", "present.PL")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def all : List LinguisticExample := [ex_1, ex_3, ex_14, ex_15, notEvery, ex_20]

end AugurzkyEtAl2023.Examples
