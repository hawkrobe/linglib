module

public import Linglib.Data.Examples.Schema

/-!
# `Karttunen1974` — typed example data

Auto-generated from `Linglib/Data/Examples/Karttunen1974.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Karttunen1974.Examples`.
-/

@[expose] public section

namespace Karttunen1974.Examples

open Data.Examples

def until_state : Datum :=
  { id := "karttunen1974_until_state"
    source := ⟨"karttunen-1974", "UNVERIFIED"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John slept until 3pm."
    glossedTokens := []
    context := "Durative *until* with a stative main clause: the canonical use. The state is homogeneous (subinterval property), satisfying the durative selectional restriction."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("clause", "main"), ("vendler_class", "state")] }

def until_activity : Datum :=
  { id := "karttunen1974_until_activity"
    source := ⟨"karttunen-1974", "UNVERIFIED"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John ran until 3pm."
    glossedTokens := []
    context := "Durative *until* with an activity main clause: activities are homogeneous, satisfying the durative selectional restriction."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("clause", "main"), ("vendler_class", "activity")] }

def until_achievement : Datum :=
  { id := "karttunen1974_until_achievement"
    source := ⟨"karttunen-1974", "UNVERIFIED"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John arrived until 3pm."
    glossedTokens := []
    context := "Durative *until* with an achievement main clause: the achievement is punctual, violating the durative selectional restriction. Coercion to an iterative (activity) reading is possible but marked."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("clause", "main"), ("vendler_class", "achievement"), ("coercion", "iterative"), ("result_class", "activity")] }

def until_accomplishment : Datum :=
  { id := "karttunen1974_until_accomplishment"
    source := ⟨"karttunen-1974", "UNVERIFIED"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John built the house until 3pm."
    glossedTokens := []
    context := "Durative *until* with an accomplishment main clause: the accomplishment's natural endpoint conflicts with *until*'s external boundary. Coercion to an atelic (activity) reading is possible but marked."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("clause", "main"), ("vendler_class", "accomplishment"), ("coercion", "atelicize"), ("result_class", "activity")] }

def all : List Datum := [until_state, until_activity, until_achievement, until_accomplishment]

end Karttunen1974.Examples
