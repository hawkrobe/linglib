module

public import Linglib.Data.Examples.Schema

/-!
# `Pancheva2003` — typed example data

Auto-generated from `Linglib/Data/Examples/Pancheva2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Pancheva2003.Examples`.
-/

@[expose] public section

namespace Pancheva2003.Examples

open Data.Examples

def ex1a_U : Datum :=
  { id := "pancheva2003_ex1a_U"
    source := ⟨"pancheva-2003", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since 2000, Alexandra has lived in LA."
    glossedTokens := []
    context := "Universal (U) perfect. Asserts that the underlying eventuality (live in LA) holds throughout an interval delimited by 2000 (LB) and the utterance time (RB). Requires adverbial modification (here: `since 2000`)."
    judgment := .acceptable
    alternatives := []
    readings := [("universal (live-in-LA holds throughout 2000-now)", .acceptable)]
    paperFeatures := [] }

def ex1b_EXP : Datum :=
  { id := "pancheva2003_ex1b_EXP"
    source := ⟨"pancheva-2003", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alexandra has been in LA (before)."
    glossedTokens := []
    context := "Experiential (EXP) perfect. Asserts that the underlying eventuality holds at a proper subset of an interval extending back from the utterance time. No claim about the eventuality holding now."
    judgment := .acceptable
    alternatives := []
    readings := [("experiential (LA-being at some past subinterval)", .acceptable)]
    paperFeatures := [] }

def ex1c_RES : Datum :=
  { id := "pancheva2003_ex1c_RES"
    source := ⟨"pancheva-2003", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alexandra has (just) arrived in LA."
    glossedTokens := []
    context := "Resultative (RES) perfect. Same temporal assertion as Experiential, with the added meaning that the result state (be in LA) holds at the utterance time."
    judgment := .acceptable
    alternatives := []
    readings := [("resultative (arrived + still in LA at utterance)", .acceptable)]
    paperFeatures := [] }

def ex5a_atelic : Datum :=
  { id := "pancheva2003_ex5a_atelic"
    source := ⟨"pancheva-2003", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have run."
    glossedTokens := []
    context := "Atelic activity participle (`run`). Cannot yield a Resultative reading because activities have no inherent result state (Kratzer 1994). Only the Experiential reading is available."
    judgment := .acceptable
    alternatives := []
    readings := [("experiential (running at some past time)", .acceptable), ("resultative", .ungrammatical)]
    paperFeatures := [] }

def ex6a_telic : Datum :=
  { id := "pancheva2003_ex6a_telic"
    source := ⟨"pancheva-2003", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have lost my glasses."
    glossedTokens := []
    context := "Telic achievement participle (`lose my glasses`). Has both Experiential and Resultative readings. On the Resultative reading, the glasses must still be lost at the utterance time; on the Experiential reading, no such requirement."
    judgment := .acceptable
    alternatives := []
    readings := [("experiential (lost at some past time)", .acceptable), ("resultative (lost + still missing now)", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex1a_U, ex1b_EXP, ex1c_RES, ex5a_atelic, ex6a_telic]

end Pancheva2003.Examples
