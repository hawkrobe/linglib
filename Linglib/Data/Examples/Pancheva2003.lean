import Linglib.Data.Examples.Schema

/-!
# `Pancheva2003` — typed example data

Auto-generated from `Linglib/Data/Examples/Pancheva2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Pancheva2003.Examples`.
-/

namespace Pancheva2003.Examples

open Data.Examples

def ex1a_U : LinguisticExample :=
  { id := "pancheva2003_ex1a_U"
    source := ⟨"pancheva-2003", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since 2000, Alexandra has lived in LA."
    discourseSegments := []
    glossedTokens := []
    translation := "Since 2000, Alexandra has lived in LA."
    context := "Universal (U) perfect. Asserts that the underlying eventuality (live in LA) holds throughout an interval delimited by 2000 (LB) and the utterance time (RB). Requires adverbial modification (here: `since 2000`)."
    judgment := .acceptable
    alternatives := []
    readings := [("universal (live-in-LA holds throughout 2000-now)", .acceptable)]
    paperFeatures := []
    comment := "Pancheva 2003 §1 ex (1a). One of the three canonical perfect-reading exemplars. Universal reading requires stative or progressive participial aspect (Pancheva §2 thesis)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex1b_EXP : LinguisticExample :=
  { id := "pancheva2003_ex1b_EXP"
    source := ⟨"pancheva-2003", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alexandra has been in LA (before)."
    discourseSegments := []
    glossedTokens := []
    translation := "Alexandra has been in LA (before)."
    context := "Experiential (EXP) perfect. Asserts that the underlying eventuality holds at a proper subset of an interval extending back from the utterance time. No claim about the eventuality holding now."
    judgment := .acceptable
    alternatives := []
    readings := [("experiential (LA-being at some past subinterval)", .acceptable)]
    paperFeatures := []
    comment := "Pancheva 2003 §1 ex (1b). Subsumed under EXISTENTIAL by McCawley 1971, Mittwoch 1988 (umbrella for Experiential + Resultative); Pancheva keeps the finer Experiential/Resultative distinction."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex1c_RES : LinguisticExample :=
  { id := "pancheva2003_ex1c_RES"
    source := ⟨"pancheva-2003", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alexandra has (just) arrived in LA."
    discourseSegments := []
    glossedTokens := []
    translation := "Alexandra has (just) arrived in LA."
    context := "Resultative (RES) perfect. Same temporal assertion as Experiential, with the added meaning that the result state (be in LA) holds at the utterance time."
    judgment := .acceptable
    alternatives := []
    readings := [("resultative (arrived + still in LA at utterance)", .acceptable)]
    paperFeatures := []
    comment := "Pancheva 2003 §1 ex (1c). The Resultative reading requires a telic predicate (Kratzer 1994: only telic events have a natural result state); see (5)/(6) for the telic vs atelic contrast."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex5a_atelic : LinguisticExample :=
  { id := "pancheva2003_ex5a_atelic"
    source := ⟨"pancheva-2003", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have run."
    discourseSegments := []
    glossedTokens := []
    translation := "I have run."
    context := "Atelic activity participle (`run`). Cannot yield a Resultative reading because activities have no inherent result state (Kratzer 1994). Only the Experiential reading is available."
    judgment := .acceptable
    alternatives := []
    readings := [("experiential (running at some past time)", .acceptable), ("resultative", .ungrammatical)]
    paperFeatures := []
    comment := "Pancheva 2003 §2 ex (5a). Diagnostic for the telic-only restriction on Resultative reading."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex6a_telic : LinguisticExample :=
  { id := "pancheva2003_ex6a_telic"
    source := ⟨"pancheva-2003", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have lost my glasses."
    discourseSegments := []
    glossedTokens := []
    translation := "I have lost my glasses."
    context := "Telic achievement participle (`lose my glasses`). Has both Experiential and Resultative readings. On the Resultative reading, the glasses must still be lost at the utterance time; on the Experiential reading, no such requirement."
    judgment := .acceptable
    alternatives := []
    readings := [("experiential (lost at some past time)", .acceptable), ("resultative (lost + still missing now)", .acceptable)]
    paperFeatures := []
    comment := "Pancheva 2003 §2 ex (6a). The telic contrast partner to (5a). Demonstrates that telic predicates license both readings; atelic predicates only EXP."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1a_U, ex1b_EXP, ex1c_RES, ex5a_atelic, ex6a_telic]

end Pancheva2003.Examples
