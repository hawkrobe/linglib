import Linglib.Data.Examples.Schema

/-!
# `EngelhardtEtAl2006` — typed example data

Auto-generated from `Linglib/Data/Examples/EngelhardtEtAl2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace EngelhardtEtAl2006.Examples`.
-/

namespace EngelhardtEtAl2006.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "engelhardtetal2006_1"
    source := ⟨"engelhardt-etal-2006", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Put the apple on the towel in the box."
    discourseSegments := []
    glossedTokens := []
    translation := "Put the apple on the towel in the box."
    context := "A display with one apple, on a towel; an empty towel; an empty box."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ambiguity", "ambiguous")]
    comment := "The temporarily ambiguous instruction of Tanenhaus et al. (1995), on the towel a modifier of the apple or the destination: listeners fixate the empty towel on hearing the prepositional phrase in the one-referent display."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "engelhardtetal2006_2"
    source := ⟨"engelhardt-etal-2006", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Put the apple that's on the towel in the box."
    discourseSegments := []
    glossedTokens := []
    translation := "Put the apple that's on the towel in the box."
    context := "A display with one apple, on a towel; an empty towel; an empty box."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ambiguity", "unambiguous")]
    comment := "The unambiguous counterpart of (1)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "engelhardtetal2006_3"
    source := ⟨"engelhardt-etal-2006", "Table 1, (3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Put the apple on the towel."
    discourseSegments := []
    glossedTokens := []
    translation := "Put the apple on the towel."
    context := "The apple is on a towel and is to be moved to the other towel."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("target", "bare"), ("destination", "towel")]
    comment := "Bare target, matching location: the location is under-described, since the apple is already on a towel. Speakers never produced it and listeners rated it lowest of the four."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "engelhardtetal2006_4"
    source := ⟨"engelhardt-etal-2006", "Table 1, (4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Put the apple in the box."
    discourseSegments := []
    glossedTokens := []
    translation := "Put the apple in the box."
    context := "The apple is on a towel and is to be moved to the box."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("target", "bare"), ("destination", "box")]
    comment := "Bare target, different location: concise in the one-referent display, an under-description of the target in the two-referent display."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "engelhardtetal2006_5"
    source := ⟨"engelhardt-etal-2006", "Table 1, (5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Put the apple on the towel on the other towel."
    discourseSegments := []
    glossedTokens := []
    translation := "Put the apple on the towel on the other towel."
    context := "The apple is on a towel and is to be moved to the other towel."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("target", "modified"), ("destination", "otherTowel")]
    comment := "Modified target, matching location: the target is over-described in the one-referent display; the location carries the pre-nominal modifier other."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "engelhardtetal2006_6"
    source := ⟨"engelhardt-etal-2006", "Table 1, (6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Put the apple on the towel in the box."
    discourseSegments := []
    glossedTokens := []
    translation := "Put the apple on the towel in the box."
    context := "The apple is on a towel and is to be moved to the box."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("target", "modified"), ("destination", "box")]
    comment := "Modified target, different location: an over-description in the one-referent display, the modification required in the two-referent display. In Experiment 3 listeners fixated the empty towel on hearing on the towel and were delayed in fixating the box."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "engelhardtetal2006_7"
    source := ⟨"engelhardt-etal-2006", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Put the apple in the box on the towel."
    discourseSegments := []
    glossedTokens := []
    translation := "Put the apple in the box on the towel."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Recorded so that the bare target instruction of the matching condition could be cut from it with the prosody of (6)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7]

end EngelhardtEtAl2006.Examples
