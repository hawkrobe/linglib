import Linglib.Data.Examples.Schema

/-!
# `Krifka1998` — typed example data

Auto-generated from `Linglib/Data/Examples/Krifka1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Krifka1998.Examples`.
-/

namespace Krifka1998.Examples

open Data.Examples

def arrive_at_store : LinguisticExample :=
  { id := "krifka1998_arrive_at_store"
    source := ⟨"krifka-1998", "§4.5 arrive (bounded path)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary arrived at the store in five minutes."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary arrived at the store in five minutes."
    context := "Inherently directed motion with a specified goal: the path is bounded (has an endpoint), so the VP is telic and accepts the in-X adverbial."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pathShape", "bounded"), ("expectedTelicity", "telic")]
    comment := "Migrated from the deleted MotionVPDatum table in Studies/Krifka1998.lean. UNVERIFIED paperLabel: section carried from prior Lean docstrings, eq. numbers dropped pending PDF check."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def leave_the_house : LinguisticExample :=
  { id := "krifka1998_leave_the_house"
    source := ⟨"krifka-1998", "§4.5 leave (source path)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary left the house in a moment."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary left the house in a moment."
    context := "Leave verb specifying a source: the path is bounded at its origin, so the VP is telic and accepts the in-X adverbial."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pathShape", "source"), ("expectedTelicity", "telic")]
    comment := "Migrated from the deleted MotionVPDatum table in Studies/Krifka1998.lean. UNVERIFIED paperLabel: section carried from prior Lean docstrings."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def run_to_park : LinguisticExample :=
  { id := "krifka1998_run_to_park"
    source := ⟨"krifka-1998", "§4.5 run to (bounded PP)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary ran to the park in ten minutes."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary ran to the park in ten minutes."
    context := "Manner-of-motion verb plus a goal PP: the directional to-PP supplies a bounded path, so the otherwise atelic verb yields a telic VP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pathShape", "bounded"), ("expectedTelicity", "telic")]
    comment := "Migrated from the deleted MotionVPDatum table in Studies/Krifka1998.lean. UNVERIFIED paperLabel: section carried from prior Lean docstrings."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def run_towards_park : LinguisticExample :=
  { id := "krifka1998_run_towards_park"
    source := ⟨"krifka-1998", "§4.5 run towards (unbounded PP)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary ran towards the park for ten minutes."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary ran towards the park for ten minutes."
    context := "Manner-of-motion verb plus a towards-PP: direction without a goal supplies an unbounded path, so the VP is atelic and takes for-X, not in-X."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pathShape", "unbounded"), ("expectedTelicity", "atelic")]
    comment := "Migrated from the deleted MotionVPDatum table in Studies/Krifka1998.lean. UNVERIFIED paperLabel: section carried from prior Lean docstrings."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [arrive_at_store, leave_the_house, run_to_park, run_towards_park]

end Krifka1998.Examples
