import Linglib.Data.Examples.Schema

/-!
# `LevinRappaportHovav1995` — typed example data

Auto-generated from `Linglib/Data/Examples/LevinRappaportHovav1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace LevinRappaportHovav1995.Examples`.
-/

namespace LevinRappaportHovav1995.Examples

open Data.Examples

def loc_arrive : LinguisticExample :=
  { id := "levinrappaporthovav1995_loc_arrive"
    source := ⟨"levin-hovav-1995", "UNVERIFIED locative inversion of an unaccusative (no example number recorded)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Into the room arrived a messenger."
    discourseSegments := []
    glossedTokens := []
    translation := "Into the room arrived a messenger."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "locative_inversion"), ("verb", "arrive"), ("verb_class", "unaccusative")]
    comment := "Migrated from Phenomena/ArgumentStructure/Unaccusativity/Data.lean loc_arrive. Attribution follows the dissolved file's header citation [levin-hovav-1995]; locative inversion of unaccusatives is their flagship diagnostic. Consumed by Studies/Storment2026.lean for the unified smuggling analysis of LI."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def loc_whisper : LinguisticExample :=
  { id := "levinrappaporthovav1995_loc_whisper"
    source := ⟨"levin-hovav-1995", "UNVERIFIED locative inversion of a manner-of-speaking verb (no example number recorded)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "From the back of the room whispered a voice."
    discourseSegments := []
    glossedTokens := []
    translation := "From the back of the room whispered a voice."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "locative_inversion"), ("verb", "whisper"), ("verb_class", "manner_of_speaking")]
    comment := "Migrated from Phenomena/ArgumentStructure/Unaccusativity/Data.lean loc_whisper. Manner-of-speaking verbs show variable acceptability in locative inversion. Attribution follows the dissolved file's header citation [levin-hovav-1995]."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [loc_arrive, loc_whisper]

end LevinRappaportHovav1995.Examples
