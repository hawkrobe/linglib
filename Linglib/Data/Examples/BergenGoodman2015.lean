import Linglib.Data.Examples.Schema

/-!
# `BergenGoodman2015` — typed example data

Auto-generated from `Linglib/Data/Examples/BergenGoodman2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BergenGoodman2015.Examples`.
-/

namespace BergenGoodman2015.Examples

open Data.Examples

def stressed_subject : LinguisticExample :=
  { id := "bergengoodman2015_stressed_subject"
    source := ⟨"bergen-goodman-2015", "UNVERIFIED (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "BOB went to the movies."
    discourseSegments := []
    glossedTokens := []
    translation := "BOB went to the movies."
    context := "Q: Who went to the movies? (CAPS = prosodic stress)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "subject"), ("reading", "exhaustive")]
    comment := "Migrated from Phenomena/Focus/ProsodicExhaustivity.lean stressedSubject. Stress on the subject signals exhaustive knowledge: only Bob went. Modeled by the noisy-channel ProsodyModel in Studies/BergenGoodman2015.lean (stress reduces the noise rate on the stressed word)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def unstressed_subject : LinguisticExample :=
  { id := "bergengoodman2015_unstressed_subject"
    source := ⟨"bergen-goodman-2015", "UNVERIFIED section 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob went to the movies."
    discourseSegments := []
    glossedTokens := []
    translation := "Bob went to the movies."
    context := "Q: Who went to the movies?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "none"), ("reading", "nonExhaustive")]
    comment := "Migrated from Phenomena/Focus/ProsodicExhaustivity.lean unstressedSubject. Without stress the answer is compatible with others having gone too."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [stressed_subject, unstressed_subject]

end BergenGoodman2015.Examples
