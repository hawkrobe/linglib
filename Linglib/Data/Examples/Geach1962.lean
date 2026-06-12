import Linglib.Data.Examples.Schema

/-!
# `Geach1962` — typed example data

Auto-generated from `Linglib/Data/Examples/Geach1962.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Geach1962.Examples`.
-/

namespace Geach1962.Examples

open Data.Examples

def donkey_classic : LinguisticExample :=
  { id := "geach1962_donkey_classic"
    source := ⟨"geach-1962", "UNVERIFIED the donkey sentence"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every farmer who owns a donkey beats it."
    discourseSegments := []
    glossedTokens := []
    translation := "Every farmer who owns a donkey beats it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strong/universal", .acceptable), ("weak/existential", .acceptable), ("bound", .acceptable)]
    paperFeatures := [("donkey_configuration", "relative_clause"), ("preferred_reading", "strong")]
    comment := "Migrated from Phenomena/Anaphora/DonkeyAnaphora.lean geachDonkey. The original donkey sentence: 'a donkey' sits inside a relative clause and does not c-command 'it', yet binds it. The strong (every donkey they own) reading is preferred out of the blue; the weak (some donkey they own) reading is less salient."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [donkey_classic]

end Geach1962.Examples
