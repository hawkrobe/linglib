module

public import Linglib.Data.Examples.Schema

/-!
# `Geach1962` — typed example data

Auto-generated from `Linglib/Data/Examples/Geach1962.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Geach1962.Examples`.
-/

@[expose] public section

namespace Geach1962.Examples

open Data.Examples

def donkey_classic : Datum :=
  { id := "geach1962_donkey_classic"
    source := ⟨"geach-1962", "UNVERIFIED the donkey sentence"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every farmer who owns a donkey beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strong/universal", .acceptable), ("weak/existential", .acceptable), ("bound", .acceptable)]
    paperFeatures := [("donkey_configuration", "relative_clause"), ("preferred_reading", "strong")] }

def all : List Datum := [donkey_classic]

end Geach1962.Examples
