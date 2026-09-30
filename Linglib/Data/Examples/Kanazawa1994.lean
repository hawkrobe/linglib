module

public import Linglib.Data.Examples.Schema

/-!
# `Kanazawa1994` — typed example data

Auto-generated from `Linglib/Data/Examples/Kanazawa1994.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kanazawa1994.Examples`.
-/

@[expose] public section

namespace Kanazawa1994.Examples

open Data.Examples

def strong_dominant : Datum :=
  { id := "kanazawa1994_strong_dominant"
    source := ⟨"geach-1962", "UNVERIFIED the donkey sentence"⟩
    reportedIn := some ⟨"kanazawa-1994", "UNVERIFIED strong reading dominant out of the blue"⟩
    language := "stan1293"
    primaryText := "Every farmer who owns a donkey beats it."
    glossedTokens := []
    context := "Out of the blue"
    judgment := .acceptable
    alternatives := []
    readings := [("strong/universal", .acceptable), ("weak/existential", .acceptable)]
    paperFeatures := [("preferred_reading", "strong"), ("quantifier_monotonicity", "upward")] }

def all : List Datum := [strong_dominant]

end Kanazawa1994.Examples
