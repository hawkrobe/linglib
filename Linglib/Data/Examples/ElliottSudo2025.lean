import Linglib.Data.Examples.Schema

/-!
# `ElliottSudo2025` — typed example data

Auto-generated from `Linglib/Data/Examples/ElliottSudo2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ElliottSudo2025.Examples`.
-/

namespace ElliottSudo2025.Examples

open Data.Examples

def double_negation : LinguisticExample :=
  { id := "elliottsudo2025_double_negation"
    source := ⟨"elliott-sudo-2025", "UNVERIFIED double negation enables anaphora"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that John didn't see a bird. It was singing."
    discourseSegments := ["It's not the case that John didn't see a bird.", "It was singing."]
    glossedTokens := []
    translation := "It's not the case that John didn't see a bird. It was singing."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "double_negation")]
    comment := "Migrated from Phenomena/Anaphora/CrossSentential.lean doubleNegation. Doubly negated indefinites license cross-sentential anaphora, in contrast with single negation (heim1982_standard_negation_blocks). DPL predicts infelicity here because its negation is a test (double negation elimination fails for anaphora); bilateral update semantics recovers the binding."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [double_negation]

end ElliottSudo2025.Examples
