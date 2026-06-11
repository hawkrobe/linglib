import Linglib.Data.Examples.Schema

/-!
# `Charlow2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Charlow2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Charlow2014.Examples`.
-/

namespace Charlow2014.Examples

open Data.Examples

def donkey1 : LinguisticExample :=
  { id := "charlow2014_donkey1"
    source := ⟨"geach-1962", "ch. III, the donkey sentence"⟩
    reportedIn := some ⟨"charlow-2014", "Ch. 2 donkey case"⟩
    language := "stan1293"
    primaryText := "Every farmer who owns a donkey beats it."
    discourseSegments := []
    glossedTokens := [("Every", "every"), ("farmer", "farmer"), ("who", "REL.ANIM"), ("owns", "own.PRS.3SG"), ("a", "INDEF"), ("donkey", "donkey"), ("beats", "beat.PRS.3SG"), ("it", "3SG.N")]
    translation := "Every farmer who owns a donkey beats it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "The Geach donkey sentence (Geach 1962, Reference and Generality, ch. III). Charlow 2014 cites this as the central case for the dynamic-anaphora frameworks comparison. Note: the INDEF gloss for \"a donkey\" papers over the existential-vs-open-variable dispute that is the literature's whole subject; an alternative encoding would project the determiner status into a separate field once the schema gains paper-relativized claim layers."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [donkey1]

end Charlow2014.Examples
