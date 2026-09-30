module

public import Linglib.Data.Examples.Schema

/-!
# `Merchant2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Merchant2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Merchant2001.Examples`.
-/

@[expose] public section

namespace Merchant2001.Examples

open Data.Examples

def german_case_match : Datum :=
  { id := "merchant2001_german_case_match"
    source := ⟨"merchant-2001", "case-matching under sluicing"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er will jemandem schmeicheln, aber sie wissen nicht, wem."
    glossedTokens := [("Er", "he.NOM"), ("will", "want.PRS.3SG"), ("jemandem", "someone.DAT"), ("schmeicheln", "flatter.INF"), ("aber", "but"), ("sie", "they"), ("wissen", "know.PRS.3PL"), ("nicht", "NEG"), ("wem", "who.DAT")]
    context := "Sluicing: the wh-remnant must bear the case its correlate bears in the antecedent. The verb schmeicheln 'flatter' assigns dative."
    judgment := .acceptable
    alternatives := [("Er will jemandem schmeicheln, aber sie wissen nicht, wen.", .ungrammatical)]
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("whPhraseCase", "dative"), ("innerAntecedentCase", "dative")] }

def all : List Datum := [german_case_match]

end Merchant2001.Examples
