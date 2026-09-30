module

public import Linglib.Data.Examples.Schema

/-!
# `OgiharaSteinertThrelkeld2024` — typed example data

Auto-generated from `Linglib/Data/Examples/OgiharaSteinertThrelkeld2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace OgiharaSteinertThrelkeld2024.Examples`.
-/

@[expose] public section

namespace OgiharaSteinertThrelkeld2024.Examples

open Data.Examples

def ost2024_after_veridical : Datum :=
  { id := "ost2024_after_veridical"
    source := ⟨"ogihara-steinert-threlkeld-2024", "veridicality"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He left after she arrived."
    glossedTokens := []
    context := "*After* is veridical: the sentence entails that she arrived."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "veridicality"), ("connective", "after"), ("complement_entailed", "true")] }

def ost2024_before_nonveridical : Datum :=
  { id := "ost2024_before_nonveridical"
    source := ⟨"ogihara-steinert-threlkeld-2024", "veridicality"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He left before she arrived."
    glossedTokens := []
    context := "*Before* is non-veridical: compatible with her arriving (veridical), not arriving (counterfactual), or indeterminate (non-committal)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "veridicality"), ("connective", "before"), ("complement_entailed", "false")] }

def ost2024_before_counterfactual : Datum :=
  { id := "ost2024_before_counterfactual"
    source := ⟨"ogihara-steinert-threlkeld-2024", "veridicality"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bomb exploded before anyone defused it."
    glossedTokens := []
    context := "Counterfactual reading of *before*: the defusing did not occur ([beaver-condoravdi-2003], the \"barely prevented\" reading)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "veridicality"), ("connective", "before"), ("complement_entailed", "false")] }

def ost2024_after_veridical_2 : Datum :=
  { id := "ost2024_after_veridical_2"
    source := ⟨"ogihara-steinert-threlkeld-2024", "veridicality"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She finished her coffee after he left."
    glossedTokens := []
    context := "*After* is veridical: the sentence entails that he left."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "veridicality"), ("connective", "after"), ("complement_entailed", "true")] }

def ost2024_before_noncommittal : Datum :=
  { id := "ost2024_before_noncommittal"
    source := ⟨"beaver-condoravdi-2003", "(43)"⟩
    reportedIn := some ⟨"ogihara-steinert-threlkeld-2024", "veridicality"⟩
    language := "stan1293"
    primaryText := "I left the party before there was any trouble."
    glossedTokens := []
    context := "Non-committal reading of *before*: implies trouble seemed likely but does not commit to whether it occurred. (B&C (22), the Supreme Court \"uncounted votes\" case, is counterfactual, not non-committal — B&C §6.)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "veridicality"), ("connective", "before"), ("complement_entailed", "false")] }

def ost2024_before_counterfactual_mozart : Datum :=
  { id := "ost2024_before_counterfactual_mozart"
    source := ⟨"beaver-condoravdi-2003", "(24)"⟩
    reportedIn := some ⟨"ogihara-steinert-threlkeld-2024", "veridicality"⟩
    language := "stan1293"
    primaryText := "Mozart died before he finished the Requiem."
    glossedTokens := []
    context := "Counterfactual reading of *before*: Mozart never finished the Requiem."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "veridicality"), ("connective", "before"), ("complement_entailed", "false")] }

def ost2024_ohtani : Datum :=
  { id := "ost2024_ohtani"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately, the 2021 MLB season will be over before Shohei Ohtani earns his 10th win of the season."
    glossedTokens := []
    context := "Uttered in the middle of September 2021. The A-time is the end of the 2021 MLB season; the complement (Ohtani's 10th win) can only occur during the season, before the A-time — a counterexample to B&C's forward-branching alt(w,t)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "bc_counterexample"), ("reading", "counterfactual")] }

def ost2024_snow : Datum :=
  { id := "ost2024_snow"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "2020 might come to an end before it snows for the first time this year."
    glossedTokens := []
    context := "Uttered on Christmas Day 2020. *This year* refers to 2020; the first snow of 2020 can only occur in 2020, so a modal alternative placing it after 2020 does not work."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "bc_counterexample"), ("reading", "nonCommittal")] }

def ost2024_nostradamus : Datum :=
  { id := "ost2024_nostradamus"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(20c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "July 1999 will come to an end before Nostradamus' prophecy about the end of the world comes true."
    glossedTokens := []
    context := "Uttered a few minutes before the end of July 1999. The prophecy (a King of terror in July 1999) can only come true in July 1999 — not after."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "bc_counterexample"), ("reading", "counterfactual")] }

def ost2024_noncommittal_available : Datum :=
  { id := "ost2024_noncommittal_available"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary will leave the party before Bill gets drunk."
    glossedTokens := []
    context := "Non-committal reading available: Bill's getting drunk is a normal continuation of being at a party."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "noncommittal"), ("noncommittal_available", "true")] }

def ost2024_noncommittal_unavailable : Datum :=
  { id := "ost2024_noncommittal_unavailable"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary will leave the party before Quebec becomes an independent country."
    glossedTokens := []
    context := "Non-committal reading unavailable (odd): Quebec's independence is not a contextually normal continuation of the party."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "noncommittal"), ("noncommittal_available", "false")] }

def all : List Datum := [ost2024_after_veridical, ost2024_before_nonveridical, ost2024_before_counterfactual, ost2024_after_veridical_2, ost2024_before_noncommittal, ost2024_before_counterfactual_mozart, ost2024_ohtani, ost2024_snow, ost2024_nostradamus, ost2024_noncommittal_available, ost2024_noncommittal_unavailable]

end OgiharaSteinertThrelkeld2024.Examples
