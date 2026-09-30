module

public import Linglib.Data.Examples.Schema

/-!
# `SolstadBott2024` — typed example data

Auto-generated from `Linglib/Data/Examples/SolstadBott2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SolstadBott2024.Examples`.
-/

@[expose] public section

namespace SolstadBott2024.Examples

def sb2024_exp1_occasion : Datum :=
  { id := "sb2024_exp1_occasion"
    source := ⟨"solstad-bott-2024", "Exp 1, occasion verbs (16 German occasion verbs)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie dankte ihm."
    glossedTokens := []
    context := "Projective content 'there was an occasion for her to thank him' under the certain-that / asking-whether diagnostics (Exp 1)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "occasion"), ("experiment", "1"), ("verbClass", "agentEvocator"), ("triggerClass", "C"), ("projectivity", "79"), ("atIssueness", "32")] }

def sb2024_exp2_occasion : Datum :=
  { id := "sb2024_exp2_occasion"
    source := ⟨"solstad-bott-2024", "Exp 2, occasion verbs (14 of 16; loben/gratulieren excluded)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie dankte ihm."
    glossedTokens := []
    context := "Projective content 'there was an occasion for her to thank him' under the certain-that / asking-whether diagnostics (Exp 2)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "occasion"), ("experiment", "2"), ("verbClass", "agentEvocator"), ("triggerClass", "C"), ("projectivity", "69"), ("atIssueness", "35")] }

def sb2024_exp2_stimulusExperiencer : Datum :=
  { id := "sb2024_exp2_stimulusExperiencer"
    source := ⟨"solstad-bott-2024", "Exp 2, stimulus-experiencer psych verbs (9 verbs)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie schockierte ihn zutiefst."
    glossedTokens := []
    context := "Projective content 'she did something the experiencer might find shocking' under the certain-that / asking-whether diagnostics (Exp 2)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "stimulusExperiencer"), ("experiment", "2"), ("verbClass", "stimExp"), ("triggerClass", "C"), ("projectivity", "54"), ("atIssueness", "52")] }

def sb2024_exp2_experiencerStimulus : Datum :=
  { id := "sb2024_exp2_experiencerStimulus"
    source := ⟨"solstad-bott-2024", "Exp 2, experiencer-stimulus psych verbs (9 verbs)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie bewunderte ihn."
    glossedTokens := []
    context := "Projective content 'a relevant property of the stimulus argument' under the certain-that / asking-whether diagnostics (Exp 2)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "experiencerStimulus"), ("experiment", "2"), ("verbClass", "expStim"), ("triggerClass", "C"), ("projectivity", "52"), ("atIssueness", "46")] }

def all : List Datum := [sb2024_exp1_occasion, sb2024_exp2_occasion, sb2024_exp2_stimulusExperiencer, sb2024_exp2_experiencerStimulus]

end SolstadBott2024.Examples
