import Linglib.Data.Examples.Schema

/-!
# `SolstadBott2024` — typed example data

Auto-generated from `Linglib/Data/Examples/SolstadBott2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SolstadBott2024.Examples`.
-/

namespace SolstadBott2024.Examples

open Data.Examples

def sb2024_exp1_occasion : LinguisticExample :=
  { id := "sb2024_exp1_occasion"
    source := ⟨"solstad-bott-2024", "Exp 1, occasion verbs (16 German occasion verbs)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie dankte ihm."
    discourseSegments := []
    glossedTokens := []
    translation := "She thanked him."
    context := "Projective content 'there was an occasion for her to thank him' under the certain-that / asking-whether diagnostics (Exp 1)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "occasion"), ("experiment", "1"), ("verbClass", "agentEvocator"), ("triggerClass", "C"), ("projectivity", "79"), ("atIssueness", "32")]
    comment := "Mean projectivity .79 and at-issueness .32 (ratings on the certain-that / asking-whether diagnostics of [tonhauser-beaver-degen-2018], rescaled to [0,1], n=71), Exp 1 Block 2 (osf.io/76rxb). Projective content: 'there was an occasion for her to thank him'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sb2024_exp2_occasion : LinguisticExample :=
  { id := "sb2024_exp2_occasion"
    source := ⟨"solstad-bott-2024", "Exp 2, occasion verbs (14 of 16; loben/gratulieren excluded)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie dankte ihm."
    discourseSegments := []
    glossedTokens := []
    translation := "She thanked him."
    context := "Projective content 'there was an occasion for her to thank him' under the certain-that / asking-whether diagnostics (Exp 2)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "occasion"), ("experiment", "2"), ("verbClass", "agentEvocator"), ("triggerClass", "C"), ("projectivity", "69"), ("atIssueness", "35")]
    comment := "Mean projectivity .69 and at-issueness .35 (ratings on the certain-that / asking-whether diagnostics of [tonhauser-beaver-degen-2018], rescaled to [0,1], n=60), Exp 2 Block 2 (osf.io/76rxb). Projective content: 'there was an occasion for her to thank him'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sb2024_exp2_stimulusExperiencer : LinguisticExample :=
  { id := "sb2024_exp2_stimulusExperiencer"
    source := ⟨"solstad-bott-2024", "Exp 2, stimulus-experiencer psych verbs (9 verbs)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie schockierte ihn zutiefst."
    discourseSegments := []
    glossedTokens := []
    translation := "She shocked him deeply."
    context := "Projective content 'she did something the experiencer might find shocking' under the certain-that / asking-whether diagnostics (Exp 2)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "stimulusExperiencer"), ("experiment", "2"), ("verbClass", "stimExp"), ("triggerClass", "C"), ("projectivity", "54"), ("atIssueness", "52")]
    comment := "Mean projectivity .54 and at-issueness .52 (ratings on the certain-that / asking-whether diagnostics of [tonhauser-beaver-degen-2018], rescaled to [0,1], n=60), Exp 2 Block 2 (osf.io/76rxb). Projective content: 'she did something the experiencer might find shocking'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sb2024_exp2_experiencerStimulus : LinguisticExample :=
  { id := "sb2024_exp2_experiencerStimulus"
    source := ⟨"solstad-bott-2024", "Exp 2, experiencer-stimulus psych verbs (9 verbs)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie bewunderte ihn."
    discourseSegments := []
    glossedTokens := []
    translation := "She admired him."
    context := "Projective content 'a relevant property of the stimulus argument' under the certain-that / asking-whether diagnostics (Exp 2)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "experiencerStimulus"), ("experiment", "2"), ("verbClass", "expStim"), ("triggerClass", "C"), ("projectivity", "52"), ("atIssueness", "46")]
    comment := "Mean projectivity .52 and at-issueness .46 (ratings on the certain-that / asking-whether diagnostics of [tonhauser-beaver-degen-2018], rescaled to [0,1], n=60), Exp 2 Block 2 (osf.io/76rxb). Projective content: 'a relevant property of the stimulus argument'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [sb2024_exp1_occasion, sb2024_exp2_occasion, sb2024_exp2_stimulusExperiencer, sb2024_exp2_experiencerStimulus]

end SolstadBott2024.Examples
