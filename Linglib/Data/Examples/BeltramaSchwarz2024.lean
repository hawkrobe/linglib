module

public import Linglib.Data.Examples.Schema

/-!
# `BeltramaSchwarz2024` — typed example data

Auto-generated from `Linglib/Data/Examples/BeltramaSchwarz2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeltramaSchwarz2024.Examples`.
-/

@[expose] public section

namespace BeltramaSchwarz2024.Examples

open Data.Examples

def beltrama_schwarz_2024_cst_nopersona : Datum :=
  { id := "beltrama_schwarz_2024_cst_nopersona"
    source := ⟨"beltrama-schwarz-2024", "Exp 1 Imprecise No.Persona"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much is the cheapest ticket? It's $200."
    glossedTokens := []
    context := "Covered-Screen Task (Exp 1). Arthur answers Rachel after looking at his phone; the visible phone shows $207.xx (Imprecise screen fit). No persona described (baseline). Participant chooses the COVERED vs VISIBLE phone; COVERED = the round numeral is read precisely, so the speaker must have seen a different screen (= rejection of the imprecise reading)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("persona", "noPersona"), ("task", "coveredScreen"), ("screenFit", "imprecise"), ("statedAmount", "200"), ("displayedAmount", "207"), ("rejectionMeasure", "covered"), ("rejectionVsBaseline", "baseline"), ("contrastZ", "0"), ("contrastSig", "baseline")] }

def beltrama_schwarz_2024_cst_nerdy : Datum :=
  { id := "beltrama_schwarz_2024_cst_nerdy"
    source := ⟨"beltrama-schwarz-2024", "Exp 1 Imprecise Nerdy"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much is the cheapest ticket? It's $200."
    glossedTokens := []
    context := "Covered-Screen Task (Exp 1). Arthur and Rachel described as Nerdy (studious, articulate, introverted, uptight); visible phone shows $207.xx (Imprecise). COVERED = precise reading = rejection of imprecise reading."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("persona", "nerdy"), ("task", "coveredScreen"), ("screenFit", "imprecise"), ("statedAmount", "200"), ("displayedAmount", "207"), ("rejectionMeasure", "covered"), ("rejectionVsBaseline", "higher"), ("contrastZ", "6.62"), ("contrastSig", "significant")] }

def beltrama_schwarz_2024_cst_chill : Datum :=
  { id := "beltrama_schwarz_2024_cst_chill"
    source := ⟨"beltrama-schwarz-2024", "Exp 1 Imprecise Chill"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much is the cheapest ticket? It's $200."
    glossedTokens := []
    context := "Covered-Screen Task (Exp 1). Arthur and Rachel described as Chill (laid-back, sociable, extroverted, care-free); visible phone shows $207.xx (Imprecise). COVERED = precise reading = rejection of imprecise reading."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("persona", "chill"), ("task", "coveredScreen"), ("screenFit", "imprecise"), ("statedAmount", "200"), ("displayedAmount", "207"), ("rejectionMeasure", "covered"), ("rejectionVsBaseline", "lower"), ("contrastZ", "7.61"), ("contrastSig", "significant")] }

def beltrama_schwarz_2024_tvj_nopersona : Datum :=
  { id := "beltrama_schwarz_2024_tvj_nopersona"
    source := ⟨"beltrama-schwarz-2024", "Exp 2 Imprecise No.Persona"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much is the cheapest ticket? It's $200."
    glossedTokens := []
    context := "Truth-Value Judgment Task (Exp 2). Participant is shown the one phone Arthur is said to be looking at ($207.xx, Imprecise) and judges whether his response is RIGHT or WRONG. No persona described (baseline). WRONG = rejection of the imprecise description, a prejudicial verdict on the speaker."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("persona", "noPersona"), ("task", "truthValueJudgment"), ("screenFit", "imprecise"), ("statedAmount", "200"), ("displayedAmount", "207"), ("rejectionMeasure", "wrong"), ("rejectionVsBaseline", "baseline"), ("contrastZ", "0"), ("contrastSig", "baseline")] }

def beltrama_schwarz_2024_tvj_nerdy : Datum :=
  { id := "beltrama_schwarz_2024_tvj_nerdy"
    source := ⟨"beltrama-schwarz-2024", "Exp 2 Imprecise Nerdy"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much is the cheapest ticket? It's $200."
    glossedTokens := []
    context := "Truth-Value Judgment Task (Exp 2). Arthur described as Nerdy; phone shows $207.xx (Imprecise). WRONG = prejudicial rejection of the speaker's description."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("persona", "nerdy"), ("task", "truthValueJudgment"), ("screenFit", "imprecise"), ("statedAmount", "200"), ("displayedAmount", "207"), ("rejectionMeasure", "wrong"), ("rejectionVsBaseline", "same"), ("contrastZ", "0.15"), ("contrastSig", "null")] }

def beltrama_schwarz_2024_tvj_chill : Datum :=
  { id := "beltrama_schwarz_2024_tvj_chill"
    source := ⟨"beltrama-schwarz-2024", "Exp 2 Imprecise Chill"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much is the cheapest ticket? It's $200."
    glossedTokens := []
    context := "Truth-Value Judgment Task (Exp 2). Arthur described as Chill; phone shows $207.xx (Imprecise). WRONG = prejudicial rejection of the speaker's description."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("persona", "chill"), ("task", "truthValueJudgment"), ("screenFit", "imprecise"), ("statedAmount", "200"), ("displayedAmount", "207"), ("rejectionMeasure", "wrong"), ("rejectionVsBaseline", "lower"), ("contrastZ", "8.43"), ("contrastSig", "significant")] }

def all : List Datum := [beltrama_schwarz_2024_cst_nopersona, beltrama_schwarz_2024_cst_nerdy, beltrama_schwarz_2024_cst_chill, beltrama_schwarz_2024_tvj_nopersona, beltrama_schwarz_2024_tvj_nerdy, beltrama_schwarz_2024_tvj_chill]

end BeltramaSchwarz2024.Examples
