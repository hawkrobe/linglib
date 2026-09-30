module

public import Linglib.Data.Examples.Schema

/-!
# `TonhauserBeaverDegen2018` — typed example data

Auto-generated from `Linglib/Data/Examples/TonhauserBeaverDegen2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TonhauserBeaverDegen2018.Examples`.
-/

@[expose] public section

namespace TonhauserBeaverDegen2018.Examples

open Data.Examples

def tbd2018_1a_nrrc : LinguisticExample :=
  { id := "tbd2018_1a_nrrc"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1a (12.1), NRRC"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These muffins, which have blueberries in them, are gluten-free and low-fat."
    glossedTokens := []
    context := "Projective content 'These muffins have blueberries in them.' under the certain-that / asking-whether diagnostics (Exp 1a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "NRRC"), ("experiment", "1a"), ("triggerClass", "B"), ("projectivity", "96"), ("notAtIssueness", "97")] }

def tbd2018_1a_nominalAppositive : LinguisticExample :=
  { id := "tbd2018_1a_nominalAppositive"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1a (12.2), nominal appositive"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martha's new car, a BMW, was expensive."
    glossedTokens := []
    context := "Projective content 'Martha's new car is a BMW.' under the certain-that / asking-whether diagnostics (Exp 1a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "nominalAppositive"), ("experiment", "1a"), ("triggerClass", "B"), ("projectivity", "95"), ("notAtIssueness", "96")] }

def tbd2018_1a_possessiveNP : LinguisticExample :=
  { id := "tbd2018_1a_possessiveNP"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1a (12.3), possessive NP"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martha's new BMW was expensive."
    glossedTokens := []
    context := "Projective content 'Martha has a new BMW.' under the certain-that / asking-whether diagnostics (Exp 1a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "possessiveNP"), ("experiment", "1a"), ("triggerClass", "B"), ("projectivity", "94"), ("notAtIssueness", "97")] }

def tbd2018_1a_annoyed : LinguisticExample :=
  { id := "tbd2018_1a_annoyed"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1a (12.4), be annoyed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martha's neighbor is annoyed that Martha has a new BMW."
    glossedTokens := []
    context := "Projective content 'Martha has a new BMW.' under the certain-that / asking-whether diagnostics (Exp 1a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "annoyed"), ("experiment", "1a"), ("triggerClass", "C"), ("projectivity", "96"), ("notAtIssueness", "97")] }

def tbd2018_1a_discover : LinguisticExample :=
  { id := "tbd2018_1a_discover"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1a (12.5), discover"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary discovered that her daughter has been biting her nails."
    glossedTokens := []
    context := "Projective content 'Mary's daughter has been biting her nails.' under the certain-that / asking-whether diagnostics (Exp 1a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "discover"), ("experiment", "1a"), ("triggerClass", "C"), ("projectivity", "86"), ("notAtIssueness", "87")] }

def tbd2018_1a_know : LinguisticExample :=
  { id := "tbd2018_1a_know"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1a (12.6), know"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Billy knows that Martha has a new BMW."
    glossedTokens := []
    context := "Projective content 'Martha has a new BMW.' under the certain-that / asking-whether diagnostics (Exp 1a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "know"), ("experiment", "1a"), ("triggerClass", "C"), ("projectivity", "92"), ("notAtIssueness", "91")] }

def tbd2018_1a_only : LinguisticExample :=
  { id := "tbd2018_1a_only"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1a (12.7), only"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These muffins only have blueberries in them."
    glossedTokens := []
    context := "Projective content 'These muffins have blueberries in them.' under the certain-that / asking-whether diagnostics (Exp 1a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "only"), ("experiment", "1a"), ("triggerClass", "C"), ("projectivity", "76"), ("notAtIssueness", "72")] }

def tbd2018_1a_stop : LinguisticExample :=
  { id := "tbd2018_1a_stop"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1a (12.8), stop"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's daughter stopped biting her nails."
    glossedTokens := []
    context := "Projective content 'Mary's daughter has been biting her nails.' under the certain-that / asking-whether diagnostics (Exp 1a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "stop"), ("experiment", "1a"), ("triggerClass", "C"), ("projectivity", "87"), ("notAtIssueness", "71")] }

def tbd2018_1a_stupid : LinguisticExample :=
  { id := "tbd2018_1a_stupid"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1a (12.9), be stupid to"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's daughter is stupid to be biting her nails."
    glossedTokens := []
    context := "Projective content 'Mary's daughter has been biting her nails.' under the certain-that / asking-whether diagnostics (Exp 1a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "stupid"), ("experiment", "1a"), ("triggerClass", "C"), ("projectivity", "85"), ("notAtIssueness", "88")] }

def tbd2018_1b_amused : LinguisticExample :=
  { id := "tbd2018_1b_amused"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, be amused"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shirley is amused that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "amused"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "91"), ("notAtIssueness", "94")] }

def tbd2018_1b_annoyed : LinguisticExample :=
  { id := "tbd2018_1b_annoyed"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, be annoyed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shirley is annoyed that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "annoyed"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "92"), ("notAtIssueness", "94")] }

def tbd2018_1b_aware : LinguisticExample :=
  { id := "tbd2018_1b_aware"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, be aware"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shirley is aware that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "aware"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "92"), ("notAtIssueness", "94")] }

def tbd2018_1b_confess : LinguisticExample :=
  { id := "tbd2018_1b_confess"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, confess"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shirley confessed that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "confess"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "69"), ("notAtIssueness", "81")] }

def tbd2018_1b_discover : LinguisticExample :=
  { id := "tbd2018_1b_discover"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, discover"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Samuel discovered that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "discover"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "85"), ("notAtIssueness", "89")] }

def tbd2018_1b_establish : LinguisticExample :=
  { id := "tbd2018_1b_establish"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, establish"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shirley established that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "establish"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "42"), ("notAtIssueness", "61")] }

def tbd2018_1b_findOut : LinguisticExample :=
  { id := "tbd2018_1b_findOut"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, find out"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shirley found out that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "findOut"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "88"), ("notAtIssueness", "91")] }

def tbd2018_1b_learn : LinguisticExample :=
  { id := "tbd2018_1b_learn"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, learn"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shirley learned that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "learn"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "88"), ("notAtIssueness", "90")] }

def tbd2018_1b_notice : LinguisticExample :=
  { id := "tbd2018_1b_notice"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, notice"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shirley noticed that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "notice"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "92"), ("notAtIssueness", "92")] }

def tbd2018_1b_realize : LinguisticExample :=
  { id := "tbd2018_1b_realize"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, realize"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shirley realized that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "realize"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "91"), ("notAtIssueness", "92")] }

def tbd2018_1b_reveal : LinguisticExample :=
  { id := "tbd2018_1b_reveal"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, reveal"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shirley revealed that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "reveal"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "78"), ("notAtIssueness", "87")] }

def tbd2018_1b_see : LinguisticExample :=
  { id := "tbd2018_1b_see"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b, see"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shirley saw that Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "see"), ("experiment", "1b"), ("triggerClass", "C"), ("projectivity", "89"), ("notAtIssueness", "89")] }

def tbd2018_1a_mc : LinguisticExample :=
  { id := "tbd2018_1a_mc"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1a (15), main-clause control"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Richie is a stuntman."
    glossedTokens := []
    context := "Projective content 'Richie is a stuntman.' under the certain-that / asking-whether diagnostics (Exp 1a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "mainClause"), ("experiment", "1a"), ("triggerClass", "control"), ("projectivity", "5"), ("notAtIssueness", "2"), ("control", "true")] }

def tbd2018_1b_mc : LinguisticExample :=
  { id := "tbd2018_1b_mc"
    source := ⟨"tonhauser-beaver-degen-2018", "Exp 1b (17), main-clause control"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Raul was drinking chamomile tea."
    glossedTokens := []
    context := "Projective content 'Raul was drinking chamomile tea.' under the certain-that / asking-whether diagnostics (Exp 1b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "mainClause"), ("experiment", "1b"), ("triggerClass", "control"), ("projectivity", "6"), ("notAtIssueness", "3"), ("control", "true")] }

def all : List LinguisticExample := [tbd2018_1a_nrrc, tbd2018_1a_nominalAppositive, tbd2018_1a_possessiveNP, tbd2018_1a_annoyed, tbd2018_1a_discover, tbd2018_1a_know, tbd2018_1a_only, tbd2018_1a_stop, tbd2018_1a_stupid, tbd2018_1b_amused, tbd2018_1b_annoyed, tbd2018_1b_aware, tbd2018_1b_confess, tbd2018_1b_discover, tbd2018_1b_establish, tbd2018_1b_findOut, tbd2018_1b_learn, tbd2018_1b_notice, tbd2018_1b_realize, tbd2018_1b_reveal, tbd2018_1b_see, tbd2018_1a_mc, tbd2018_1b_mc]

end TonhauserBeaverDegen2018.Examples
