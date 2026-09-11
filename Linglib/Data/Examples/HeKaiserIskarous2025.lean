import Linglib.Data.Examples.Schema

/-!
# `HeKaiserIskarous2025` — typed example data

Auto-generated from `Linglib/Data/Examples/HeKaiserIskarous2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HeKaiserIskarous2025.Examples`.
-/

namespace HeKaiserIskarous2025.Examples

open Data.Examples

def house_no_bathroom : LinguisticExample :=
  { id := "hekaiseriskarous2025_house_no_bathroom"
    source := ⟨"he-kaiser-iskarous-2025", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house doesn't have a bathroom."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("polarity", "negative"), ("statePrior", "low")]
    comment := "A negative sentence about a low-prior state: houses usually have bathrooms."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def house_ballroom : LinguisticExample :=
  { id := "hekaiseriskarous2025_house_ballroom"
    source := ⟨"he-kaiser-iskarous-2025", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house has a ballroom."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("polarity", "positive"), ("statePrior", "low")]
    comment := "A positive sentence about a low-prior state, similarly informative to the negative one but cheaper under the standard model."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def house_no_ballroom : LinguisticExample :=
  { id := "hekaiseriskarous2025_house_no_ballroom"
    source := ⟨"he-kaiser-iskarous-2025", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house doesn't have a ballroom."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("polarity", "negative"), ("statePrior", "high")]
    comment := "Presupposes the possibility of a ballroom, which the listener must accommodate before the update."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_pos : LinguisticExample :=
  { id := "hekaiseriskarous2025_exp1_pos"
    source := ⟨"he-kaiser-iskarous-2025", "§3.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house has a bathroom."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Emma visited a friend's house yesterday."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("polarity", "positive"), ("experiment", "1")]
    comment := "Experiment 1 item: participants rated how likely Emma would be to mention the fact."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_neg : LinguisticExample :=
  { id := "hekaiseriskarous2025_exp1_neg"
    source := ⟨"he-kaiser-iskarous-2025", "§3.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house doesn't have a bathroom."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Emma visited a friend's house yesterday."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("polarity", "negative"), ("experiment", "1")]
    comment := "Experiment 1 item, the negative counterpart of the same part-whole relation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def classroom_no_board : LinguisticExample :=
  { id := "hekaiseriskarous2025_classroom_no_board"
    source := ⟨"he-kaiser-iskarous-2025", "§3.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The classroom doesn't have a board."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("polarity", "negative"), ("statePrior", "low")]
    comment := "A low-prior negative-polarity situation, rated more likely to be communicated than a positive one of similar prior."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def classroom_stove : LinguisticExample :=
  { id := "hekaiseriskarous2025_classroom_stove"
    source := ⟨"he-kaiser-iskarous-2025", "§3.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The classroom has a stove."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("polarity", "positive"), ("statePrior", "low")]
    comment := "A low-prior positive-polarity situation, rated less likely to be communicated than the negative one above."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp2 : LinguisticExample :=
  { id := "hekaiseriskarous2025_exp2"
    source := ⟨"he-kaiser-iskarous-2025", "§3.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "“The house has a bathroom,” Emma told her partner."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("polarity", "positive"), ("experiment", "2")]
    comment := "Experiment 2 item: the fact statement in direct speech; participants rated how typical a house the house is."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [house_no_bathroom, house_ballroom, house_no_ballroom, exp1_pos, exp1_neg, classroom_no_board, classroom_stove, exp2]

end HeKaiserIskarous2025.Examples
