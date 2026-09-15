import Linglib.Data.Examples.Schema

/-!
# `YingEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/YingEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace YingEtAl2025.Examples`.
-/

namespace YingEtAl2025.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "yingetal2025_1"
    source := ⟨"ying-zhi-xuan-wong-mansinghka-tenenbaum-2025", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The player believes box 1 may contain a blue key or a red key."
    discourseSegments := []
    glossedTokens := []
    translation := "The player believes box 1 may contain a blue key or a red key."
    context := "A player in the Doors, Keys and Gems gridworld; the sentence describes the player's beliefs about the contents of the boxes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("factor", "Possibility")]
    comment := "A human-written epistemic sentence from the dataset."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "yingetal2025_2"
    source := ⟨"ying-zhi-xuan-wong-mansinghka-tenenbaum-2025", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The player believes if the red key is not in box 2 then it must be in box 3."
    discourseSegments := []
    glossedTokens := []
    translation := "The player believes if the red key is not in box 2 then it must be in box 3."
    context := "A player in the Doors, Keys and Gems gridworld; the sentence describes the player's beliefs about the contents of the boxes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("factor", "Possibility")]
    comment := "A human-written epistemic sentence from the dataset."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "yingetal2025_3"
    source := ⟨"ying-zhi-xuan-wong-mansinghka-tenenbaum-2025", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The player thought that box 1 was most likely to contain a red key."
    discourseSegments := []
    glossedTokens := []
    translation := "The player thought that box 1 was most likely to contain a red key."
    context := "A player in the Doors, Keys and Gems gridworld; the sentence describes the player's beliefs about the contents of the boxes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("factor", "Probability")]
    comment := "A human-written epistemic sentence from the dataset."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "yingetal2025_4"
    source := ⟨"ying-zhi-xuan-wong-mansinghka-tenenbaum-2025", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The player is unsure what color the key in box 2 will be."
    discourseSegments := []
    glossedTokens := []
    translation := "The player is unsure what color the key in box 2 will be."
    context := "A player in the Doors, Keys and Gems gridworld; the sentence describes the player's beliefs about the contents of the boxes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("factor", "Probability")]
    comment := "A human-written epistemic sentence from the dataset."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "yingetal2025_5"
    source := ⟨"ying-zhi-xuan-wong-mansinghka-tenenbaum-2025", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The player thinks that there's more likely to be a red key in box 1 or 3 than box 2."
    discourseSegments := []
    glossedTokens := []
    translation := "The player thinks that there's more likely to be a red key in box 1 or 3 than box 2."
    context := "A player in the Doors, Keys and Gems gridworld; the sentence describes the player's beliefs about the contents of the boxes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("factor", "Compositionality")]
    comment := "A human-written epistemic sentence from the dataset."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "yingetal2025_6"
    source := ⟨"ying-zhi-xuan-wong-mansinghka-tenenbaum-2025", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The player believes that if box 1 does not have a blue key, then box 3 has a blue key."
    discourseSegments := []
    glossedTokens := []
    translation := "The player believes that if box 1 does not have a blue key, then box 3 has a blue key."
    context := "A player in the Doors, Keys and Gems gridworld; the sentence describes the player's beliefs about the contents of the boxes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("factor", "Compositionality")]
    comment := "A human-written epistemic sentence from the dataset."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "yingetal2025_7"
    source := ⟨"ying-zhi-xuan-wong-mansinghka-tenenbaum-2025", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The player already knows for sure there is no key in box 1 or box 2."
    discourseSegments := []
    glossedTokens := []
    translation := "The player already knows for sure there is no key in box 1 or box 2."
    context := "A player in the Doors, Keys and Gems gridworld; the sentence describes the player's beliefs about the contents of the boxes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("factor", "Knowledge")]
    comment := "A human-written epistemic sentence from the dataset."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "yingetal2025_8"
    source := ⟨"ying-zhi-xuan-wong-mansinghka-tenenbaum-2025", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The player did not know if box 2 contained a red key."
    discourseSegments := []
    glossedTokens := []
    translation := "The player did not know if box 2 contained a red key."
    context := "A player in the Doors, Keys and Gems gridworld; the sentence describes the player's beliefs about the contents of the boxes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("factor", "Knowledge")]
    comment := "A human-written epistemic sentence from the dataset."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8]

end YingEtAl2025.Examples
