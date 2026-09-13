import Linglib.Data.Examples.Schema

/-!
# `PoesioEtAl2004` — typed example data

Auto-generated from `Linglib/Data/Examples/PoesioEtAl2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace PoesioEtAl2004.Examples`.
-/

namespace PoesioEtAl2004.Examples

open Data.Examples

def ex5 : LinguisticExample :=
  { id := "poesioetal2004_ex5"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John walked toward the house. The door was open."
    discourseSegments := ["John walked toward the house.", "The door was open."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("parameter", "realization"), ("section", "2.4.2")]
    comment := "The house is realized in the second utterance only indirectly, by the associative reference the door."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7 : LinguisticExample :=
  { id := "poesioetal2004_ex7"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You should not use PRODUCT-Z if you are pregnant or breast-feeding. Whilst you are receiving PRODUCT-Z ..."
    discourseSegments := ["You should not use PRODUCT-Z", "if you are pregnant or breast-feeding.", "Whilst you are receiving PRODUCT-Z ..."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("parameter", "cfFilter"), ("parameter", "previousUtterance"), ("section", "2.4.2")]
    comment := "Neither the second nor the third utterance has a CB unless the second-person pronoun introduces a CF; treating the if-clause as embedded makes the first utterance the previous utterance of the third."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex9 : LinguisticExample :=
  { id := "poesioetal2004_ex9"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These \"egg vases\" are of exceptional quality: basketwork bases support egg-shaped bodies and bundles of straw form the handles, while small eggs resting in straw nests serve as the finial for each lid. Each vase is decorated with inlaid decoration: ..."
    discourseSegments := ["These \"egg vases\" are of exceptional quality:", "basketwork bases support egg-shaped bodies", "and bundles of straw form the handles,", "while small eggs resting in straw nests serve as the finial for each lid.", "Each vase is decorated with inlaid decoration: ..."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("parameter", "utterance"), ("parameter", "realization"), ("section", "4.1.1")]
    comment := "With finite clauses as utterances only the last clause refers to the egg vases; identifying utterances with sentences or allowing indirect realization removes the Strong Constraint 1 violations."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10 : LinguisticExample :=
  { id := "poesioetal2004_ex10"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The drawing of the corner cupboard, or more probably an engraving of it, must have caught Branicki's attention. Dubois was commissioned through a Warsaw dealer to construct the cabinet for the Polish aristocrat."
    discourseSegments := ["The drawing of the corner cupboard, or more probably an engraving of it, must have caught Branicki's attention.", "Dubois was commissioned through a Warsaw dealer to construct the cabinet for the Polish aristocrat."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("parameter", "rank"), ("section", "4.1.1")]
    comment := "The corner cupboard (np-compl) and Branicki (gen) tie under grammatical-function ranking and are both realized in the next utterance, so both are its CB."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex14 : LinguisticExample :=
  { id := "poesioetal2004_ex14"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John woke up when Bill rang the door. He had forgotten the appointment."
    discourseSegments := ["John woke up", "when Bill rang the door.", "He had forgotten the appointment."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("parameter", "previousUtterance"), ("section", "4.2.5")]
    comment := "Kameyama-style the previous utterance of the third clause is the when-clause; Suri and McCoy-style it is the first clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex16 : LinguisticExample :=
  { id := "poesioetal2004_ex16"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do not use scissors as you may damage the patch inside. Take out the patch."
    discourseSegments := ["Do not use scissors", "as you may damage the patch inside.", "Take out the patch."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("parameter", "previousUtterance"), ("section", "4.2.5")]
    comment := "The adjunct clause introduces the patch, so treating it as embedded loses the CB of the third clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex23 : LinguisticExample :=
  { id := "poesioetal2004_ex23"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This leaflet is a summary of the important information about Product A. If you have any questions or are not sure about anything to do with your treatment, ask your doctor or your pharmacist."
    discourseSegments := ["This leaflet is a summary of the important information about Product A.", "If you have any questions or are not sure about anything to do with your treatment,", "ask your doctor or your pharmacist."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2.2")]
    comment := "Successive utterances mention no common entity; the connection is made by the connectives."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex5, ex7, ex9, ex10, ex14, ex16, ex23]

end PoesioEtAl2004.Examples
