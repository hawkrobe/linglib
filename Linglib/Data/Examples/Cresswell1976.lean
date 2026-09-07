import Linglib.Data.Examples.Schema

/-!
# `Cresswell1976` — typed example data

Auto-generated from `Linglib/Data/Examples/Cresswell1976.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Cresswell1976.Examples`.
-/

namespace Cresswell1976.Examples

open Data.Examples

def ex_13 : LinguisticExample :=
  { id := "cresswell1976_13"
    source := ⟨"cresswell-1976", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill is taller than Arabella."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill is taller than Arabella."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "distance"), ("rightScale", "distance")]
    comment := "A comparison of two degrees of height, both on the scale of spatial distances."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15 : LinguisticExample :=
  { id := "cresswell1976_15"
    source := ⟨"cresswell-1976", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill is a taller man than Ophidia is a long snake."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill is a taller man than Ophidia is a long snake."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "distance"), ("rightScale", "distance")]
    comment := "Tall and long both measure spatial distance, so the two degrees lie on one scale."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "cresswell1976_23"
    source := ⟨"cresswell-1976", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill is a taller man than Tom is a clever man."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill is a taller man than Tom is a clever man."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "distance"), ("rightScale", "cleverness")]
    comment := "Grammatical but semantically anomalous: the degrees of height and of cleverness lie on different scales."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_35 : LinguisticExample :=
  { id := "cresswell1976_35"
    source := ⟨"cresswell-1976", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill is taller than six feet."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill is taller than six feet."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "distance"), ("rightScale", "distance")]
    comment := "Six feet names a degree on the upward scale of spatial distances."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_37 : LinguisticExample :=
  { id := "cresswell1976_37"
    source := ⟨"cresswell-1976", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill is six feet tall."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill is six feet tall."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "The degree name six feet as the degree argument of tall."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_39 : LinguisticExample :=
  { id := "cresswell1976_39"
    source := ⟨"cresswell-1976", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill is six feet short."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill is six feet short."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Not a comparative: six feet names the degree read upward, and the degree argument of short is read downward, so the degree lies outside the domain of short."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_41 : LinguisticExample :=
  { id := "cresswell1976_41"
    source := ⟨"cresswell-1976", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More water ebbs than mud flows."
    discourseSegments := []
    glossedTokens := []
    translation := "More water ebbs than mud flows."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "volume"), ("rightScale", "volume")]
    comment := "The degree of the totality of ebbing water exceeds that of flowing mud, both volumes."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_50 : LinguisticExample :=
  { id := "cresswell1976_50"
    source := ⟨"cresswell-1976", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Arabella is more beautiful than Tom is clever."
    discourseSegments := []
    glossedTokens := []
    translation := "Arabella is more beautiful than Tom is clever."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "beauty"), ("rightScale", "cleverness")]
    comment := "Listed without an asterisk as an instance of the single meaning of more, although beauty and cleverness are distinct scales, as in the starred (65)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_52 : LinguisticExample :=
  { id := "cresswell1976_52"
    source := ⟨"cresswell-1976", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More men walk than birds fly."
    discourseSegments := []
    glossedTokens := []
    translation := "More men walk than birds fly."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "number"), ("rightScale", "number")]
    comment := "Pluralization supplies the numerical scale: the number of walking men exceeds the number of flying birds."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_56 : LinguisticExample :=
  { id := "cresswell1976_56"
    source := ⟨"cresswell-1976", "(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All men walk."
    discourseSegments := []
    glossedTokens := []
    translation := "All men walk."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Synonymous with (57) although all combines with the plural and every with the singular."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_57 : LinguisticExample :=
  { id := "cresswell1976_57"
    source := ⟨"cresswell-1976", "(57)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man walks."
    discourseSegments := []
    glossedTokens := []
    translation := "Every man walks."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Synonymous with (56)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_62 : LinguisticExample :=
  { id := "cresswell1976_62"
    source := ⟨"cresswell-1976", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Arabella is more beautiful than Clarissa."
    discourseSegments := []
    glossedTokens := []
    translation := "Arabella is more beautiful than Clarissa."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "beauty"), ("rightScale", "beauty")]
    comment := "The scale of beauty has no unit; its degrees are the classes of the comparison relation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_65 : LinguisticExample :=
  { id := "cresswell1976_65"
    source := ⟨"cresswell-1976", "(65)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill is taller than Arabella is beautiful."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill is taller than Arabella is beautiful."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "distance"), ("rightScale", "beauty")]
    comment := "Anomalous: Bill's tallness and Arabella's beauty are represented on different scales."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_66 : LinguisticExample :=
  { id := "cresswell1976_66"
    source := ⟨"cresswell-1976", "(66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I am older than you are wise."
    discourseSegments := []
    glossedTokens := []
    translation := "I am older than you are wise."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Prima facie anomalous but said; the speaker uses the words as if their meanings produced a scale common to age and wisdom."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_69 : LinguisticExample :=
  { id := "cresswell1976_69"
    source := ⟨"cresswell-1976", "(69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The meeting was longer than the road."
    discourseSegments := []
    glossedTokens := []
    translation := "The meeting was longer than the road."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "time"), ("rightScale", "distance")]
    comment := "Long measures an event on the temporal scale and a physical object on the spatial one."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_70 : LinguisticExample :=
  { id := "cresswell1976_70"
    source := ⟨"cresswell-1976", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill had been a smoker he would be shorter than he is."
    discourseSegments := []
    glossedTokens := []
    translation := "If Bill had been a smoker he would be shorter than he is."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "distanceDownward"), ("rightScale", "distanceDownward")]
    comment := "A trans-world comparison: Bill's height in the nearest world where he smokes against his height in the actual world."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def fn10_iii : LinguisticExample :=
  { id := "cresswell1976_fn10_iii"
    source := ⟨"cresswell-1976", "footnote 10 (iii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill is taller than Arabella or Clarissa."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill is taller than Arabella or Clarissa."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("leftScale", "distance"), ("rightScale", "distance")]
    comment := "Means, at least usually, that Bill is taller than Arabella and taller than Clarissa, not the disjunction of the two comparisons."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_13, ex_15, ex_23, ex_35, ex_37, ex_39, ex_41, ex_50, ex_52, ex_56, ex_57, ex_62, ex_65, ex_66, ex_69, ex_70, fn10_iii]

end Cresswell1976.Examples
