import Linglib.Data.Examples.Schema

/-!
# `FoxSpector2018` — typed example data

Auto-generated from `Linglib/Data/Examples/FoxSpector2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FoxSpector2018.Examples`.
-/

namespace FoxSpector2018.Examples

open Data.Examples

def ex14a : LinguisticExample :=
  { id := "foxspector2018_ex14a"
    source := ⟨"hurford-1974", "Hurford's Constraint"⟩
    reportedIn := some ⟨"fox-spector-2018", "(14a)"⟩
    language := "stan1293"
    primaryText := "John was born in France or Paris."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "no"), ("order", "canonical"), ("distant", "no"), ("de", "0")]
    comment := "The second disjunct entails the first and no scalar alternative lets exhaustification break the entailment."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex14b : LinguisticExample :=
  { id := "foxspector2018_ex14b"
    source := ⟨"fox-spector-2018", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have a dog or a German Shepherd."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "no"), ("order", "canonical"), ("distant", "no"), ("de", "0")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex16a : LinguisticExample :=
  { id := "foxspector2018_ex16a"
    source := ⟨"hurford-1974", "(16a)"⟩
    reportedIn := some ⟨"fox-spector-2018", "(16a)"⟩
    language := "stan1293"
    primaryText := "John talked to Mary or Sue or both."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "0")]
    comment := "Exhaustifying the first disjunct excludes 'both', so the second no longer entails it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex16b : LinguisticExample :=
  { id := "foxspector2018_ex16b"
    source := ⟨"fox-spector-2018", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did some or all of the homework."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "0")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex16c : LinguisticExample :=
  { id := "foxspector2018_ex16c"
    source := ⟨"gazdar-1979", "(16c)"⟩
    reportedIn := some ⟨"fox-spector-2018", "(16c)"⟩
    language := "stan1293"
    primaryText := "John read three books or more."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "0")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex18a : LinguisticExample :=
  { id := "foxspector2018_ex18a"
    source := ⟨"fox-spector-2018", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has three or six children."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "yes"), ("de", "0")]
    comment := "Exhaustification of the first disjunct has a detectable effect: four or five children falsify it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex18b : LinguisticExample :=
  { id := "foxspector2018_ex18b"
    source := ⟨"fox-spector-2018", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The water is warm or absolutely boiling."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "yes"), ("de", "0")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex12b : LinguisticExample :=
  { id := "foxspector2018_ex12b"
    source := ⟨"singh-2008", "Singh's Asymmetry"⟩
    reportedIn := some ⟨"fox-spector-2018", "(12b)"⟩
    language := "stan1293"
    primaryText := "John talked to both Mary and Sue, or to Mary or Sue."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "reverse"), ("distant", "no"), ("de", "0")]
    comment := "Exhaustifying the final disjunct is incrementally vacuous."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46 : LinguisticExample :=
  { id := "foxspector2018_ex46"
    source := ⟨"fox-spector-2018", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The water is absolutely boiling or somewhat warm."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "reverse"), ("distant", "yes"), ("de", "0")]
    comment := "A reverse Hurford disjunction of distant entailing disjuncts: exhaustification is not vacuous."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10a : LinguisticExample :=
  { id := "foxspector2018_ex10a"
    source := ⟨"gajewski-sharvit-2012", "Hurford under negation"⟩
    reportedIn := some ⟨"fox-spector-2018", "(10a)"⟩
    language := "stan1293"
    primaryText := "John didn't talk to Mary or Sue, or both."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "1")]
    comment := "Under one downward-entailing operator exhaustification is incrementally weakening."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex65a : LinguisticExample :=
  { id := "foxspector2018_ex65a"
    source := ⟨"fox-spector-2018", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't hand in the first or second assignment or both."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "1")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex65b : LinguisticExample :=
  { id := "foxspector2018_ex65b"
    source := ⟨"fox-spector-2018", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who didn't hand in the first or second assignment or both failed the class."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "2")]
    comment := "Two downward-entailing operators make the context upward-entailing again."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex66a : LinguisticExample :=
  { id := "foxspector2018_ex66a"
    source := ⟨"fox-spector-2018", "(66a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I would go to the movies without John or Bill or both."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "1")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex66b : LinguisticExample :=
  { id := "foxspector2018_ex66b"
    source := ⟨"fox-spector-2018", "(66b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wouldn't go to the movies without John or Bill or both."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "2")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex14a, ex14b, ex16a, ex16b, ex16c, ex18a, ex18b, ex12b, ex46, ex10a, ex65a, ex65b, ex66a, ex66b]

end FoxSpector2018.Examples
