module

public import Linglib.Data.Examples.Schema

/-!
# `TieuEtAl2020` — typed example data

Auto-generated from `Linglib/Data/Examples/TieuEtAl2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TieuEtAl2020.Examples`.
-/

@[expose] public section

namespace TieuEtAl2020.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "tieuetal2020_1a"
    source := ⟨"tieu-etal-2020", "(1a), (13), (21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed giraffes."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("more than one giraffe", .acceptable)]
    paperFeatures := [("polarity", "positive")]
    comment := "Conveys that Emily fed more than one giraffe, the multiplicity inference."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2a : LinguisticExample :=
  { id := "tieuetal2020_2a"
    source := ⟨"tieu-etal-2020", "(2a), (16), (23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not more than one giraffe", .unacceptable), ("not a single giraffe", .acceptable)]
    paperFeatures := [("polarity", "negative")]
    comment := "Paraphrased as the negation of the singular, that Emily fed no giraffe, rather than as not more than one."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3a : LinguisticExample :=
  { id := "tieuetal2020_3a"
    source := ⟨"tieu-etal-2020", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If there are books on Stephen's desk, Robin should lock the door."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "downward")]
    comment := "In the antecedent of a conditional the plural is equivalent to the singular."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4a : LinguisticExample :=
  { id := "tieuetal2020_4a"
    source := ⟨"tieu-etal-2020", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Are there books on Stephen's desk?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "downward")]
    comment := "In a question the plural is equivalent to the singular."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "tieuetal2020_8"
    source := ⟨"tieu-etal-2020", "(8), (18), (26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes, because she fed only one!"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative")]
    comment := "The marked reading with stress on the plural morpheme: the weak reading of the ambiguity account, a local implicature, or an undefined sentence used as if true."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "tieuetal2020_14"
    source := ⟨"tieu-etal-2020", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed exactly one giraffe."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive")]
    comment := "The more informative alternative to (13) whose denial is the multiplicity inference."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17 : LinguisticExample :=
  { id := "tieuetal2020_17"
    source := ⟨"tieu-etal-2020", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed exactly one giraffe."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative")]
    comment := "Weaker than (16), so no implicature arises under negation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_27a : LinguisticExample :=
  { id := "tieuetal2020_27a"
    source := ⟨"tieu-etal-2020", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed giraffes."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Emily fed exactly one giraffe."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("n_acted_on", "one")]
    comment := "In a context where Emily fed only one giraffe: literally true with a false implicature on the implicature approach, false on the ambiguity approach, undefined on the homogeneity approach."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_27b : LinguisticExample :=
  { id := "tieuetal2020_27b"
    source := ⟨"tieu-etal-2020", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Emily fed exactly one giraffe."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("n_acted_on", "one")]
    comment := "In the same context: false on the implicature and ambiguity approaches, undefined on the homogeneity approach."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_29a : LinguisticExample :=
  { id := "tieuetal2020_29a"
    source := ⟨"tieu-etal-2020", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed some of the giraffes."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not all of the giraffes", .acceptable)]
    paperFeatures := [("polarity", "positive")]
    comment := "Children accept it where the stronger (29b) is also true, failing to compute the implicature (29c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_positive : LinguisticExample :=
  { id := "tieuetal2020_exp1_positive"
    source := ⟨"tieu-etal-2020", "(35), Experiment 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed pigs."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Emily is visiting the zoo and feeds exactly one pig."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("polarity", "positive"), ("n_acted_on", "one")]
    comment := "Truth-value judgment after a story in which Emily fed exactly one pig; rejection indicates the multiplicity inference. Adults rejected at a high rate and children at a low rate."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_negative : LinguisticExample :=
  { id := "tieuetal2020_exp1_negative"
    source := ⟨"tieu-etal-2020", "(43), Experiment 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Emily feeds exactly one giraffe."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("polarity", "negative"), ("n_acted_on", "one")]
    comment := "Truth-value judgment after a story in which Emily fed exactly one giraffe; acceptance indicates a local multiplicity reading under negation, which adults gave at a moderate rate and children at a low rate."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp2_si : LinguisticExample :=
  { id := "tieuetal2020_exp2_si"
    source := ⟨"tieu-etal-2020", "(47), Experiment 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lion carried some of the apples!"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Lion carried all of the apples."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("polarity", "positive"), ("inference", "scalar")]
    comment := "Scalar-implicature target after a story in which Lion carried all of the apples; rejection indicates the not-all implicature. Children computed fewer scalar implicatures and fewer multiplicity inferences than adults, and the two rates were correlated within children."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp3_positive_plural : LinguisticExample :=
  { id := "tieuetal2020_exp3_positive_plural"
    source := ⟨"tieu-etal-2020", "(54), Experiment 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Koala bought pears."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Koala bought exactly one pear."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("polarity", "positive"), ("n_acted_on", "one"), ("task", "ternary_reward"), ("preferred_reward", "intermediate")]
    comment := "Ternary judgment with adults after Koala bought exactly one pear: the intermediate reward, literally true but misleading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp3_negative_plural : LinguisticExample :=
  { id := "tieuetal2020_exp3_negative_plural"
    source := ⟨"tieu-etal-2020", "(54), Experiment 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Koala didn't buy pears."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Koala bought exactly one pear."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("polarity", "negative"), ("n_acted_on", "one"), ("task", "ternary_reward"), ("preferred_reward", "minimal")]
    comment := "Ternary judgment with adults after Koala bought exactly one pear: the minimal reward, literally false."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_2a, ex_3a, ex_4a, ex_8, ex_14, ex_17, ex_27a, ex_27b, ex_29a, exp1_positive, exp1_negative, exp2_si, exp3_positive_plural, exp3_negative_plural]

end TieuEtAl2020.Examples
