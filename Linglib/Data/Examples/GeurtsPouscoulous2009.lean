import Linglib.Data.Examples.Schema

/-!
# `GeurtsPouscoulous2009` — typed example data

Auto-generated from `Linglib/Data/Examples/GeurtsPouscoulous2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GeurtsPouscoulous2009.Examples`.
-/

namespace GeurtsPouscoulous2009.Examples

open Data.Examples

def t1_simple : LinguisticExample :=
  { id := "geurtspouscoulous2009_t1_simple"
    source := ⟨"geurts-pouscoulous-2009", "Table 1 ∅"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred heard some of the Verdi operas."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("embedding", "simple"), ("rate1a", "93"), ("rate1b", "94")]
    comment := "Candidate inference: he didn't hear all of them. Experiment 1 sentence; the participants judged whether the candidate inference follows."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def t1_all : LinguisticExample :=
  { id := "geurtspouscoulous2009_t1_all"
    source := ⟨"geurts-pouscoulous-2009", "Table 1 all"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All students heard some of the Verdi operas."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("embedding", "all"), ("rate1a", "27"), ("rate1b", "none")]
    comment := "Candidate inference: none of the students heard them all. Experiment 1 sentence; the participants judged whether the candidate inference follows."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def t1_must : LinguisticExample :=
  { id := "geurtspouscoulous2009_t1_must"
    source := ⟨"geurts-pouscoulous-2009", "Table 1 must"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred has to hear some of the Verdi operas."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("embedding", "must"), ("rate1a", "3"), ("rate1b", "none")]
    comment := "Candidate inference: he isn't allowed to hear all of them. Experiment 1 sentence; the participants judged whether the candidate inference follows."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def t1_think : LinguisticExample :=
  { id := "geurtspouscoulous2009_t1_think"
    source := ⟨"geurts-pouscoulous-2009", "Table 1 think"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Betty thinks Fred heard some of the Verdi operas."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("embedding", "think"), ("rate1a", "50"), ("rate1b", "65")]
    comment := "Candidate inference: she thinks he didn't hear all of them. Experiment 1 sentence; the participants judged whether the candidate inference follows."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def t1_want : LinguisticExample :=
  { id := "geurtspouscoulous2009_t1_want"
    source := ⟨"geurts-pouscoulous-2009", "Table 1 want"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Betty wants Fred to hear some of the Verdi operas."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("embedding", "want"), ("rate1a", "none"), ("rate1b", "32")]
    comment := "Candidate inference: she wants him not to hear all of them. Experiment 1 sentence; the participants judged whether the candidate inference follows."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex24 : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex24"
    source := ⟨"geurts-pouscoulous-2009", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of the B's are in the box on the left."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("embedding", "simple"), ("inferenceRate", "62"), ("verificationRate", "34")]
    comment := "Verification situation: BBBAAA in the left box, CCC in the right; the scalar inference is a positive response in the inference task and a negative one in the verification task."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex26a : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex26a"
    source := ⟨"geurts-pouscoulous-2009", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the squares are connected with some of the circles."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "all"), ("trial", "none"), ("verificationRate", "100"), ("predictedRate", "0"), ("inferenceRate", "46"), ("exp4Yes", "95"), ("exp4No", "5"), ("exp4Both", "0")]
    comment := "Experiment 3 sentence, run in Dutch; the verification situation makes the classical and the local-implicature construal conflict."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex26b : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex26b"
    source := ⟨"geurts-pouscoulous-2009", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is more than one square that is connected with some of the circles."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "moreThanOne"), ("trial", "none"), ("verificationRate", "100"), ("predictedRate", "0"), ("inferenceRate", "62"), ("exp4Yes", "100"), ("exp4No", "0"), ("exp4Both", "0")]
    comment := "Experiment 3 sentence, run in Dutch; the verification situation makes the classical and the local-implicature construal conflict."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex27_a : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex27_a"
    source := ⟨"geurts-pouscoulous-2009", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are exactly two squares that are connected with some of the circles."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "exactlyTwo"), ("trial", "A"), ("verificationRate", "100"), ("predictedRate", "0"), ("inferenceRate", "50"), ("exp4Yes", "86"), ("exp4No", "5"), ("exp4Both", "9")]
    comment := "Experiment 3 sentence, run in Dutch; the verification situation makes the classical and the local-implicature construal conflict. Trial with one square connected with some but not all of the circles and one with all."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex27_b : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex27_b"
    source := ⟨"geurts-pouscoulous-2009", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are exactly two squares that are connected with some of the circles."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "exactlyTwo"), ("trial", "B"), ("verificationRate", "0"), ("predictedRate", "100"), ("inferenceRate", "50"), ("exp4Yes", "9"), ("exp4No", "77"), ("exp4Both", "14")]
    comment := "Experiment 3 sentence, run in Dutch; the verification situation makes the classical and the local-implicature construal conflict. Trial with two squares connected with some but not all of the circles and one with all."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex25a : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex25a"
    source := ⟨"geurts-pouscoulous-2009", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not all the squares are connected with some of the circles."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "notAll"), ("trial", "none"), ("verificationRate", "4"), ("predictedRate", "0"), ("inferenceRate", "58"), ("exp4Yes", "9"), ("exp4No", "86"), ("exp4Both", "5")]
    comment := "Experiment 3 sentence, run in Dutch; the verification situation makes the classical and the local-implicature construal conflict."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex25b : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex25b"
    source := ⟨"geurts-pouscoulous-2009", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There isn't more than one square that is connected with some of the circles."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "notMoreThanOne"), ("trial", "none"), ("verificationRate", "4"), ("predictedRate", "0"), ("inferenceRate", "46"), ("exp4Yes", "9"), ("exp4No", "91"), ("exp4Both", "0")]
    comment := "Experiment 3 sentence, run in Dutch; the verification situation makes the classical and the local-implicature construal conflict."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29a : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex29a"
    source := ⟨"geurts-pouscoulous-2009", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The circles and the squares are connected with each other."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "4"), ("role", "ambiguousControl"), ("exp4Both", "82")]
    comment := "Ambiguous control item of Experiment 4."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29b : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex29b"
    source := ⟨"geurts-pouscoulous-2009", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The green and the orange figures are connected with each other."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "4"), ("role", "ambiguousControl"), ("exp4Both", "73")]
    comment := "Ambiguous control item of Experiment 4."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29c : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex29c"
    source := ⟨"geurts-pouscoulous-2009", "(29c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the figures are orange and green."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "4"), ("role", "ambiguousControl"), ("exp4Both", "59")]
    comment := "Ambiguous control item of Experiment 4."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29d : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex29d"
    source := ⟨"geurts-pouscoulous-2009", "(29d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are green circles and squares."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "4"), ("role", "ambiguousControl"), ("exp4Both", "77")]
    comment := "Ambiguous control item of Experiment 4."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29e : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex29e"
    source := ⟨"geurts-pouscoulous-2009", "(29e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The circles and the squares have the same colour."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "4"), ("role", "ambiguousControl"), ("exp4Both", "59")]
    comment := "Ambiguous control item of Experiment 4."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex31 : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex31"
    source := ⟨"geurts-pouscoulous-2009", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob believes that Anna ate some of the cookies."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "none"), ("embedding", "think")]
    comment := "The global implicature is that Bob does not believe Anna ate all; with Bob opinionated on whether she did, it yields that he believes she did not."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex35 : LinguisticExample :=
  { id := "geurtspouscoulous2009_ex35"
    source := ⟨"geurts-pouscoulous-2009", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the customers shot at some of the salesmen."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "none"), ("embedding", "all")]
    comment := "The global implicature is that not all customers shot at all salesmen; the local construal needs the implausible uniformity assumption that either all or none did."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [t1_simple, t1_all, t1_must, t1_think, t1_want, ex24, ex26a, ex26b, ex27_a, ex27_b, ex25a, ex25b, ex29a, ex29b, ex29c, ex29d, ex29e, ex31, ex35]

end GeurtsPouscoulous2009.Examples
