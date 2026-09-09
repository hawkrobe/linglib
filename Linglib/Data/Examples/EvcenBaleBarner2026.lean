import Linglib.Data.Examples.Schema

/-!
# `EvcenBaleBarner2026` — typed example data

Auto-generated from `Linglib/Data/Examples/EvcenBaleBarner2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace EvcenBaleBarner2026.Examples`.
-/

namespace EvcenBaleBarner2026.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "evcenbalebarner2026_1a"
    source := ⟨"evcen-bale-barner-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary mowed the lawn."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary mowed the lawn."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Where Peter, Paul and Mary might be mowing, the assertion implies that Peter and Paul did not: a quantity implicature over ad hoc alternatives."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1b : LinguisticExample :=
  { id := "evcenbalebarner2026_1b"
    source := ⟨"evcen-bale-barner-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter mowed the lawn."
    discourseSegments := []
    glossedTokens := []
    translation := "Peter mowed the lawn."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "An ad hoc alternative to (1a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1c : LinguisticExample :=
  { id := "evcenbalebarner2026_1c"
    source := ⟨"evcen-bale-barner-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Paul mowed the lawn."
    discourseSegments := []
    glossedTokens := []
    translation := "Paul mowed the lawn."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "An ad hoc alternative to (1a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2a : LinguisticExample :=
  { id := "evcenbalebarner2026_2a"
    source := ⟨"evcen-bale-barner-2026", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary mows the lawn, she will receive $5."
    discourseSegments := []
    glossedTokens := []
    translation := "If Mary mows the lawn, she will receive $5."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Perfected to only if, on von Fintel's account, by excluding the conditionals with the alternative antecedents (2b) and (2c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2b : LinguisticExample :=
  { id := "evcenbalebarner2026_2b"
    source := ⟨"evcen-bale-barner-2026", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary does the dishes, she will receive $5."
    discourseSegments := []
    glossedTokens := []
    translation := "If Mary does the dishes, she will receive $5."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2c : LinguisticExample :=
  { id := "evcenbalebarner2026_2c"
    source := ⟨"evcen-bale-barner-2026", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary cleans the pool, she will receive $5."
    discourseSegments := []
    glossedTokens := []
    translation := "If Mary cleans the pool, she will receive $5."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3a : LinguisticExample :=
  { id := "evcenbalebarner2026_3a"
    source := ⟨"evcen-bale-barner-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who mowed the lawn?"
    discourseSegments := []
    glossedTokens := []
    translation := "Who mowed the lawn?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "As an answer to this question (1a) implies that neither Peter nor Paul mowed; (1b) and (1c) are answers to it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3b : LinguisticExample :=
  { id := "evcenbalebarner2026_3b"
    source := ⟨"evcen-bale-barner-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did Mary do after doing the dishes?"
    discourseSegments := []
    glossedTokens := []
    translation := "What did Mary do after doing the dishes?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "As an answer to this question (1a) says nothing about Peter or Paul."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3c : LinguisticExample :=
  { id := "evcenbalebarner2026_3c"
    source := ⟨"evcen-bale-barner-2026", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did Mary mow the lawn?"
    discourseSegments := []
    glossedTokens := []
    translation := "Did Mary mow the lawn?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_antecedent : LinguisticExample :=
  { id := "evcenbalebarner2026_exp1_antecedent"
    source := ⟨"evcen-bale-barner-2026", "Experiment 1, antecedent-focused"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue button, it will play a dog barking."
    discourseSegments := []
    glossedTokens := []
    translation := "If you press the blue button, it will play a dog barking."
    context := "Mary has tested all three buttons. Which of these buttons will play a dog sound?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("qud", "antecedentFocused"), ("tested", "all"), ("response", "no")]
    comment := "Perfection rate 0.65 (SE 0.10); the follow-ups with 'what buttons' and 'which buttons' gave 0.86 and 0.77."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_consequent : LinguisticExample :=
  { id := "evcenbalebarner2026_exp1_consequent"
    source := ⟨"evcen-bale-barner-2026", "Experiment 1, consequent-focused"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue button, it will play a dog barking."
    discourseSegments := []
    glossedTokens := []
    translation := "If you press the blue button, it will play a dog barking."
    context := "Mary has tested all three buttons. What will happen if I press the blue button?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("qud", "consequentFocused"), ("tested", "all"), ("response", "cantTell")]
    comment := "Perfection rate 0.22 (SE 0.10)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_neutral : LinguisticExample :=
  { id := "evcenbalebarner2026_exp1_neutral"
    source := ⟨"evcen-bale-barner-2026", "Experiment 1, neutral"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue button, it will play a dog barking."
    discourseSegments := []
    glossedTokens := []
    translation := "If you press the blue button, it will play a dog barking."
    context := "Mary has tested all three buttons. What will happen if I press the buttons?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("qud", "neutral"), ("tested", "all"), ("response", "cantTell")]
    comment := "Perfection rate 0.29 (SE 0.11), not different from the consequent-focused condition."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp3_full : LinguisticExample :=
  { id := "evcenbalebarner2026_exp3_full"
    source := ⟨"evcen-bale-barner-2026", "Experiment 3, full knowledge"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue button, it will play a dog barking."
    discourseSegments := []
    glossedTokens := []
    translation := "If you press the blue button, it will play a dog barking."
    context := "Mary has tested all three buttons. Which of these buttons will play a dog sound?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("qud", "antecedentFocused"), ("tested", "all"), ("response", "no")]
    comment := "Perfection rate 0.72 (SE 0.13)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp3_partial : LinguisticExample :=
  { id := "evcenbalebarner2026_exp3_partial"
    source := ⟨"evcen-bale-barner-2026", "Experiment 3, partial knowledge"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue button, it will play a dog barking."
    discourseSegments := []
    glossedTokens := []
    translation := "If you press the blue button, it will play a dog barking."
    context := "Mary has tested the red and blue buttons only. Which of these buttons will play a dog sound?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("qud", "antecedentFocused"), ("tested", "two"), ("response", "cantTell")]
    comment := "Perfection rate 0.21 (SE 0.12)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp2_optimal : LinguisticExample :=
  { id := "evcenbalebarner2026_exp2_optimal"
    source := ⟨"evcen-bale-barner-2026", "Experiment 2, optimally informative"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the triangles, it will play a dog barking."
    discourseSegments := []
    glossedTokens := []
    translation := "If you press the triangles, it will play a dog barking."
    context := "Which of these shapes, triangles or squares, will play a dog barking?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("answerType", "optimallyInformative"), ("response", "no")]
    comment := "Asked whether the squares play the same sound: perfection rate 0.92 (SE 0.09)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp2_overly : LinguisticExample :=
  { id := "evcenbalebarner2026_exp2_overly"
    source := ⟨"evcen-bale-barner-2026", "Experiment 2, overly informative"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue square, it will play a dog barking."
    discourseSegments := []
    glossedTokens := []
    translation := "If you press the blue square, it will play a dog barking."
    context := "Which of these shapes, triangles or squares, will play a dog barking?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("answerType", "overlyInformative"), ("response", "no")]
    comment := "Asked whether the red square plays the same sound: perfection rate 0.84 (SE 0.07), not reliably different (p = .16)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_1b, ex_1c, ex_2a, ex_2b, ex_2c, ex_3a, ex_3b, ex_3c, exp1_antecedent, exp1_consequent, exp1_neutral, exp3_full, exp3_partial, exp2_optimal, exp2_overly]

end EvcenBaleBarner2026.Examples
