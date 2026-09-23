module

public import Linglib.Data.Examples.Schema

/-!
# `Ross1967` — typed example data

Auto-generated from `Linglib/Data/Examples/Ross1967.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ross1967.Examples`.
-/

@[expose] public section

namespace Ross1967.Examples

open Data.Examples

def ex4_15a : LinguisticExample :=
  { id := "ross1967_ex4_15a"
    source := ⟨"ross-1967", "(4.15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who does Phineas know a girl who is jealous of?"
    discourseSegments := []
    glossedTokens := []
    translation := "Who does Phineas know a girl who is jealous of?"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "question"), ("constraint", "CNPC")]
    comment := "Questioning out of a relative clause on a lexically headed NP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_18a : LinguisticExample :=
  { id := "ross1967_ex4_18a"
    source := ⟨"ross-1967", "(4.18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The hat which I believed the claim that Otto was wearing is red."
    discourseSegments := []
    glossedTokens := []
    translation := "The hat which I believed the claim that Otto was wearing is red."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization"), ("constraint", "CNPC")]
    comment := "Relativization out of a noun complement clause under the lexical head noun claim."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_18b : LinguisticExample :=
  { id := "ross1967_ex4_18b"
    source := ⟨"ross-1967", "(4.18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The hat which I believed that Otto was wearing is red."
    discourseSegments := []
    glossedTokens := []
    translation := "The hat which I believed that Otto was wearing is red."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization")]
    comment := "The minimal pair of (4.18a): the complement clause is not dominated by a lexically headed NP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2_18 : LinguisticExample :=
  { id := "ross1967_ex2_18"
    source := ⟨"ross-1967", "(2.18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What sofa will he put the chair between some table and?"
    discourseSegments := []
    glossedTokens := []
    translation := "What sofa will he put the chair between some table and?"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "question"), ("constraint", "CSC")]
    comment := "Questioning a conjunct."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_82a : LinguisticExample :=
  { id := "ross1967_ex4_82a"
    source := ⟨"ross-1967", "(4.82a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lute which Henry plays and sings madrigals is warped."
    discourseSegments := []
    glossedTokens := []
    translation := "The lute which Henry plays and sings madrigals is warped."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization"), ("constraint", "CSC")]
    comment := "Relativization out of a conjoined VP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_82d : LinguisticExample :=
  { id := "ross1967_ex4_82d"
    source := ⟨"ross-1967", "(4.82d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which trombone did the nurse polish and the plumber computed my tax?"
    discourseSegments := []
    glossedTokens := []
    translation := "Which trombone did the nurse polish and the plumber computed my tax?"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "question"), ("constraint", "CSC")]
    comment := "Questioning out of a conjoined S."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_184a : LinguisticExample :=
  { id := "ross1967_ex4_184a"
    source := ⟨"ross-1967", "(4.184a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boy whose guardian's employer we elected president ratted on us."
    discourseSegments := []
    glossedTokens := []
    translation := "The boy whose guardian's employer we elected president ratted on us."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization")]
    comment := "Relativization of the largest NP, the pied-piping output the Left Branch Condition leaves."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_184b : LinguisticExample :=
  { id := "ross1967_ex4_184b"
    source := ⟨"ross-1967", "(4.184b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boy whose guardian's we elected employer president ratted on us."
    discourseSegments := []
    glossedTokens := []
    translation := "The boy whose guardian's we elected employer president ratted on us."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization"), ("constraint", "LBC")]
    comment := "Relativization of the possessor NP on the left branch of the object NP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_184c : LinguisticExample :=
  { id := "ross1967_ex4_184c"
    source := ⟨"ross-1967", "(4.184c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boy whose we elected guardian's employer president ratted on us."
    discourseSegments := []
    glossedTokens := []
    translation := "The boy whose we elected guardian's employer president ratted on us."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization"), ("constraint", "LBC")]
    comment := "Relativization of the lowest possessor NP, on the left branch of the possessor NP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_251a : LinguisticExample :=
  { id := "ross1967_ex4_251a"
    source := ⟨"ross-1967", "(4.251a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The teacher who the reporters expected that the principal would fire is a crusty old battleax."
    discourseSegments := []
    glossedTokens := []
    translation := "The teacher who the reporters expected that the principal would fire is a crusty old battleax."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization")]
    comment := "Relativization out of an object that-clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_251b : LinguisticExample :=
  { id := "ross1967_ex4_251b"
    source := ⟨"ross-1967", "(4.251b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The teacher who that the principal would fire was expected by the reporters is a crusty old battleax."
    discourseSegments := []
    glossedTokens := []
    translation := "The teacher who that the principal would fire was expected by the reporters is a crusty old battleax."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization"), ("constraint", "SSC")]
    comment := "Relativization out of the that-clause in subject position, the passive of (4.250a); no lexical head noun is involved."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_251c : LinguisticExample :=
  { id := "ross1967_ex4_251c"
    source := ⟨"ross-1967", "(4.251c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The teacher who it was expected by the reporters that the principal would fire is a crusty old battleax."
    discourseSegments := []
    glossedTokens := []
    translation := "The teacher who it was expected by the reporters that the principal would fire is a crusty old battleax."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization")]
    comment := "Relativization out of the extraposed that-clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_252 : LinguisticExample :=
  { id := "ross1967_ex4_252"
    source := ⟨"ross-1967", "(4.252)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Of which cars were the hoods damaged by the explosion?"
    discourseSegments := []
    glossedTokens := []
    translation := "Of which cars were the hoods damaged by the explosion?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "question")]
    comment := "Questioning a subconstituent of a phrasal, not sentential, subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6_128b : LinguisticExample :=
  { id := "ross1967_ex6_128b"
    source := ⟨"ross-1967", "(6.128b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My father, the man he works with in Boston is going to tell the police that that traffic expert has set that traffic light on the corner of Murk Street far too slow."
    discourseSegments := []
    glossedTokens := []
    translation := "My father, the man he works with in Boston is going to tell the police that that traffic expert has set that traffic light on the corner of Murk Street far too slow."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "leftDislocation"), ("constraint", "CNPC")]
    comment := "Left Dislocation out of a relative clause on a lexically headed NP, leaving a pronoun."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6_135b : LinguisticExample :=
  { id := "ross1967_ex6_135b"
    source := ⟨"ross-1967", "(6.135b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This guitar, I've sung folksongs and accompanied myself on it all my life."
    discourseSegments := []
    glossedTokens := []
    translation := "This guitar, I've sung folksongs and accompanied myself on it all my life."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "leftDislocation"), ("constraint", "CSC")]
    comment := "Left Dislocation out of a conjunct."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6_136 : LinguisticExample :=
  { id := "ross1967_ex6_136"
    source := ⟨"ross-1967", "(6.136)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My father, that he's lived here all his life is well-known to the cops."
    discourseSegments := []
    glossedTokens := []
    translation := "My father, that he's lived here all his life is well-known to the cops."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "leftDislocation"), ("constraint", "SSC")]
    comment := "Left Dislocation out of a sentential subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6_137 : LinguisticExample :=
  { id := "ross1967_ex6_137"
    source := ⟨"ross-1967", "(6.137)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My wife, somebody stole her handbag last night."
    discourseSegments := []
    glossedTokens := []
    translation := "My wife, somebody stole her handbag last night."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "leftDislocation"), ("constraint", "LBC")]
    comment := "Left Dislocation of a possessor on the left branch of an NP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex4_15a, ex4_18a, ex4_18b, ex2_18, ex4_82a, ex4_82d, ex4_184a, ex4_184b, ex4_184c, ex4_251a, ex4_251b, ex4_251c, ex4_252, ex6_128b, ex6_135b, ex6_136, ex6_137]

end Ross1967.Examples
