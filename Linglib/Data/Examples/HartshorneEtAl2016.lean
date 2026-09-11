import Linglib.Data.Examples.Schema

/-!
# `HartshorneEtAl2016` — typed example data

Auto-generated from `Linglib/Data/Examples/HartshorneEtAl2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HartshorneEtAl2016.Examples`.
-/

namespace HartshorneEtAl2016.Examples

open Data.Examples

def fear : LinguisticExample :=
  { id := "hartshorneetal2016_fear"
    source := ⟨"hartshorne-etal-2016", "§1.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Agnes feared Bartholomew."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("phenomenon", "fearType"), ("verbType", "fear"), ("subject", "experiencer")]
    comment := "A fear-type verb: the experiencer is the subject, the stimulus the object."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def frighten : LinguisticExample :=
  { id := "hartshorneetal2016_frighten"
    source := ⟨"hartshorne-etal-2016", "§1.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Agnes frightened Bartholomew."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("phenomenon", "frightenType"), ("verbType", "frighten"), ("subject", "stimulus")]
    comment := "A frighten-type verb: the stimulus is the subject, the experiencer the object."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def episode : LinguisticExample :=
  { id := "hartshorneetal2016_episode"
    source := ⟨"hartshorne-etal-2016", "§2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bats swooped out of the cave and frightened Agnes."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("The bats swooped out of the cave and Agnes feared them.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "frightenType"), ("verbType", "frighten")]
    comment := "A frighten-type verb describes a specific instance in which an emotional state occurs."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def stageLevel : LinguisticExample :=
  { id := "hartshorneetal2016_stageLevel"
    source := ⟨"hartshorne-etal-2016", "§1.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Agnes concerned Bartholomew yesterday in the kitchen."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Agnes feared Bartholomew yesterday in the kitchen.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "1.2"), ("phenomenon", "frightenType"), ("verbType", "frighten")]
    comment := "The paper's rendering of the observation that frighten-type verbs describe states bound to a time and place, and fear-type verbs do not."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1 : LinguisticExample :=
  { id := "hartshorneetal2016_exp1"
    source := ⟨"hartshorne-etal-2016", "§2.1.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sally frightened Mary."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1.1"), ("phenomenon", "durationRating"), ("experiment", "1")]
    comment := "Experiment 1 stimulus shape: how long is the mental state likely to have lasted (seconds to years)?"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp2 : LinguisticExample :=
  { id := "hartshorneetal2016_exp2"
    source := ⟨"hartshorne-etal-2016", "§2.2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary frightened Sally."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.1"), ("phenomenon", "causationJudgment"), ("experiment", "2")]
    comment := "Experiment 2 stimulus shape: in a court case in which causing an emotion is illegal, who if anyone is guilty?"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2a : LinguisticExample :=
  { id := "hartshorneetal2016_2a"
    source := ⟨"hartshorne-etal-2016", "(2a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-wa koomori-o kowagat-ta."
    discourseSegments := []
    glossedTokens := [("Taro-wa", "Taro-TOPIC"), ("koomori-o", "bat-ACC"), ("kowagat-ta", "fear-PAST")]
    translation := "Taro feared bats."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("phenomenon", "fearType"), ("verbType", "fear")]
    comment := "Japanese fear-type verb, unaffixed."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_2b : LinguisticExample :=
  { id := "hartshorneetal2016_2b"
    source := ⟨"hartshorne-etal-2016", "(2b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Koomori-wa Taro-o kowagar-ase-ta."
    discourseSegments := []
    glossedTokens := [("Koomori-wa", "bat-TOPIC"), ("Taro-o", "Taro-ACC"), ("kowagar-ase-ta", "fear-CAUS-PAST")]
    translation := "Bats frightened Taro."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("phenomenon", "frightenType"), ("verbType", "frighten"), ("causativeAffix", "sase")]
    comment := "Japanese frighten-type verb: the causative affix -(s)ase- on the fear-type stem."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_3a : LinguisticExample :=
  { id := "hartshorneetal2016_3a"
    source := ⟨"hartshorne-etal-2016", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ken douyos the unexpected exam."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1.1"), ("phenomenon", "novelVerb"), ("experiment", "5"), ("syntax", "fear")]
    comment := "Experiment 5: the novel verb *douyo* 'uneasiness' with fear-type, experiencer-subject syntax."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3b : LinguisticExample :=
  { id := "hartshorneetal2016_3b"
    source := ⟨"hartshorne-etal-2016", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The unexpected exam douyos Ken."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1.1"), ("phenomenon", "novelVerb"), ("experiment", "5"), ("syntax", "frighten")]
    comment := "Experiment 5: the novel verb *douyo* with frighten-type, experiencer-object syntax."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "hartshorneetal2016_5"
    source := ⟨"hartshorne-etal-2016", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some people wixter each other. Do you know what wixter is? Wixter is when you want something that somebody else has. Or maybe you think somebody else is so cool you wish you were just like them. That means you feel wixter."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "novelVerb"), ("experiment", "9"), ("semanticType", "attitude")]
    comment := "Experiment 9: the habitual-attitude definition of a novel verb, based on envy."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "hartshorneetal2016_6"
    source := ⟨"hartshorne-etal-2016", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some people gorfin each other. Do you know what gorfin is? You feel gorfin when you see something really, really gross. Or if you had to hold something really slimy, you might feel gorfin."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "novelVerb"), ("experiment", "9"), ("semanticType", "episode")]
    comment := "Experiment 9: the emotional-episode definition of a novel verb, based on disgust."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp9q : LinguisticExample :=
  { id := "hartshorneetal2016_exp9q"
    source := ⟨"hartshorne-etal-2016", "§4.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did Bear wixter?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "novelVerb"), ("experiment", "9")]
    comment := "Experiment 9 test question: a fear-type linking picks the character Bear had the attitude about, a frighten-type linking the character Bear affected."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "hartshorneetal2016_7"
    source := ⟨"hartshorne-etal-2016", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The newspaper frightened John about the housing bubble."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.4.3"), ("phenomenon", "frightenType"), ("verbType", "frighten")]
    comment := "The unattested target of a caused emotional episode, which the Fig. 11 structures do not exclude."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [fear, frighten, episode, stageLevel, exp1, exp2, ex_2a, ex_2b, ex_3a, ex_3b, ex_5, ex_6, exp9q, ex_7]

end HartshorneEtAl2016.Examples
