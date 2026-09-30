module

public import Linglib.Data.Examples.Schema

/-!
# `HartshorneEtAl2016` — typed example data

Auto-generated from `Linglib/Data/Examples/HartshorneEtAl2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HartshorneEtAl2016.Examples`.
-/

@[expose] public section

namespace HartshorneEtAl2016.Examples

open Data.Examples

def fear : LinguisticExample :=
  { id := "hartshorneetal2016_fear"
    source := ⟨"hartshorne-etal-2016", "§1.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Agnes feared Bartholomew."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("phenomenon", "fearType"), ("verbType", "fear"), ("subject", "experiencer")] }

def frighten : LinguisticExample :=
  { id := "hartshorneetal2016_frighten"
    source := ⟨"hartshorne-etal-2016", "§1.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Agnes frightened Bartholomew."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("phenomenon", "frightenType"), ("verbType", "frighten"), ("subject", "stimulus")] }

def episode : LinguisticExample :=
  { id := "hartshorneetal2016_episode"
    source := ⟨"hartshorne-etal-2016", "§2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bats swooped out of the cave and frightened Agnes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The bats swooped out of the cave and Agnes feared them.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "frightenType"), ("verbType", "frighten")] }

def stageLevel : LinguisticExample :=
  { id := "hartshorneetal2016_stageLevel"
    source := ⟨"hartshorne-etal-2016", "§1.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Agnes concerned Bartholomew yesterday in the kitchen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Agnes feared Bartholomew yesterday in the kitchen.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "1.2"), ("phenomenon", "frightenType"), ("verbType", "frighten")] }

def exp1 : LinguisticExample :=
  { id := "hartshorneetal2016_exp1"
    source := ⟨"hartshorne-etal-2016", "§2.1.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sally frightened Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1.1"), ("phenomenon", "durationRating"), ("experiment", "1")] }

def exp2 : LinguisticExample :=
  { id := "hartshorneetal2016_exp2"
    source := ⟨"hartshorne-etal-2016", "§2.2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary frightened Sally."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.1"), ("phenomenon", "causationJudgment"), ("experiment", "2")] }

def ex_2a : LinguisticExample :=
  { id := "hartshorneetal2016_2a"
    source := ⟨"hartshorne-etal-2016", "(2a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-wa koomori-o kowagat-ta."
    glossedTokens := [("Taro-wa", "Taro-TOPIC"), ("koomori-o", "bat-ACC"), ("kowagat-ta", "fear-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("phenomenon", "fearType"), ("verbType", "fear")] }

def ex_2b : LinguisticExample :=
  { id := "hartshorneetal2016_2b"
    source := ⟨"hartshorne-etal-2016", "(2b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Koomori-wa Taro-o kowagar-ase-ta."
    glossedTokens := [("Koomori-wa", "bat-TOPIC"), ("Taro-o", "Taro-ACC"), ("kowagar-ase-ta", "fear-CAUS-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("phenomenon", "frightenType"), ("verbType", "frighten"), ("causativeAffix", "sase")] }

def ex_3a : LinguisticExample :=
  { id := "hartshorneetal2016_3a"
    source := ⟨"hartshorne-etal-2016", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ken douyos the unexpected exam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1.1"), ("phenomenon", "novelVerb"), ("experiment", "5"), ("syntax", "fear")] }

def ex_3b : LinguisticExample :=
  { id := "hartshorneetal2016_3b"
    source := ⟨"hartshorne-etal-2016", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The unexpected exam douyos Ken."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1.1"), ("phenomenon", "novelVerb"), ("experiment", "5"), ("syntax", "frighten")] }

def ex_5 : LinguisticExample :=
  { id := "hartshorneetal2016_5"
    source := ⟨"hartshorne-etal-2016", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some people wixter each other. Do you know what wixter is? Wixter is when you want something that somebody else has. Or maybe you think somebody else is so cool you wish you were just like them. That means you feel wixter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "novelVerb"), ("experiment", "9"), ("semanticType", "attitude")] }

def ex_6 : LinguisticExample :=
  { id := "hartshorneetal2016_6"
    source := ⟨"hartshorne-etal-2016", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some people gorfin each other. Do you know what gorfin is? You feel gorfin when you see something really, really gross. Or if you had to hold something really slimy, you might feel gorfin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "novelVerb"), ("experiment", "9"), ("semanticType", "episode")] }

def exp9q : LinguisticExample :=
  { id := "hartshorneetal2016_exp9q"
    source := ⟨"hartshorne-etal-2016", "§4.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did Bear wixter?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "novelVerb"), ("experiment", "9")] }

def ex_7 : LinguisticExample :=
  { id := "hartshorneetal2016_7"
    source := ⟨"hartshorne-etal-2016", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The newspaper frightened John about the housing bubble."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.4.3"), ("phenomenon", "frightenType"), ("verbType", "frighten")] }

def all : List LinguisticExample := [fear, frighten, episode, stageLevel, exp1, exp2, ex_2a, ex_2b, ex_3a, ex_3b, ex_5, ex_6, exp9q, ex_7]

end HartshorneEtAl2016.Examples
