module

public import Linglib.Data.Examples.Schema

/-!
# `DelPinal2015` — typed example data

Auto-generated from `Linglib/Data/Examples/DelPinal2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DelPinal2015.Examples`.
-/

@[expose] public section

namespace DelPinal2015.Examples

open Data.Examples

def fake_gun : LinguisticExample :=
  { id := "delpinal2015_fake_gun"
    source := ⟨"delpinal-2015", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fake gun"
    glossedTokens := [("fake", "fake"), ("gun", "gun")]
    context := "Paper eq. 17 worked composition: fake gun's E-structure asserts ¬gun(x), ¬made-as-gun, ∃e[MAKING(e) ∧ GOAL(e, perceptual-gun(x))]. C-structure: TELIC negated (not for shooting), FORMAL preserved (looks like gun), AGENTIVE = made-to-look-like-gun. The canonical privative."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def counterfeit_rolex : LinguisticExample :=
  { id := "delpinal2015_counterfeit_rolex"
    source := ⟨"delpinal-2015", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "counterfeit Rolex"
    glossedTokens := [("counterfeit", "counterfeit"), ("Rolex", "Rolex")]
    context := "Paper eq. 11: counterfeit differs from fake in TELIC. A counterfeit Rolex is made to BOTH look AND function like a Rolex (GOAL includes Q_F AND Q_T); a fake Rolex would only need to look like one."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def artificial_heart : LinguisticExample :=
  { id := "delpinal2015_artificial_heart"
    source := ⟨"delpinal-2015", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "artificial heart"
    glossedTokens := [("artificial", "artificial"), ("heart", "heart")]
    context := "Paper eq. 12: artificial differs from fake in NOT negating FORMAL. An artificial heart need not look like a heart but is made with the intention that it function like a heart (GOAL = Q_T, not Q_F). Some find ¬Q_E itself unstable for 'artificial' (paper notes mixed intuitions about whether artificial legs are 'really' legs)."
    judgment := .acceptable
    alternatives := []
    readings := [("strict privative (¬Q_E preserved)", .acceptable), ("non-privative (Q_E preserved)", .marginal)]
    paperFeatures := [] }

def fake_chanel_handbag : LinguisticExample :=
  { id := "delpinal2015_fake_chanel_handbag"
    source := ⟨"delpinal-2015", "fn. 12"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fake Chanel handbag"
    glossedTokens := [("fake", "fake"), ("Chanel", "Chanel"), ("handbag", "handbag")]
    context := "Paper footnote 12: structural-scope ambiguity diagnostic. (i) [fake [Chanel handbag]]: a counterfeit Chanel handbag (negates AGENTIVE of 'Chanel handbag' = the brand-source quale). (ii) [[fake Chanel] handbag]: a handbag whose 'Chanel' attribution is fake (could be a real handbag, falsely branded). Distinguishes DC from coarser noun-coercion accounts that don't distinguish the two scopes."
    judgment := .acceptable
    alternatives := []
    readings := [("[fake [Chanel handbag]] (counterfeit)", .acceptable), ("[[fake Chanel] handbag] (falsely-branded)", .acceptable)]
    paperFeatures := [] }

def all : List LinguisticExample := [fake_gun, counterfeit_rolex, artificial_heart, fake_chanel_handbag]

end DelPinal2015.Examples
