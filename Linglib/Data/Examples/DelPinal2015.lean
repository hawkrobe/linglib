import Linglib.Data.Examples.Schema

/-!
# `DelPinal2015` — typed example data

Auto-generated from `Linglib/Data/Examples/DelPinal2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DelPinal2015.Examples`.
-/

namespace DelPinal2015.Examples

open Data.Examples

def fake_gun : LinguisticExample :=
  { id := "delpinal2015_fake_gun"
    source := ⟨"delpinal-2015", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fake gun"
    discourseSegments := []
    glossedTokens := [("fake", "fake"), ("gun", "gun")]
    translation := "fake gun"
    context := "Paper eq. 17 worked composition: fake gun's E-structure asserts ¬gun(x), ¬made-as-gun, ∃e[MAKING(e) ∧ GOAL(e, perceptual-gun(x))]. C-structure: TELIC negated (not for shooting), FORMAL preserved (looks like gun), AGENTIVE = made-to-look-like-gun. The canonical privative."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Del Pinal §3 eq. 17. Illustrates the full DC composition for the privative paradigm case. The TELIC-negation entailment (fake gun is not for shooting) distinguishes DC from a coarser Kamp-privative analysis that only commits to ¬gun."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def counterfeit_rolex : LinguisticExample :=
  { id := "delpinal2015_counterfeit_rolex"
    source := ⟨"delpinal-2015", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "counterfeit Rolex"
    discourseSegments := []
    glossedTokens := [("counterfeit", "counterfeit"), ("Rolex", "Rolex")]
    translation := "counterfeit Rolex"
    context := "Paper eq. 11: counterfeit differs from fake in TELIC. A counterfeit Rolex is made to BOTH look AND function like a Rolex (GOAL includes Q_F AND Q_T); a fake Rolex would only need to look like one."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Del Pinal §3 eq. 11. Discriminates counterfeit from fake at the C-structure level: counterfeit's AGENTIVE asserts MAKING with GOAL = (Q_F ∧ Q_T)(N), fake's asserts MAKING with GOAL = Q_F(N) only. This three-way contrast (fake/counterfeit/artificial) is the DC-specific empirical wedge against any account that lumps all privatives."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def artificial_heart : LinguisticExample :=
  { id := "delpinal2015_artificial_heart"
    source := ⟨"delpinal-2015", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "artificial heart"
    discourseSegments := []
    glossedTokens := [("artificial", "artificial"), ("heart", "heart")]
    translation := "artificial heart"
    context := "Paper eq. 12: artificial differs from fake in NOT negating FORMAL. An artificial heart need not look like a heart but is made with the intention that it function like a heart (GOAL = Q_T, not Q_F). Some find ¬Q_E itself unstable for 'artificial' (paper notes mixed intuitions about whether artificial legs are 'really' legs)."
    judgment := .acceptable
    alternatives := []
    readings := [("strict privative (¬Q_E preserved)", .acceptable), ("non-privative (Q_E preserved)", .marginal)]
    paperFeatures := []
    comment := "Del Pinal §3 eq. 12. Completes the fake/counterfeit/artificial trio. The reading-level annotation captures Del Pinal's own observation (p. 17) that mature speakers give 'mixed and unstable intuitions' about whether artificial N is a kind of N — a graded privativity that no purely-binary classification can model."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def fake_chanel_handbag : LinguisticExample :=
  { id := "delpinal2015_fake_chanel_handbag"
    source := ⟨"delpinal-2015", "fn. 12"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fake Chanel handbag"
    discourseSegments := []
    glossedTokens := [("fake", "fake"), ("Chanel", "Chanel"), ("handbag", "handbag")]
    translation := "fake Chanel handbag"
    context := "Paper footnote 12: structural-scope ambiguity diagnostic. (i) [fake [Chanel handbag]]: a counterfeit Chanel handbag (negates AGENTIVE of 'Chanel handbag' = the brand-source quale). (ii) [[fake Chanel] handbag]: a handbag whose 'Chanel' attribution is fake (could be a real handbag, falsely branded). Distinguishes DC from coarser noun-coercion accounts that don't distinguish the two scopes."
    judgment := .acceptable
    alternatives := []
    readings := [("[fake [Chanel handbag]] (counterfeit)", .acceptable), ("[[fake Chanel] handbag] (falsely-branded)", .acceptable)]
    paperFeatures := []
    comment := "Del Pinal §3 footnote 12. The scope ambiguity is structurally derivable in DC because both 'Chanel' (a brand-name modifier, adding to AGENTIVE) and 'fake' (a semantic restructuring operator) compose via FA_DC at different bracketings. Partee's noun-coercion account does not naturally yield the two readings — the canonical diagnostic for the DC-vs-Partee divergence on iterated privatives."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [fake_gun, counterfeit_rolex, artificial_heart, fake_chanel_handbag]

end DelPinal2015.Examples
