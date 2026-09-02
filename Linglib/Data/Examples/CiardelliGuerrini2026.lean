import Linglib.Data.Examples.Schema

/-!
# `CiardelliGuerrini2026` — typed example data

Auto-generated from `Linglib/Data/Examples/CiardelliGuerrini2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace CiardelliGuerrini2026.Examples`.
-/

namespace CiardelliGuerrini2026.Examples

open Data.Examples

def cg2026_2_may_or_may : LinguisticExample :=
  { id := "cg2026_2_may_or_may"
    source := ⟨"ciardelli-guerrini-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may do A or you may do B."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice: you may do A and you may do B", .acceptable), ("ignorance: the speaker is unsure which of A and B is allowed", .acceptable)]
    paperFeatures := [("coordinator", "or"), ("modalForce", "possibility")]
    comment := "The wide-scope free-choice datum. The paper's thesis: the free-choice reading comes from the narrow-scope LF, the ignorance reading from the wide-scope LF."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cg2026_5_must_or_must : LinguisticExample :=
  { id := "cg2026_5_must_or_must"
    source := ⟨"ciardelli-guerrini-2026", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Either) you must write an essay or you must give a presentation."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Alice asks Bob how one can get credit for a certain course; Bob replies."
    judgment := .acceptable
    alternatives := []
    readings := [("disjunctive obligation: to get credit one is required to do either of two things; dominant when Bob is knowledgeable, e.g. the instructor", .acceptable), ("ignorance: Bob is uncertain whether one gets credit by essay or by presentation, and could follow up with 'I'm not sure which'", .acceptable)]
    paperFeatures := [("coordinator", "or"), ("modalForce", "necessity")]
    comment := "Must-or-must: under necessity the scope distinction is truth-conditionally visible, so the ambiguity of MOD-A-COORD-MOD-B is directly detectable."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cg2026_7_may_and_may : LinguisticExample :=
  { id := "cg2026_7_may_and_may"
    source := ⟨"ciardelli-guerrini-2026", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may go to Bob's party and you may go to Charlie's party."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Bob, Charlie, and Diana each invited Alice to their birthday party this week. Alice asks her mom for permission; mom rules out Diana's party because of an exam, then says this."
    judgment := .acceptable
    alternatives := []
    readings := [("conjunctive permission: Alice is permitted to go to both parties (the natural reading; how many parties may Alice attend? two)", .acceptable), ("conjunction of permissions: each party is individually permitted; brought out by the continuation 'but you can't go to both'", .acceptable)]
    paperFeatures := [("coordinator", "and"), ("modalForce", "possibility")]
    comment := "May-and-may: unlike disjunction, conjunction under a possibility modal makes the scope distinction truth-conditionally visible."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [cg2026_2_may_or_may, cg2026_5_must_or_must, cg2026_7_may_and_may]

end CiardelliGuerrini2026.Examples
