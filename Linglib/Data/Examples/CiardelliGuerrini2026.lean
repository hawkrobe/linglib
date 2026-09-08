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

def ex2 : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex2"
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
    readings := [("free choice", .acceptable), ("ignorance", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "may"), ("coordinator", "or"), ("narrowReading", "free choice")]
    comment := "Free choice: you may do A and you may do B. Ignorance: the speaker is unsure which of A and B is allowed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5 : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex5"
    source := ⟨"ciardelli-guerrini-2026", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Either) you must write an essay or you must give a presentation."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Alice asks Bob how one can get credit for a certain course."
    judgment := .acceptable
    alternatives := []
    readings := [("disjunctive obligation", .acceptable), ("ignorance", .acceptable)]
    paperFeatures := [("modal1", "must"), ("modal2", "must"), ("coordinator", "or"), ("narrowReading", "disjunctive obligation")]
    comment := "Disjunctive obligation: to get credit one is required to do either of two things, dominant when Bob is knowledgeable. Ignorance: Bob is uncertain whether one gets credit by essay or by presentation and could follow up with 'I'm not sure which'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7 : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex7"
    source := ⟨"ciardelli-guerrini-2026", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may go to Bob's party and you may go to Charlie's party."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Alice's friends Bob, Charlie and Diana each invited her to their birthday party this week. Mom says she cannot go to Diana's party, then:"
    judgment := .acceptable
    alternatives := []
    readings := [("conjunctive permission", .acceptable), ("conjunction of permissions", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "may"), ("coordinator", "and"), ("narrowReading", "conjunctive permission")]
    comment := "Conjunctive permission: Alice is permitted to go to both parties, the natural reading. Conjunction of permissions: each party is individually permitted, brought out by the continuation 'but you can't go to both'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex9b : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex9b"
    source := ⟨"ciardelli-guerrini-2026", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may come with me and you may stay here."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := [("conjunctive permission", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "may"), ("coordinator", "and"), ("narrowReading", "conjunctive permission")]
    comment := "Has one striking reading on which it is absurd, since it implies the possibility of both going and staying; (9a) with 'or' is perfectly natural."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex19a : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex19a"
    source := ⟨"ciardelli-guerrini-2026", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's ok for John to sing or it's ok for John to dance."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("modal1", "it's ok"), ("modal2", "it's ok"), ("coordinator", "or")]
    comment := "No free-choice reading, the contrast of Meyer and Sauerland (2017)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex19b_allowed : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex19b_allowed"
    source := ⟨"ciardelli-guerrini-2026", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is allowed to sing or he is allowed to dance."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("modal1", "be allowed"), ("modal2", "be allowed"), ("coordinator", "or")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex19b_required : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex19b_required"
    source := ⟨"ciardelli-guerrini-2026", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is required to sing or he is required to dance."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("modal1", "be required"), ("modal2", "be required"), ("coordinator", "or")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex22a : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex22a"
    source := ⟨"ciardelli-guerrini-2026", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John may either sing or he may dance."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "may"), ("coordinator", "or"), ("narrowReading", "free choice")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex22b : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex22b"
    source := ⟨"ciardelli-guerrini-2026", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either John may sing or he may dance."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "may"), ("coordinator", "or"), ("narrowReading", "free choice")]
    comment := "Free choice survives a high 'either', above which across-the-board movement is impossible, (21)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exfn4i : LinguisticExample :=
  { id := "ciardelliguerrini2026_exfn4i"
    source := ⟨"ciardelli-guerrini-2026", "fn. 4 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may email us or you can reach the Business License office at 949 644-3141."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "can"), ("coordinator", "or"), ("narrowReading", "free choice")]
    comment := "Alonso-Ovalle's (2006) mixed-form case."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex28 : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex28"
    source := ⟨"ciardelli-guerrini-2026", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I need not cook and I need not clean."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("permission to do neither", .acceptable), ("obligation to do neither", .unacceptable)]
    paperFeatures := [("modal1", "need"), ("modal2", "need"), ("coordinator", "and"), ("narrowReading", "permission to do neither"), ("negated", "true")]
    comment := "Conveys that I am permitted to neither cook nor clean, not that I am required to do neither."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11a : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex11a"
    source := ⟨"ciardelli-guerrini-2026", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boss allows that Alice may leave."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("modal concord", .acceptable)]
    paperFeatures := [("checker", "allow"), ("checked", "may")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11b : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex11b"
    source := ⟨"ciardelli-guerrini-2026", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boss demands that Bob must stay."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("modal concord", .acceptable)]
    paperFeatures := [("checker", "demand"), ("checked", "must")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex20a : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex20a"
    source := ⟨"ciardelli-guerrini-2026", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boss allows that Alice be permitted to leave."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("modal concord", .unacceptable)]
    paperFeatures := [("checker", "allow"), ("checked", "be permitted")]
    comment := "Unambiguously conveys that the boss is ok with the fact that Alice has permission to leave."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex20b : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex20b"
    source := ⟨"ciardelli-guerrini-2026", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boss demands that Bob be required to stay."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("modal concord", .unacceptable)]
    paperFeatures := [("checker", "demand"), ("checked", "be required")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex24 : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex24"
    source := ⟨"ciardelli-guerrini-2026", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The countess graciously allowed that I needn't do it for her again."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("modal concord", .acceptable)]
    paperFeatures := [("checker", "allow"), ("checked", "need"), ("negated", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex25 : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex25"
    source := ⟨"ciardelli-guerrini-2026", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A restraining order demands that Roiland may not harass or surveil the plaintiff."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("modal concord", .acceptable)]
    paperFeatures := [("checker", "demand"), ("checked", "may"), ("negated", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex26 : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex26"
    source := ⟨"ciardelli-guerrini-2026", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The countess firmly demanded that I needn't do it for her again."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("modal concord", .unacceptable)]
    paperFeatures := [("checker", "demand"), ("checked", "need"), ("negated", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex27 : LinguisticExample :=
  { id := "ciardelliguerrini2026_ex27"
    source := ⟨"ciardelli-guerrini-2026", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A special permit allows that Roiland may not recycle."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("modal concord", .unacceptable)]
    paperFeatures := [("checker", "allow"), ("checked", "may"), ("negated", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex2, ex5, ex7, ex9b, ex19a, ex19b_allowed, ex19b_required, ex22a, ex22b, exfn4i, ex28, ex11a, ex11b, ex20a, ex20b, ex24, ex25, ex26, ex27]

end CiardelliGuerrini2026.Examples
