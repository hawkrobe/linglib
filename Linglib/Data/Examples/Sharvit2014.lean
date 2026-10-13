module

public import Linglib.Data.Examples.Schema

/-!
# `Sharvit2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Sharvit2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sharvit2014.Examples`.
-/

@[expose] public section

namespace Sharvit2014.Examples

def ex_1 : Datum :=
  { id := "sharvit2014_1"
    source := ⟨"sharvit-2014", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left the meeting before Mary arrived."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past")] }

def ex_2 : Datum :=
  { id := "sharvit2014_2"
    source := ⟨"sharvit-2014", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left the meeting before Mary arrives."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "present")] }

def ex_3 : Datum :=
  { id := "sharvit2014_3"
    source := ⟨"sharvit-2014", "(3)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ni at-ta mae-ni denwa-o si-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ni", "Hanako-DAT"), ("at-ta", "meet-PAST"), ("mae-ni", "before"), ("denwa-o", "phone-ACC"), ("si-ta", "do-PAST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past")] }

def ex_4 : Datum :=
  { id := "sharvit2014_4"
    source := ⟨"sharvit-2014", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ni au mae-ni denwa-o si-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ni", "Hanako-DAT"), ("au", "meet-PRES"), ("mae-ni", "before"), ("denwa-o", "phone-ACC"), ("si-ta", "do-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "present")] }

def ex_5 : Datum :=
  { id := "sharvit2014_5"
    source := ⟨"sharvit-2014", "(5)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania przyszła na przyjęcie zanim Marcin przyszedł."
    glossedTokens := [("Ania", "Ania"), ("przyszła", "PRF-come-PAST"), ("na", "to"), ("przyjęcie", "party"), ("zanim", "before"), ("Marcin", "Marcin"), ("przyszedł", "PRF-come PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past")] }

def ex_6 : Datum :=
  { id := "sharvit2014_6"
    source := ⟨"sharvit-2014", "(6)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania przyszła na przyjęcie zanim Marcin przychodzi."
    glossedTokens := [("Ania", "Ania"), ("przyszła", "PRF-come-PAST"), ("na", "to"), ("przyjęcie", "party"), ("zanim", "before"), ("Marcin", "Marcin"), ("przychodzi", "PRF-come PRES")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "present")] }

def ex_7 : Datum :=
  { id := "sharvit2014_7"
    source := ⟨"sharvit-2014", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said that Mary was sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable), ("back-shifted", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "past")] }

def ex_8a : Datum :=
  { id := "sharvit2014_8a"
    source := ⟨"sharvit-2014", "(8a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ga byooki-da-to it-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byooki-da", "be-sick-PRES"), ("-to", "that"), ("it-ta", "say-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "present")] }

def ex_8b : Datum :=
  { id := "sharvit2014_8b"
    source := ⟨"sharvit-2014", "(8b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ga byooki-datta-to it-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byooki-datta", "be-sick-PAST"), ("-to", "that"), ("it-ta", "say-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable), ("back-shifted", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "past")] }

def ex_9a : Datum :=
  { id := "sharvit2014_9a"
    source := ⟨"sharvit-2014", "(9a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania powiedziała że Marcin jest chory."
    glossedTokens := [("Ania", "Ania"), ("powiedziała", "say-PRF-PAST"), ("że", "that"), ("Marcin", "Marcin"), ("jest", "be-PRES"), ("chory", "sick")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "present")] }

def ex_9b : Datum :=
  { id := "sharvit2014_9b"
    source := ⟨"sharvit-2014", "(9b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania powiedziała że Marcin był chory."
    glossedTokens := [("Ania", "Ania"), ("powiedziała", "say-PRF-PAST"), ("że", "that"), ("Marcin", "Marcin"), ("był", "be-PAST"), ("chory", "sick")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable), ("back-shifted", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "past")] }

def ex_46 : Datum :=
  { id := "sharvit2014_46"
    source := ⟨"sharvit-2014", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John found out that Mary is sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable), ("double access", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "present")] }

def ex_50b_did : Datum :=
  { id := "sharvit2014_50b_did"
    source := ⟨"sharvit-2014", "(50b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left before Sally arrived, which she did this morning."
    glossedTokens := []
    context := "John's leaving and Sally's arrival are independent of each other."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past"), ("clauseTime", "before speech")] }

def ex_50b_will : Datum :=
  { id := "sharvit2014_50b_will"
    source := ⟨"sharvit-2014", "(50b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left before Sally arrived, which she will tomorrow."
    glossedTokens := []
    context := "John's leaving and Sally's arrival are independent of each other."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past"), ("clauseTime", "after speech")] }

def ex_51 : Datum :=
  { id := "sharvit2014_51"
    source := ⟨"sharvit-2014", "(51)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mary-wa asu toochakusu-ru koto-ni nat-te i-ru. dakara, John-ga Mary-ga toochakusu-ru maeni syuppatsusi-ta to iu koto-wa hontoo-da."
    glossedTokens := [("Mary-wa", "Mary-TOP"), ("asu", "tomorrow"), ("toochakusu-ru", "arrive-PRES"), ("koto-ni", "fact-DAT"), ("nat-te", "become-GER"), ("i-ru", "be-PRES"), ("dakara,", "So"), ("John-ga", "John-NOM"), ("Mary-ga", "Mary-NOM"), ("toochakusu-ru", "arrive-PRES"), ("maeni", "before"), ("syuppatsusi-ta", "depart-PAST"), ("to iu", "say"), ("koto-wa", "fact-TOP"), ("hontoo-da", "true")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "present"), ("clauseTime", "after speech")] }

def ex_103 : Datum :=
  { id := "sharvit2014_103"
    source := ⟨"sharvit-2014", "(103)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis efige prin efige i Maria."
    glossedTokens := [("O", "the"), ("Janis", "John"), ("efige", "leave-PAST-PERF"), ("prin", "before"), ("efige", "leave-PAST-PERF"), ("i", "the"), ("Maria", "Mary")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("O Janis efige prin na efige i Maria.", .ungrammatical), ("O Janis efige prin efevge i Maria.", .ungrammatical), ("O Janis efige prin na efevge i Maria.", .ungrammatical)]
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past")] }

def ex_104 : Datum :=
  { id := "sharvit2014_104"
    source := ⟨"sharvit-2014", "(104)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 1963 o Kostas mas ipe oti i Maria itan eggios."
    glossedTokens := [("To", "the"), ("1963", "1963"), ("o", "the"), ("Kostas", "Kostas"), ("mas", "us"), ("ipe", "tell-PAST"), ("oti", "that"), ("i", "the"), ("Maria", "Maria"), ("itan", "be-PAST"), ("eggios", "pregnant")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "past")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8a, ex_8b, ex_9a, ex_9b, ex_46, ex_50b_did, ex_50b_will, ex_51, ex_103, ex_104]

end Sharvit2014.Examples
