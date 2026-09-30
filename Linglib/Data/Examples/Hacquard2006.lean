module

public import Linglib.Data.Examples.Schema

/-!
# `Hacquard2006` — typed example data

Auto-generated from `Linglib/Data/Examples/Hacquard2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hacquard2006.Examples`.
-/

@[expose] public section

namespace Hacquard2006.Examples

open Data.Examples

def ex1a : Datum :=
  { id := "hacquard2006_ex1a"
    source := ⟨"hacquard-2006", "(1a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Pour aller au zoo, Jane pouvait prendre le train."
    glossedTokens := [("Pour", "to"), ("aller", "go"), ("au", "to-the"), ("zoo,", "zoo,"), ("Jane", "Jane"), ("pouvait", "can-PST-IMPF"), ("prendre", "take"), ("le", "the"), ("train.", "train.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "intro"), ("phenomenon", "actualityEntailment"), ("aspect", "imperfective"), ("flavor", "goalOriented"), ("actualityEntailment", "false")] }

def ex1b : Datum :=
  { id := "hacquard2006_ex1b"
    source := ⟨"hacquard-2006", "(1b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Pour aller au zoo, Jane a pu prendre le train."
    glossedTokens := [("Pour", "to"), ("aller", "go"), ("au", "to-the"), ("zoo,", "zoo,"), ("Jane", "Jane"), ("a", "has"), ("pu", "can-PST-PFV"), ("prendre", "take"), ("le", "the"), ("train.", "train.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "intro"), ("phenomenon", "actualityEntailment"), ("aspect", "perfective"), ("flavor", "goalOriented"), ("actualityEntailment", "true")] }

def ex2a : Datum :=
  { id := "hacquard2006_ex2a"
    source := ⟨"bhatt-1999", "(2a)"⟩
    reportedIn := some ⟨"hacquard-2006", "(2a)"⟩
    language := "stan1293"
    primaryText := "Yesterday, firemen were able to eat 50 apples."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "intro"), ("phenomenon", "actualityEntailment"), ("aspect", "perfective"), ("flavor", "ability"), ("actualityEntailment", "true")] }

def ex2b : Datum :=
  { id := "hacquard2006_ex2b"
    source := ⟨"hacquard-2006", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Back in the days, firemen were able to eat 50 apples."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "intro"), ("phenomenon", "actualityEntailment"), ("aspect", "imperfective"), ("flavor", "ability"), ("actualityEntailment", "false")] }

def ex22a : Datum :=
  { id := "hacquard2006_ex22a"
    source := ⟨"hacquard-2006", "(22a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a pu soulever cette table, mais elle ne l'a pas soulevée."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1.2"), ("phenomenon", "actualityEntailment"), ("aspect", "perfective"), ("flavor", "ability"), ("actualityEntailment", "true")] }

def ex22b : Datum :=
  { id := "hacquard2006_ex22b"
    source := ⟨"hacquard-2006", "(22b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Jane ha potuto sollevare questo tavolo, ma non lo ha fatto."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1.2"), ("phenomenon", "actualityEntailment"), ("aspect", "perfective"), ("flavor", "ability"), ("actualityEntailment", "true")] }

def ex23a : Datum :=
  { id := "hacquard2006_ex23a"
    source := ⟨"hacquard-2006", "(23a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane pouvait soulever cette table, mais elle ne l'a pas soulevée."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1.2"), ("phenomenon", "actualityEntailment"), ("aspect", "imperfective"), ("flavor", "ability"), ("actualityEntailment", "false")] }

def ex23b : Datum :=
  { id := "hacquard2006_ex23b"
    source := ⟨"hacquard-2006", "(23b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Jane poteva sollevare questo tavolo, ma non lo ha fatto."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1.2"), ("phenomenon", "actualityEntailment"), ("aspect", "imperfective"), ("flavor", "ability"), ("actualityEntailment", "false")] }

def ex81a : Datum :=
  { id := "hacquard2006_ex81a"
    source := ⟨"hacquard-2006", "(81a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Darcy a pu épouser une clocharde."
    glossedTokens := []
    context := "Darcy proposes to Jane thinking she is homeless; she is in fact an eccentric billionaire."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2.3"), ("phenomenon", "eventIdentification"), ("aspect", "perfective"), ("flavor", "circumstantial"), ("actualityEntailment", "true")] }

def ex81b : Datum :=
  { id := "hacquard2006_ex81b"
    source := ⟨"hacquard-2006", "(81b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Darcy a pu épouser une milliardaire."
    glossedTokens := []
    context := "Darcy proposes to Jane thinking she is homeless; she is in fact an eccentric billionaire."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2.3"), ("phenomenon", "eventIdentification"), ("aspect", "perfective"), ("flavor", "circumstantial"), ("actualityEntailment", "true")] }

def ex86 : Datum :=
  { id := "hacquard2006_ex86"
    source := ⟨"hacquard-2006", "(86)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a pu prendre le train pour aller à Paris."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2.5"), ("phenomenon", "goalOriented"), ("aspect", "perfective"), ("flavor", "goalOriented"), ("actualityEntailment", "true")] }

def ex87 : Datum :=
  { id := "hacquard2006_ex87"
    source := ⟨"hacquard-2006", "(87)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a dû prendre le train pour aller à Paris."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2.5"), ("phenomenon", "goalOriented"), ("aspect", "perfective"), ("flavor", "goalOriented"), ("actualityEntailment", "true")] }

def ex88 : Datum :=
  { id := "hacquard2006_ex88"
    source := ⟨"hacquard-2006", "(88)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a pu prendre l'avion pour aller à Londres, mais l'avion a été détourné vers Manchester, et elle n'est jamais arrivée à Londres."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2.5"), ("phenomenon", "goalOriented"), ("aspect", "perfective"), ("flavor", "goalOriented"), ("actualityEntailment", "true")] }

def ex89a : Datum :=
  { id := "hacquard2006_ex89a"
    source := ⟨"hacquard-2006", "(89a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a pris le train pour aller à Paris."
    glossedTokens := [("Jane", "Jane"), ("a", "has"), ("pris", "taken"), ("le", "the"), ("train", "train"), ("pour", "to"), ("aller", "go"), ("à", "to"), ("Paris.", "Paris.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2.5"), ("phenomenon", "implicature"), ("aspect", "perfective")] }

def ex89b : Datum :=
  { id := "hacquard2006_ex89b"
    source := ⟨"hacquard-2006", "(89b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a pu prendre le train pour aller à Paris."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2.5"), ("phenomenon", "implicature"), ("aspect", "perfective"), ("flavor", "goalOriented"), ("actualityEntailment", "true")] }

def ex89c : Datum :=
  { id := "hacquard2006_ex89c"
    source := ⟨"hacquard-2006", "(89c)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a dû prendre le train pour aller à Paris."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2.5"), ("phenomenon", "implicature"), ("aspect", "perfective"), ("flavor", "goalOriented"), ("actualityEntailment", "true")] }

def ex100a : Datum :=
  { id := "hacquard2006_ex100a"
    source := ⟨"hacquard-2006", "(100a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Elisabeth pouvait parler aux singes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "genericAbility"), ("aspect", "imperfective"), ("flavor", "ability"), ("actualityEntailment", "false")] }

def ex100b : Datum :=
  { id := "hacquard2006_ex100b"
    source := ⟨"hacquard-2006", "(100b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Cette voiture pouvait faire du 250 km/h."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "genericAbility"), ("aspect", "imperfective"), ("flavor", "ability"), ("actualityEntailment", "false")] }

def ex101a : Datum :=
  { id := "hacquard2006_ex101a"
    source := ⟨"hacquard-2006", "(101a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "...et qu'elle pouvait leur parler. Malheureusement, quand on est arrivé, tous les singes avaient déjà été transférés au nouveau zoo."
    glossedTokens := []
    context := "Hier on est allé au zoo avec les enfants. Elisabeth était particulièrement heureuse, parce qu'elle adorait les singes"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "genericAbility"), ("aspect", "imperfective"), ("flavor", "ability"), ("actualityEntailment", "false")] }

def ex101b : Datum :=
  { id := "hacquard2006_ex101b"
    source := ⟨"hacquard-2006", "(101b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "...et qu'elle a pu leur parler. Malheureusement, quand on est arrivé, tous les singes avaient déjà été transférés au nouveau zoo."
    glossedTokens := []
    context := "Hier on est allé au zoo avec les enfants. Elisabeth était particulièrement heureuse, parce qu'elle adorait les singes"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "genericAbility"), ("aspect", "perfective"), ("flavor", "ability"), ("actualityEntailment", "true")] }

def ex103 : Datum :=
  { id := "hacquard2006_ex103"
    source := ⟨"hacquard-2006", "(103)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane pouvait prendre le train pour aller à Londres, mais elle..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "counterfactualImperfective"), ("aspect", "imperfective"), ("flavor", "goalOriented"), ("actualityEntailment", "false")] }

def ex201 : Datum :=
  { id := "hacquard2006_ex201"
    source := ⟨"hacquard-2006", "(201)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a dû prendre le train."
    glossedTokens := [("Jane", "Jane"), ("a", "has"), ("dû", "must-PST-PFV"), ("prendre", "take"), ("le", "the"), ("train.", "train.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("epistemic: given my evidence now, Jane must have taken the train", .acceptable), ("goalOriented: given Jane's circumstances then, Jane had to take the train", .acceptable)]
    paperFeatures := [("section", "3.4.1"), ("phenomenon", "eventBinding")] }

def ex242a : Datum :=
  { id := "hacquard2006_ex242a"
    source := ⟨"hacquard-2006", "(242a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A l'heure du crime, Jane pouvait être en train de lire un livre."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("phenomenon", "progressiveComplement"), ("aspect", "imperfective"), ("flavor", "epistemic")] }

def ex242b : Datum :=
  { id := "hacquard2006_ex242b"
    source := ⟨"hacquard-2006", "(242b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A l'heure du crime, Jane devait lire un livre."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("phenomenon", "progressiveComplement"), ("aspect", "imperfective"), ("flavor", "epistemic")] }

def ex244a : Datum :=
  { id := "hacquard2006_ex244a"
    source := ⟨"hacquard-2006", "(244a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane can be sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("phenomenon", "changeOfState"), ("flavor", "ability")] }

def ex244b : Datum :=
  { id := "hacquard2006_ex244b"
    source := ⟨"hacquard-2006", "(244b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane can have blue eyes."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("phenomenon", "changeOfState"), ("flavor", "ability")] }

def ex245a : Datum :=
  { id := "hacquard2006_ex245a"
    source := ⟨"hacquard-2006", "(245a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a pu être malade."
    glossedTokens := [("Jane", "Jane"), ("a", "has"), ("pu", "can-PST-PFV"), ("être", "be"), ("malade.", "sick.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("phenomenon", "changeOfState"), ("aspect", "perfective"), ("flavor", "epistemic"), ("actualityEntailment", "false")] }

def ex246 : Datum :=
  { id := "hacquard2006_ex246"
    source := ⟨"hacquard-2006", "(246)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane could lift this table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("phenomenon", "contentLicensing"), ("flavor", "ability")] }

def ex247b : Datum :=
  { id := "hacquard2006_ex247b"
    source := ⟨"hacquard-2006", "(247b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a pu penser que Darcy aimait Lizzie."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("speechBoundEpistemic: possible given the speaker's evidence", .acceptable), ("aspectBoundEpistemic: an epistemic necessity for Jane at a past belief state", .questionable)]
    paperFeatures := [("section", "3.4.3"), ("phenomenon", "contentLicensing"), ("aspect", "perfective")] }

def ex249b : Datum :=
  { id := "hacquard2006_ex249b"
    source := ⟨"hacquard-2006", "(249b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a pu remarquer que Darcy était gentil."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("phenomenon", "contentLicensing"), ("aspect", "perfective"), ("actualityEntailment", "true")] }

def all : List Datum := [ex1a, ex1b, ex2a, ex2b, ex22a, ex22b, ex23a, ex23b, ex81a, ex81b, ex86, ex87, ex88, ex89a, ex89b, ex89c, ex100a, ex100b, ex101a, ex101b, ex103, ex201, ex242a, ex242b, ex244a, ex244b, ex245a, ex246, ex247b, ex249b]

end Hacquard2006.Examples
