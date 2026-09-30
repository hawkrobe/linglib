module

public import Linglib.Data.Examples.Schema

/-!
# `FuscoSgrizzi2026` — typed example data

Auto-generated from `Linglib/Data/Examples/FuscoSgrizzi2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FuscoSgrizzi2026.Examples`.
-/

@[expose] public section

namespace FuscoSgrizzi2026.Examples

open Data.Examples

def ex4a : Datum :=
  { id := "fuscosgrizzi2026_ex4a"
    source := ⟨"fusco-sgrizzi-2026", "(4a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni di avere un figlio."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("di", "di"), ("avere", "have-INF"), ("un", "a"), ("figlio.", "child")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "cP"), ("diagnostic", "belief"), ("grammatical", "yes")] }

def ex4b : Datum :=
  { id := "fuscosgrizzi2026_ex4b"
    source := ⟨"fusco-sgrizzi-2026", "(4b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni a avere un figlio."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("a", "a"), ("avere", "have-INF"), ("un", "a"), ("figlio.", "child")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "intention"), ("grammatical", "yes")] }

def ex4a_control : Datum :=
  { id := "fuscosgrizzi2026_ex4a_control"
    source := ⟨"fusco-sgrizzi-2026", "(4a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni di avere un figlio."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("di", "di"), ("avere", "have-INF"), ("un", "a"), ("figlio.", "child")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "cP"), ("diagnostic", "subjectControl"), ("grammatical", "yes")] }

def ex4b_control : Datum :=
  { id := "fuscosgrizzi2026_ex4b_control"
    source := ⟨"fusco-sgrizzi-2026", "(4b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni a avere un figlio."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("a", "a"), ("avere", "have-INF"), ("un", "a"), ("figlio.", "child")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "subjectControl"), ("grammatical", "no")] }

def ex11a : Datum :=
  { id := "fuscosgrizzi2026_ex11a"
    source := ⟨"fusco-sgrizzi-2026", "(11a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni di avere un figlio, ma non è vero."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("di", "di"), ("avere", "have-INF"), ("un", "a"), ("figlio,", "child"), ("ma", "but"), ("non", "not"), ("è", "be-PRS.3SG"), ("vero.", "true")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "cP"), ("diagnostic", "truthAssessable"), ("grammatical", "yes")] }

def ex11b : Datum :=
  { id := "fuscosgrizzi2026_ex11b"
    source := ⟨"fusco-sgrizzi-2026", "(11b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni ad avere un figlio, ma non è vero."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("ad", "a"), ("avere", "have-INF"), ("un", "a"), ("figlio,", "child"), ("ma", "but"), ("non", "not"), ("è", "be-PRS.3SG"), ("vero.", "true")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "truthAssessable"), ("grammatical", "no")] }

def ex12 : Datum :=
  { id := "fuscosgrizzi2026_ex12"
    source := ⟨"fusco-sgrizzi-2026", "(12)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La conduttrice ha convinto l'ospite ad essere intervistato."
    glossedTokens := [("La", "the"), ("conduttrice", "conductor"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("l'ospite", "the.guest"), ("ad", "a"), ("essere", "be-INF"), ("intervistato.", "interviewed-PST.PTCP.M")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "passive"), ("grammatical", "yes")] }

def ex13 : Datum :=
  { id := "fuscosgrizzi2026_ex13"
    source := ⟨"fusco-sgrizzi-2026", "(13)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni a cominciare a lavorare."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("a", "a"), ("cominciare", "begin-INF"), ("a", "to"), ("lavorare.", "work-INF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "aspectual"), ("grammatical", "yes")] }

def ex14 : Datum :=
  { id := "fuscosgrizzi2026_ex14"
    source := ⟨"fusco-sgrizzi-2026", "(14)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "L'operaio lo prova a costruire."
    glossedTokens := [("L'operaio", "the-worker"), ("lo", "it"), ("prova", "try-PRS.3SG"), ("a", "to"), ("costruire.", "build")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "vP"), ("diagnostic", "cliticClimbing"), ("grammatical", "yes")] }

def ex15 : Datum :=
  { id := "fuscosgrizzi2026_ex15"
    source := ⟨"fusco-sgrizzi-2026", "(15)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni lo pensa a costruire domani."
    glossedTokens := [("Gianni", "Gianni"), ("lo", "it"), ("pensa", "think-PRS.3SG"), ("a", "to"), ("costruire", "build"), ("domani.", "tomorrow")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "cliticClimbing"), ("grammatical", "no")] }

def ex16 : Datum :=
  { id := "fuscosgrizzi2026_ex16"
    source := ⟨"fusco-sgrizzi-2026", "(16)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni mi ha convinto a non salutare più il capo."
    glossedTokens := [("Gianni", "Gianni"), ("mi", "me.CL"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("a", "to"), ("non", "not"), ("salutare", "greet-INF"), ("più", "anymore"), ("il", "the"), ("capo.", "boss")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "negation"), ("grammatical", "yes")] }

def ex17 : Datum :=
  { id := "fuscosgrizzi2026_ex17"
    source := ⟨"fusco-sgrizzi-2026", "(17)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri Gianni mi ha convinto a comprare una macchina nuova il mese prossimo."
    glossedTokens := [("Ieri", "yesterday"), ("Gianni", "Gianni"), ("mi", "me.CL"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("a", "to"), ("comprare", "buy-INF"), ("una", "a"), ("macchina", "car"), ("nuova", "new"), ("il", "the"), ("mese", "month"), ("prossimo.", "next")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "independentTime"), ("grammatical", "yes")] }

def ex18 : Datum :=
  { id := "fuscosgrizzi2026_ex18"
    source := ⟨"fusco-sgrizzi-2026", "(18)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri Gianni ha provato a riparare la macchina il mese prossimo."
    glossedTokens := [("Ieri", "yesterday"), ("Gianni", "Gianni"), ("ha", "have-PRS.3SG"), ("provato", "try-PST.PTCP"), ("a", "to"), ("riparare", "repair"), ("la", "the"), ("macchina", "car"), ("il", "the"), ("mese", "month"), ("prossimo.", "next")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "vP"), ("diagnostic", "independentTime"), ("grammatical", "no")] }

def all : List Datum := [ex4a, ex4b, ex4a_control, ex4b_control, ex11a, ex11b, ex12, ex13, ex14, ex15, ex16, ex17, ex18]

end FuscoSgrizzi2026.Examples
