module

public import Linglib.Data.Examples.Schema

/-!
# `KratzerShimoyama2002` — typed example data

Auto-generated from `Linglib/Data/Examples/KratzerShimoyama2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KratzerShimoyama2002.Examples`.
-/

@[expose] public section

namespace KratzerShimoyama2002.Examples

def ex23a : Datum :=
  { id := "kratzershimoyama2002_ex23a"
    source := ⟨"kratzer-shimoyama-2002", "(23a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie nicht WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("nicht", "not"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "nicht"), ("feature", "Neg"), ("order", "intervener-first")] }

def ex23b : Datum :=
  { id := "kratzershimoyama2002_ex23b"
    source := ⟨"kratzer-shimoyama-2002", "(23b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie nie WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("nie", "never"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "nie"), ("feature", "exists"), ("order", "intervener-first")] }

def ex23c : Datum :=
  { id := "kratzershimoyama2002_ex23c"
    source := ⟨"kratzer-shimoyama-2002", "(23c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat niemand WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("niemand", "nobody"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "niemand"), ("feature", "exists"), ("order", "intervener-first")] }

def ex23d : Datum :=
  { id := "kratzershimoyama2002_ex23d"
    source := ⟨"kratzer-shimoyama-2002", "(23d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat fast jeder WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("fast", "almost"), ("jeder", "everybody"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "fast jeder"), ("feature", "exists"), ("order", "intervener-first")] }

def ex23e : Datum :=
  { id := "kratzershimoyama2002_ex23e"
    source := ⟨"kratzer-shimoyama-2002", "(23e)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat (irgend)jemand WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("(irgend)jemand", "somebody"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "(irgend)jemand"), ("feature", "exists"), ("order", "intervener-first")] }

def ex23f : Datum :=
  { id := "kratzershimoyama2002_ex23f"
    source := ⟨"kratzer-shimoyama-2002", "(23f)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat der Hans WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("der", "the"), ("Hans", "Hans"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "der Hans"), ("feature", "none"), ("order", "intervener-first")] }

def ex23g : Datum :=
  { id := "kratzershimoyama2002_ex23g"
    source := ⟨"kratzer-shimoyama-2002", "(23g)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie damals WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("damals", "then"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "damals"), ("feature", "none"), ("order", "intervener-first")] }

def ex24a : Datum :=
  { id := "kratzershimoyama2002_ex24a"
    source := ⟨"kratzer-shimoyama-2002", "(24a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie WEM nicht gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("WEM", "to.whom"), ("nicht", "not"), ("gezeigt", "shown")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "nicht"), ("feature", "Neg"), ("order", "wh-first")] }

def ex24b : Datum :=
  { id := "kratzershimoyama2002_ex24b"
    source := ⟨"kratzer-shimoyama-2002", "(24b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie WEM nie gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("WEM", "to.whom"), ("nie", "never"), ("gezeigt", "shown")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "nie"), ("feature", "exists"), ("order", "wh-first")] }

def ex24c : Datum :=
  { id := "kratzershimoyama2002_ex24c"
    source := ⟨"kratzer-shimoyama-2002", "(24c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat WEM niemand gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("WEM", "to.whom"), ("niemand", "nobody"), ("gezeigt", "shown")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "niemand"), ("feature", "exists"), ("order", "wh-first")] }

def ex24d : Datum :=
  { id := "kratzershimoyama2002_ex24d"
    source := ⟨"kratzer-shimoyama-2002", "(24d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat WEM fast jeder gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("WEM", "to.whom"), ("fast", "almost"), ("jeder", "everybody"), ("gezeigt", "shown")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "fast jeder"), ("feature", "exists"), ("order", "wh-first")] }

def ex24e : Datum :=
  { id := "kratzershimoyama2002_ex24e"
    source := ⟨"kratzer-shimoyama-2002", "(24e)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat WEM (irgend)jemand gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("WEM", "to.whom"), ("(irgend)jemand", "somebody"), ("gezeigt", "shown")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "(irgend)jemand"), ("feature", "exists"), ("order", "wh-first")] }

def ex12 : Datum :=
  { id := "kratzershimoyama2002_ex12"
    source := ⟨"kratzer-shimoyama-2002", "(12)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Niemand musste irgendjemand einladen."
    glossedTokens := [("Niemand", "nobody"), ("musste", "had.to"), ("irgendjemand", "irgend-one"), ("einladen", "invite")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "nobody"), ("intervener", "niemand"), ("feature", "exists")] }

def ex13 : Datum :=
  { id := "kratzershimoyama2002_ex13"
    source := ⟨"kratzer-shimoyama-2002", "(13)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ich bezweifle, dass sie je irgendjemand einladen durfte."
    glossedTokens := [("Ich", "I"), ("bezweifle", "doubt"), ("dass", "that"), ("sie", "she"), ("je", "ever"), ("irgendjemand", "irgend-one"), ("einladen", "invite"), ("durfte", "could")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "doubtVerb")] }

def ex16 : Datum :=
  { id := "kratzershimoyama2002_ex16"
    source := ⟨"kratzer-shimoyama-2002", "(16)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Du kannst dir irgendeins von diesen beiden Büchern leihen."
    glossedTokens := [("Du", "you"), ("kannst", "can"), ("dir", "you.DAT"), ("irgendeins", "irgend-one"), ("von", "of"), ("diesen", "those"), ("beiden", "two"), ("Büchern", "books"), ("leihen", "borrow")]
    context := "Two books are under discussion, an algebra book and a biology book."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "modalPossibility")] }

def ex17 : Datum :=
  { id := "kratzershimoyama2002_ex17"
    source := ⟨"kratzer-shimoyama-2002", "(17)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Du musst dir irgendeins von diesen beiden Büchern leihen."
    glossedTokens := [("Du", "you"), ("musst", "must"), ("dir", "you.DAT"), ("irgendeins", "irgend-one"), ("von", "of"), ("diesen", "those"), ("beiden", "two"), ("Büchern", "books"), ("leihen", "borrow")]
    context := "Two books are under discussion, an algebra book and a biology book."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "modalNecessity")] }

def ex18 : Datum :=
  { id := "kratzershimoyama2002_ex18"
    source := ⟨"kratzer-shimoyama-2002", "(18)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Du kannst dir auf keinen Fall irgendeins von diesen beiden Büchern leihen."
    glossedTokens := [("Du", "you"), ("kannst", "can"), ("dir", "you.DAT"), ("auf", "in"), ("keinen", "no"), ("Fall", "case"), ("irgendeins", "irgend-one"), ("von", "of"), ("diesen", "those"), ("beiden", "two"), ("Büchern", "books"), ("leihen", "borrow")]
    context := "Two books are under discussion, an algebra book and a biology book."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "nobody"), ("intervener", "auf keinen Fall"), ("feature", "exists")] }

def ex21 : Datum :=
  { id := "kratzershimoyama2002_ex21"
    source := ⟨"kratzer-shimoyama-2002", "(21)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ich hab’ nicht irgendwas gelesen."
    glossedTokens := [("Ich", "I"), ("hab’", "have"), ("nicht", "not"), ("irgendwas", "irgend-what"), ("gelesen", "read")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("context", "negation"), ("intervener", "nicht"), ("feature", "Neg")] }

def ex22 : Datum :=
  { id := "kratzershimoyama2002_ex22"
    source := ⟨"kratzer-shimoyama-2002", "(22)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Lehrer hat gefragt, ob Hans irgendein Buch gelesen hat."
    glossedTokens := [("Der", "the"), ("Lehrer", "teacher"), ("hat", "has"), ("gefragt", "asked"), ("ob", "whether"), ("Hans", "Hans"), ("irgendein", "irgend-one"), ("Buch", "book"), ("gelesen", "read"), ("hat", "has")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "question")] }

def all : List Datum := [ex23a, ex23b, ex23c, ex23d, ex23e, ex23f, ex23g, ex24a, ex24b, ex24c, ex24d, ex24e, ex12, ex13, ex16, ex17, ex18, ex21, ex22]

end KratzerShimoyama2002.Examples
