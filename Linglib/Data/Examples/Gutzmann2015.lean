module

public import Linglib.Data.Examples.Schema

/-!
# `Gutzmann2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Gutzmann2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gutzmann2015.Examples`.
-/

@[expose] public section

namespace Gutzmann2015.Examples

open Data.Examples

def ex_5_34 : Datum :=
  { id := "gutzmann2015_5_34"
    source := ⟨"gutzmann-2015", "(5.34)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wann kommt Peter nach Hause?"
    glossedTokens := [("Wann", "when"), ("kommt", "comes"), ("Peter", "Peter"), ("nach", "to"), ("Hause?", "home?")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "verbPosition"), ("sentenceType", "constituent"), ("embedding", "matrix")] }

def ex_5_35 : Datum :=
  { id := "gutzmann2015_5_35"
    source := ⟨"gutzmann-2015", "(5.35)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wann Peter nach Hause kommt?"
    glossedTokens := [("Wann", "when"), ("Peter", "Peter"), ("nach", "to"), ("Hause", "home"), ("kommt?", "comes?")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "verbPosition"), ("sentenceType", "constituent"), ("embedding", "insubordinated")] }

def ex_5_36a : Datum :=
  { id := "gutzmann2015_5_36a"
    source := ⟨"gutzmann-2015", "(5.36a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Mag er immer noch kubanische Zigarren?"
    glossedTokens := []
    context := "Stefan: Ich hab seit Jahren nichts mehr von Peter gehört. 'I haven't heard from Peter in years.' Heiner: Ich auch nicht. 'Me neither.' Stefan continues:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "hearerKnowledge"), ("sentenceType", "polar"), ("embedding", "matrix")] }

def ex_5_36b : Datum :=
  { id := "gutzmann2015_5_36b"
    source := ⟨"gutzmann-2015", "(5.36b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ob er immer noch kubanische Zigarren mag?"
    glossedTokens := []
    context := "Stefan: Ich hab seit Jahren nichts mehr von Peter gehört. 'I haven't heard from Peter in years.' Heiner: Ich auch nicht. 'Me neither.' Stefan continues:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "hearerKnowledge"), ("sentenceType", "polar"), ("embedding", "insubordinated")] }

def ex_5_44 : Datum :=
  { id := "gutzmann2015_5_44"
    source := ⟨"gutzmann-2015", "(5.44)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dass du nicht wieder die Schlüssel vergisst!"
    glossedTokens := [("Dass", "that"), ("du", "you"), ("nicht", "not"), ("wieder", "again"), ("die", "the"), ("Schlüssel", "keys"), ("vergisst!", "forget!")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "deonticMood"), ("sentenceType", "declarative"), ("embedding", "insubordinated")] }

def ex_5_46 : Datum :=
  { id := "gutzmann2015_5_46"
    source := ⟨"gutzmann-2015", "(5.46)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jim wohnt in Berlin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "epistemicMood"), ("sentenceType", "declarative"), ("embedding", "matrix")] }

def ex_5_81 : Datum :=
  { id := "gutzmann2015_5_81"
    source := ⟨"gutzmann-2015", "(5.81)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dass du nicht zu spät kommst!"
    glossedTokens := [("Dass", "that"), ("du", "you"), ("nicht", "not"), ("zu", "too"), ("spät", "late"), ("kommst!", "come!")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.6"), ("phenomenon", "deonticMood"), ("sentenceType", "declarative"), ("embedding", "insubordinated")] }

def ex_6_20 : Datum :=
  { id := "gutzmann2015_6_20"
    source := ⟨"gutzmann-2015", "(6.20)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Anna fährt ja morgen nach Hause."
    glossedTokens := [("Anna", "Anna"), ("fährt", "drives"), ("ja", "MP"), ("morgen", "tomorrow"), ("nach", "to"), ("Hause.", "home.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_21a : Datum :=
  { id := "gutzmann2015_6_21a"
    source := ⟨"gutzmann-2015", "(6.21a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ist Peter ja gekommen?"
    glossedTokens := [("Ist", "is"), ("Peter", "Peter"), ("ja", "MP"), ("gekommen?", "come?")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_21b : Datum :=
  { id := "gutzmann2015_6_21b"
    source := ⟨"gutzmann-2015", "(6.21b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wer kommt ja nach Tübingen?"
    glossedTokens := [("Wer", "who"), ("kommt", "comes"), ("ja", "MP"), ("nach", "to"), ("Tübingen?", "Tübingen?")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "constituent"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_22a : Datum :=
  { id := "gutzmann2015_6_22a"
    source := ⟨"gutzmann-2015", "(6.22a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Geh ja nicht zum Museumsball!"
    glossedTokens := [("Geh", "go"), ("ja", "MP"), ("nicht", "not"), ("zum", "to-the"), ("Museumsball!", "museum-ball!")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_22b : Datum :=
  { id := "gutzmann2015_6_22b"
    source := ⟨"gutzmann-2015", "(6.22b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dass du ja nicht dein ganzes Geld ausgibst!"
    glossedTokens := [("Dass", "that"), ("du", "you"), ("ja", "MP"), ("nicht", "not"), ("dein", "your"), ("ganzes", "entire"), ("Geld", "money"), ("ausgibst!", "spend!")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "insubordinated"), ("particle", "ja")] }

def ex_6_26 : Datum :=
  { id := "gutzmann2015_6_26"
    source := ⟨"gutzmann-2015", "(6.26)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Du kommst ja morgen um zehn?"
    glossedTokens := [("Du", "you"), ("kommst", "come"), ("ja", "MP"), ("morgen", "tomorrow"), ("um", "at"), ("zehn?", "ten?")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "checkQuestion"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_27 : Datum :=
  { id := "gutzmann2015_6_27"
    source := ⟨"gutzmann-2015", "(6.27)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wer will das Spiel ja nicht gewinnen?"
    glossedTokens := [("Wer", "who"), ("will", "want"), ("das", "the"), ("Spiel", "game"), ("ja", "MP"), ("nicht", "not"), ("gewinnen?", "win?")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "rhetoricalQuestion"), ("sentenceType", "constituent"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_28a : Datum :=
  { id := "gutzmann2015_6_28a"
    source := ⟨"gutzmann-2015", "(6.28a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hast du denn ein Auto?"
    glossedTokens := [("Hast", "have"), ("du", "you"), ("denn", "MP"), ("ein", "a"), ("Auto?", "car?")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_28b : Datum :=
  { id := "gutzmann2015_6_28b"
    source := ⟨"gutzmann-2015", "(6.28b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Warum lachst du denn?"
    glossedTokens := [("Warum", "why"), ("lachst", "laugh"), ("du", "you"), ("denn?", "MP?")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "constituent"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_29 : Datum :=
  { id := "gutzmann2015_6_29"
    source := ⟨"gutzmann-2015", "(6.29)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter ist denn ein Philosoph."
    glossedTokens := [("Peter", "Peter"), ("ist", "is"), ("denn", "MP"), ("ein", "a"), ("Philosoph.", "philosopher.")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_30 : Datum :=
  { id := "gutzmann2015_6_30"
    source := ⟨"gutzmann-2015", "(6.30)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Lass mich denn nicht alleine!"
    glossedTokens := [("Lass", "let"), ("mich", "me"), ("denn", "MP"), ("nicht", "not"), ("alleine!", "alone!")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_31 : Datum :=
  { id := "gutzmann2015_6_31"
    source := ⟨"gutzmann-2015", "(6.31)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dass du denn pünktlich nach Hause kommst!"
    glossedTokens := [("Dass", "that"), ("du", "you"), ("denn", "MP"), ("pünktlich", "on-time"), ("nach", "to"), ("Hause", "home"), ("kommst!", "come!")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "insubordinated"), ("particle", "denn")] }

def ex_6_32 : Datum :=
  { id := "gutzmann2015_6_32"
    source := ⟨"gutzmann-2015", "(6.32)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Du kommst denn morgen um zehn?"
    glossedTokens := [("Du", "you"), ("kommst", "come"), ("denn", "MP"), ("morgen", "tomorrow"), ("um", "at"), ("zehn?", "ten?")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "checkQuestion"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_33 : Datum :=
  { id := "gutzmann2015_6_33"
    source := ⟨"gutzmann-2015", "(6.33)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wer will das Spiel denn nicht gewinnen?"
    glossedTokens := [("Wer", "who"), ("will", "want"), ("das", "the"), ("Spiel", "game"), ("denn", "MP"), ("nicht", "not"), ("gewinnen?", "win?")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "rhetoricalQuestion"), ("sentenceType", "constituent"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_35 : Datum :=
  { id := "gutzmann2015_6_35"
    source := ⟨"gutzmann-2015", "(6.35)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hein ist wohl auf See."
    glossedTokens := [("Hein", "Hein"), ("ist", "is"), ("wohl", "MP"), ("auf", "at"), ("See.", "sea.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_36 : Datum :=
  { id := "gutzmann2015_6_36"
    source := ⟨"gutzmann-2015", "(6.36)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ist Hein wohl auf See?"
    glossedTokens := [("Ist", "is"), ("Hein", "Hein"), ("wohl", "MP"), ("auf", "at"), ("See?", "sea?")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_37a : Datum :=
  { id := "gutzmann2015_6_37a"
    source := ⟨"gutzmann-2015", "(6.37a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Komm wohl pünktlich nach Hause!"
    glossedTokens := [("Komm", "come"), ("wohl", "MP"), ("pünktlich", "on-time"), ("nach", "to"), ("Hause!", "home!")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_37b : Datum :=
  { id := "gutzmann2015_6_37b"
    source := ⟨"gutzmann-2015", "(6.37b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dass du wohl pünktlich nach Hause kommst!"
    glossedTokens := [("Dass", "that"), ("du", "you"), ("wohl", "MP"), ("pünktlich", "on-time"), ("nach", "to"), ("Hause", "home"), ("kommst!", "come!")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "insubordinated"), ("particle", "wohl")] }

def ex_6_38 : Datum :=
  { id := "gutzmann2015_6_38"
    source := ⟨"gutzmann-2015", "(6.38)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Bist du wohl still?"
    glossedTokens := [("Bist", "are"), ("du", "you"), ("wohl", "MP"), ("still?", "quiet?")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "indirectRequest"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_39 : Datum :=
  { id := "gutzmann2015_6_39"
    source := ⟨"gutzmann-2015", "(6.39)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Könnst du mir wohl das Salz reichen?"
    glossedTokens := [("Könnst", "could"), ("du", "you"), ("mir", "me"), ("wohl", "MP"), ("das", "the"), ("Salz", "salt"), ("reichen?", "pass?")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "indirectRequest"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_41 : Datum :=
  { id := "gutzmann2015_6_41"
    source := ⟨"gutzmann-2015", "(6.41)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Zeigen Sie mir wohl den Journalisten, der Gehaltseinbußen hinnimmt, um einem der vielen hundert Bewerber den Weg in eine Redaktion zu ebnen."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "rhetoricalRequest"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_108 : Datum :=
  { id := "gutzmann2015_6_108"
    source := ⟨"gutzmann-2015", "(6.108)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Geh wohl weg!"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.5.1"), ("phenomenon", "typeMismatch"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_117 : Datum :=
  { id := "gutzmann2015_6_117"
    source := ⟨"gutzmann-2015", "(6.117)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter ist wohl ein Philosoph."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.5.1"), ("phenomenon", "useConditions"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_124 : Datum :=
  { id := "gutzmann2015_6_124"
    source := ⟨"gutzmann-2015", "(6.124)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Georg ist ja ein Philosoph."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "useConditions"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_128 : Datum :=
  { id := "gutzmann2015_6_128"
    source := ⟨"gutzmann-2015", "(6.128)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ist Peter ja ein Philosoph?"
    glossedTokens := [("Ist", "is"), ("Peter", "Peter"), ("ja", "MP"), ("ein", "a"), ("Philosoph?", "philosopher?")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "useConditions"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_134 : Datum :=
  { id := "gutzmann2015_6_134"
    source := ⟨"gutzmann-2015", "(6.134)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hast du denn einen Führerschein?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "useConditions"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_138 : Datum :=
  { id := "gutzmann2015_6_138"
    source := ⟨"gutzmann-2015", "(6.138)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Entschuldigung, könnten Sie mir denn sagen, wo's hier nach Klein-Heubach geht?"
    glossedTokens := [("Entschuldigung,", "excuse"), ("könnten", "could"), ("Sie", "you"), ("mir", "me"), ("denn", "MP"), ("sagen,", "say"), ("wo's", "where-it"), ("hier", "here"), ("nach", "to"), ("Klein-Heubach", "Klein-Heubach"), ("geht?", "goes?")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "externalMotivation"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_139 : Datum :=
  { id := "gutzmann2015_6_139"
    source := ⟨"gutzmann-2015", "(6.139)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was schreibst du denn da?"
    glossedTokens := [("Was", "what"), ("schreibst", "write"), ("du", "you"), ("denn", "MP"), ("da?", "there?")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "externalMotivation"), ("sentenceType", "constituent"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_141 : Datum :=
  { id := "gutzmann2015_6_141"
    source := ⟨"gutzmann-2015", "(6.141)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Geh denn weg!"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "useConditions"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "denn")] }

def all : List Datum := [ex_5_34, ex_5_35, ex_5_36a, ex_5_36b, ex_5_44, ex_5_46, ex_5_81, ex_6_20, ex_6_21a, ex_6_21b, ex_6_22a, ex_6_22b, ex_6_26, ex_6_27, ex_6_28a, ex_6_28b, ex_6_29, ex_6_30, ex_6_31, ex_6_32, ex_6_33, ex_6_35, ex_6_36, ex_6_37a, ex_6_37b, ex_6_38, ex_6_39, ex_6_41, ex_6_108, ex_6_117, ex_6_124, ex_6_128, ex_6_134, ex_6_138, ex_6_139, ex_6_141]

end Gutzmann2015.Examples
