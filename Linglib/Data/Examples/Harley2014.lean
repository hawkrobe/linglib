module

public import Linglib.Data.Examples.Schema

/-!
# `Harley2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Harley2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Harley2014.Examples`.
-/

@[expose] public section

namespace Harley2014.Examples

open Data.Examples

def ex3a : Datum :=
  { id := "harley2014_ex3a"
    source := ⟨"harley-2014", "(3a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "vuite~tenne"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "vuite"), ("pluralForm", "tenne"), ("conditioner", "subject")] }

def ex3b : Datum :=
  { id := "harley2014_ex3b"
    source := ⟨"harley-2014", "(3b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "siika~saka"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "siika"), ("pluralForm", "saka"), ("conditioner", "subject")] }

def ex3c : Datum :=
  { id := "harley2014_ex3c"
    source := ⟨"harley-2014", "(3c)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "weama~rehte"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "weama"), ("pluralForm", "rehte"), ("conditioner", "subject")] }

def ex3d : Datum :=
  { id := "harley2014_ex3d"
    source := ⟨"harley-2014", "(3d)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "kivake~kiime"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "kivake"), ("pluralForm", "kiime"), ("conditioner", "subject")] }

def ex3e : Datum :=
  { id := "harley2014_ex3e"
    source := ⟨"harley-2014", "(3e)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "vo'e~to'e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "vo'e"), ("pluralForm", "to'e"), ("conditioner", "subject")] }

def ex3f : Datum :=
  { id := "harley2014_ex3f"
    source := ⟨"harley-2014", "(3f)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "weye~kaate"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "weye"), ("pluralForm", "kaate"), ("conditioner", "subject")] }

def ex3g : Datum :=
  { id := "harley2014_ex3g"
    source := ⟨"harley-2014", "(3g)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "mea~sua"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "mea"), ("pluralForm", "sua"), ("conditioner", "object")] }

def ex6a : Datum :=
  { id := "harley2014_ex6a"
    source := ⟨"harley-2014", "(6a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Aapo aman vuite-k."
    glossedTokens := [("Aapo", "3sg"), ("aman", "there"), ("vuite-k.", "run.sg-prf")]
    context := ""
    judgment := .acceptable
    alternatives := [("Vempo aman vuite-k.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("subjectNumber", "singular")] }

def ex6b : Datum :=
  { id := "harley2014_ex6b"
    source := ⟨"harley-2014", "(6b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Vempo aman tenne-k"
    glossedTokens := [("Vempo", "3pl"), ("aman", "there"), ("tenne-k", "run.pl-prf")]
    context := ""
    judgment := .acceptable
    alternatives := [("Aapo aman tenne-k.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("subjectNumber", "plural")] }

def ex26a : Datum :=
  { id := "harley2014_ex26a"
    source := ⟨"harley-2014", "(26a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Aapo weye"
    glossedTokens := [("Aapo", "3sg"), ("weye", "walk.sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "rootSuppletion"), ("subjectNumber", "singular")] }

def ex26b : Datum :=
  { id := "harley2014_ex26b"
    source := ⟨"harley-2014", "(26b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Vempo kaate"
    glossedTokens := [("Vempo", "3pl"), ("kaate", "walk.pl")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "rootSuppletion"), ("subjectNumber", "plural")] }

def ex27a : Datum :=
  { id := "harley2014_ex27a"
    source := ⟨"harley-2014", "(27a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Aapo/Vempo uka koowi-ta mea-k"
    glossedTokens := [("Aapo/Vempo", "3sg/3pl"), ("uka", "the.sg"), ("koowi-ta", "pig-ACC.sg"), ("mea-k", "kill.sg-PRF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "rootSuppletion"), ("objectNumber", "singular")] }

def ex27b : Datum :=
  { id := "harley2014_ex27b"
    source := ⟨"harley-2014", "(27b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Aapo/Vempo ume kowi-m sua-k"
    glossedTokens := [("Aapo/Vempo", "3sg/3pl"), ("ume", "the.pl"), ("kowi-m", "pig-pl"), ("sua-k", "kill.pl-PRF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "rootSuppletion"), ("objectNumber", "plural")] }

def ex29a : Datum :=
  { id := "harley2014_ex29a"
    source := ⟨"harley-2014", "(29a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Hoan Maria-ta vicha-k"
    glossedTokens := [("Hoan", "Juan.nom"), ("Maria-ta", "Maria-acc"), ("vicha-k", "see-prf")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "case")] }

def ex29b : Datum :=
  { id := "harley2014_ex29b"
    source := ⟨"harley-2014", "(29b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Maria aman vicha-wa-k"
    glossedTokens := [("Maria", "Maria.nom"), ("aman", "there"), ("vicha-wa-k", "see-pass-prf")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "case")] }

def ex30a : Datum :=
  { id := "harley2014_ex30a"
    source := ⟨"harley-2014", "(30a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "U'u maaso uusi-m yi'i-ria-k"
    glossedTokens := [("U'u", "the"), ("maaso", "deer.dancer"), ("uusi-m", "children-pl"), ("yi'i-ria-k", "dance-APPL-PRF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "unergative")] }

def ex30b : Datum :=
  { id := "harley2014_ex30b"
    source := ⟨"harley-2014", "(30b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Inepo Hose-ta pueta-ta eta-ria-k"
    glossedTokens := [("Inepo", "1sg"), ("Hose-ta", "Jose-ACC"), ("pueta-ta", "door-ACC"), ("eta-ria-k", "close-APPL-PRF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "transitive")] }

def ex31 : Datum :=
  { id := "harley2014_ex31"
    source := ⟨"harley-2014", "(31)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Uu tasa Maria-ta hamte-ria-k"
    glossedTokens := [("Uu", "the"), ("tasa", "cup.nom"), ("Maria-ta", "Maria-ACC"), ("hamte-ria-k", "break.intr-APPL-PRF")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "unaccusative")] }

def ex32a : Datum :=
  { id := "harley2014_ex32a"
    source := ⟨"harley-2014", "(32a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Santos Maria-ta San Xavierle-u weye-ria"
    glossedTokens := [("Santos", "Santos"), ("Maria-ta", "Maria-ACC"), ("San", "San"), ("Xavierle-u", "Xavier-to"), ("weye-ria", "go-APPL")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "suppletiveIntransitive")] }

def ex32b : Datum :=
  { id := "harley2014_ex32b"
    source := ⟨"harley-2014", "(32b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Santos Maria-ta vetchi'ivo San Xavierle-u weye"
    glossedTokens := [("Santos", "Santos"), ("Maria-ta", "Maria-ACC"), ("vetchi'ivo", "for"), ("San", "San"), ("Xavierle-u", "Xavier-to"), ("weye", "go")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "suppletiveIntransitive")] }

def exfn33_i : Datum :=
  { id := "harley2014_exfn33-i"
    source := ⟨"harley-2014", "(fn33-i)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Santos Hose-ta koowi-ta/koowi-m mea/sua-ria-k."
    glossedTokens := [("Santos", "Santos"), ("Hose-ta", "Jose-ACC"), ("koowi-ta/koowi-m", "pig-ACC/pig-PL"), ("mea/sua-ria-k.", "kill.sg/kill.pl-APPL-PRF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "suppletiveTransitive")] }

def all : List Datum := [ex3a, ex3b, ex3c, ex3d, ex3e, ex3f, ex3g, ex6a, ex6b, ex26a, ex26b, ex27a, ex27b, ex29a, ex29b, ex30a, ex30b, ex31, ex32a, ex32b, exfn33_i]

end Harley2014.Examples
