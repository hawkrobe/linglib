module

public import Linglib.Data.Examples.Schema

/-!
# `Gajewski2002` — typed example data

Auto-generated from `Linglib/Data/Examples/Gajewski2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gajewski2002.Examples`.
-/

@[expose] public section

namespace Gajewski2002.Examples

open Data.Examples

def ex4c : Datum :=
  { id := "gajewski2002_ex4c"
    source := ⟨"barwise-cooper-1981", "(4c)"⟩
    reportedIn := some ⟨"gajewski-2002", "(4c)"⟩
    language := "stan1293"
    primaryText := "There was everyone in the room."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "every"), ("grammatical", "no")] }

def ex30a : Datum :=
  { id := "gajewski2002_ex30a"
    source := ⟨"gajewski-2002", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is every new student."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "every"), ("grammatical", "no")] }

def ex5a : Datum :=
  { id := "gajewski2002_ex5a"
    source := ⟨"barwise-cooper-1981", "(5a)"⟩
    reportedIn := some ⟨"gajewski-2002", "(5a)"⟩
    language := "stan1293"
    primaryText := "There is a wolf at the door."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "some"), ("grammatical", "yes")] }

def ex5c : Datum :=
  { id := "gajewski2002_ex5c"
    source := ⟨"barwise-cooper-1981", "(5c)"⟩
    reportedIn := some ⟨"gajewski-2002", "(5c)"⟩
    language := "stan1293"
    primaryText := "There was someone in the room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "some"), ("grammatical", "yes")] }

def ex11a_every : Datum :=
  { id := "gajewski2002_ex11a_every"
    source := ⟨"von-fintel-1993", "(11a)"⟩
    reportedIn := some ⟨"gajewski-2002", "(11a)"⟩
    language := "stan1293"
    primaryText := "Every student but Bill passed the exam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "every"), ("grammatical", "yes")] }

def ex11a_no : Datum :=
  { id := "gajewski2002_ex11a_no"
    source := ⟨"von-fintel-1993", "(11a)"⟩
    reportedIn := some ⟨"gajewski-2002", "(11a)"⟩
    language := "stan1293"
    primaryText := "No student but Bill passed the exam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "no"), ("grammatical", "yes")] }

def ex11b : Datum :=
  { id := "gajewski2002_ex11b"
    source := ⟨"von-fintel-1993", "(11b)"⟩
    reportedIn := some ⟨"gajewski-2002", "(11b)"⟩
    language := "stan1293"
    primaryText := "Some students but Bill passed the exam."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "some"), ("grammatical", "no")] }

def ex34a : Datum :=
  { id := "gajewski2002_ex34a"
    source := ⟨"gajewski-2002", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every woman is a woman."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "everyIs"), ("determiner", "every"), ("grammatical", "yes")] }

def ex34b : Datum :=
  { id := "gajewski2002_ex34b"
    source := ⟨"gajewski-2002", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is smoking and John is not smoking."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "andNot"), ("determiner", "none"), ("grammatical", "yes")] }

def all : List Datum := [ex4c, ex30a, ex5a, ex5c, ex11a_every, ex11a_no, ex11b, ex34a, ex34b]

end Gajewski2002.Examples
