module

public import Linglib.Data.Examples.Schema

/-!
# `Fox2018` — typed example data

Auto-generated from `Linglib/Data/Examples/Fox2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Fox2018.Examples`.
-/

@[expose] public section

namespace Fox2018.Examples

open Data.Examples

def ex16a : Datum :=
  { id := "fox2018_ex16a"
    source := ⟨"fox-2018", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tell me how fast you drove."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("family", "degree"), ("negation", "no"), ("modal", "no"), ("number", "na"), ("blocked", "no")] }

def ex16b : Datum :=
  { id := "fox2018_ex16b"
    source := ⟨"fox-hackl-2006", "negative islands"⟩
    reportedIn := some ⟨"fox-2018", "(16b)"⟩
    language := "stan1293"
    primaryText := "Tell me how fast you didn't drive."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("family", "degree"), ("negation", "yes"), ("modal", "no"), ("number", "na"), ("blocked", "yes")] }

def ex16c : Datum :=
  { id := "fox2018_ex16c"
    source := ⟨"fox-2018", "(16c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tell me how fast you are not allowed to drive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("family", "degree"), ("negation", "yes"), ("modal", "yes"), ("number", "na"), ("blocked", "no")] }

def ex24 : Datum :=
  { id := "fox2018_ex24"
    source := ⟨"fox-2018", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What are you required to read for this class? -- War and Peace or Brothers Karamazov."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > or", .acceptable), ("or > required", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "no"), ("modal", "yes"), ("number", "neutral"), ("blocked", "no")] }

def ex26 : Datum :=
  { id := "fox2018_ex26"
    source := ⟨"fox-2018", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did you not read for this class? -- War and Peace or Brothers Karamazov."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not > or", .unacceptable), ("or > not", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "yes"), ("modal", "no"), ("number", "neutral"), ("blocked", "yes")] }

def ex27 : Datum :=
  { id := "fox2018_ex27"
    source := ⟨"fox-2018", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What are you not allowed to read for this class? -- War and Peace or Brothers Karamazov."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not > or", .acceptable), ("or > not", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "yes"), ("modal", "yes"), ("number", "neutral"), ("blocked", "no")] }

def ex47a : Datum :=
  { id := "fox2018_ex47a"
    source := ⟨"fox-2018", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What are you required to read for this class? -- War and Peace or Brothers Karamazov."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > or", .acceptable), ("or > required", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "no"), ("modal", "yes"), ("number", "neutral"), ("blocked", "no")] }

def ex47b : Datum :=
  { id := "fox2018_ex47b"
    source := ⟨"fox-2018", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which books are you required to read for this class? -- The Russian books or the French books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > or", .acceptable), ("or > required", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "no"), ("modal", "yes"), ("number", "plural"), ("blocked", "no")] }

def ex48 : Datum :=
  { id := "fox2018_ex48"
    source := ⟨"fox-2018", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which book are you required to read for this class? -- War and Peace or Brothers Karamazov."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > or", .unacceptable), ("or > required", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "no"), ("modal", "yes"), ("number", "singular"), ("blocked", "yes")] }

def all : List Datum := [ex16a, ex16b, ex16c, ex24, ex26, ex27, ex47a, ex47b, ex48]

end Fox2018.Examples
