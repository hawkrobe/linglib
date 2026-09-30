module

public import Linglib.Data.Examples.Schema

/-!
# `Beavers2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Beavers2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beavers2010.Examples`.
-/

@[expose] public section

namespace Beavers2010.Examples

open Data.Examples

def ex_9a : Datum :=
  { id := "beavers2010_9a"
    source := ⟨"beavers-2010", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John loaded the hay onto the wagon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("direct", "theme")] }

def ex_9b : Datum :=
  { id := "beavers2010_9b"
    source := ⟨"beavers-2010", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John loaded the wagon with the hay."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("direct", "location")] }

def ex_10a : Datum :=
  { id := "beavers2010_10a"
    source := ⟨"beavers-2010", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim loaded the hay onto the wagon, but still needed a truck for the rest."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("diagnostic", "holistic effect")] }

def ex_18a : Datum :=
  { id := "beavers2010_18a"
    source := ⟨"beavers-2010", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John cut the diamond on the glass."
    glossedTokens := []
    context := "John moves a sharp-edged diamond forcefully into contact with a piece of glass."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("verb class", "cut/slice")] }

def ex_18b : Datum :=
  { id := "beavers2010_18b"
    source := ⟨"beavers-2010", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John cut the glass with the diamond."
    glossedTokens := []
    context := "Same scenario; the glass is damaged rather than the diamond."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("verb class", "cut/slice")] }

def ex_20a : Datum :=
  { id := "beavers2010_20a"
    source := ⟨"beavers-2010", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie cut the rope."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "cut")] }

def ex_20b : Datum :=
  { id := "beavers2010_20b"
    source := ⟨"beavers-2010", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie cut at the rope."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "cut")] }

def ex_21a : Datum :=
  { id := "beavers2010_21a"
    source := ⟨"beavers-2010", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie ate her cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "consumption")] }

def ex_21b : Datum :=
  { id := "beavers2010_21b"
    source := ⟨"beavers-2010", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie ate at her cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "consumption")] }

def ex_22a : Datum :=
  { id := "beavers2010_22a"
    source := ⟨"beavers-2010", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie hit Defarge."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "impact")] }

def ex_22b : Datum :=
  { id := "beavers2010_22b"
    source := ⟨"beavers-2010", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie hit at Defarge."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "impact")] }

def ex_24a : Datum :=
  { id := "beavers2010_24a"
    source := ⟨"beavers-2010", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John hit the fence with the stick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("contrast", "none")] }

def ex_29 : Datum :=
  { id := "beavers2010_29"
    source := ⟨"beavers-2010", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tailor lengthened the jeans to 32ins."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("degree", "quantized"), ("diagnostic", "telicity")] }

def ex_30 : Datum :=
  { id := "beavers2010_30"
    source := ⟨"beavers-2010", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tailor lengthened the jeans."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("degree", "nonquantized"), ("diagnostic", "telicity")] }

def ex_81a : Datum :=
  { id := "beavers2010_81a"
    source := ⟨"beavers-2010", "(81a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John climbed the stairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "traversal"), ("degree", "totally traversed")] }

def ex_81b : Datum :=
  { id := "beavers2010_81b"
    source := ⟨"beavers-2010", "(81b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John climbed up the stairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "traversal"), ("degree", "traversed")] }

def ex_88a : Datum :=
  { id := "beavers2010_88a"
    source := ⟨"beavers-2010", "(88a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim mailed London a ball."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := [("London as an agency (Scotland Yard reading)", .acceptable)]
    paperFeatures := [("alternation", "dative"), ("direct", "recipient")] }

def ex_88b : Datum :=
  { id := "beavers2010_88b"
    source := ⟨"beavers-2010", "(88b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim mailed a ball to London."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "dative"), ("oblique", "goal")] }

def all : List Datum := [ex_9a, ex_9b, ex_10a, ex_18a, ex_18b, ex_20a, ex_20b, ex_21a, ex_21b, ex_22a, ex_22b, ex_24a, ex_29, ex_30, ex_81a, ex_81b, ex_88a, ex_88b]

end Beavers2010.Examples
