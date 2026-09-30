module

public import Linglib.Data.Examples.Schema

/-!
# `Zimmermann2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Zimmermann2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zimmermann2026.Examples`.
-/

@[expose] public section

namespace Zimmermann2026.Examples

open Data.Examples

def ex_12 : Datum :=
  { id := "zimmermann2026_12"
    source := ⟨"zimmermann-2026", "(12)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "John ya karanta wani littafi, amma ban san ko wanne ba ne."
    glossedTokens := [("John", "John"), ("ya", "3SG.M.PFV"), ("karanta", "read"), ("wani", "INDEF"), ("littafi", "book"), ("amma", "but"), ("ban", "NEG-1SG"), ("san", "know"), ("ko", "Q"), ("wanne", "which"), ("ba", "NEG"), ("ne", "COP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "sluicing antecedent")] }

def ex_13a : Datum :=
  { id := "zimmermann2026_13a"
    source := ⟨"zimmermann-2026", "(13a)"⟩
    reportedIn := some ⟨"zimmermann-2014", ""⟩
    language := "haus1257"
    primaryText := "Audù bà-i sàyi wani kiifii ba."
    glossedTokens := [("Audù", "Audu"), ("bà-i", "NEG-3SG.M"), ("sàyi", "buy"), ("wani", "INDEF"), ("kiifii", "fish"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("scope", "wide"), ("context", "Audu bought a lot of fish, but")] }

def ex_13b : Datum :=
  { id := "zimmermann2026_13b"
    source := ⟨"zimmermann-2026", "(13b)"⟩
    reportedIn := some ⟨"zimmermann-2014", ""⟩
    language := "haus1257"
    primaryText := "Audù bà-i sàyi wani kiifii ba."
    glossedTokens := [("Audù", "Audu"), ("bà-i", "NEG-3SG.M"), ("sàyi", "buy"), ("wani", "INDEF"), ("kiifii", "fish"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("scope", "narrow"), ("context", "the market was closed, so")] }

def ex_14 : Datum :=
  { id := "zimmermann2026_14"
    source := ⟨"zimmermann-2026", "(14)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Me-re-kɔ-tɔ mpaboa bí."
    glossedTokens := [("Me-re-kɔ-tɔ", "1SG-PROG-go-buy"), ("mpaboa", "shoes"), ("bí", "INDEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "specificity")] }

def ex_15 : Datum :=
  { id := "zimmermann2026_15"
    source := ⟨"zimmermann-2026", "(15)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Me-n-ni fish bí."
    glossedTokens := [("Me-n-ni", "1SG-NEG-eat"), ("fish", "fish"), ("bí", "INDEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("scope", "wide only")] }

def ex_17 : Datum :=
  { id := "zimmermann2026_17"
    source := ⟨"zimmermann-2026", "(17)"⟩
    reportedIn := none
    language := "gaaa1244"
    primaryText := "Nikasel ko kε e-wolo ko ni e-ma lε e-ya-aa."
    glossedTokens := [("Nikasel", "student"), ("ko", "INDEF"), ("kε", "take"), ("e-wolo", "3SG.POSS-letter"), ("ko", "INDEF"), ("ni", "REL"), ("e-ma", "3SG-write"), ("lε", "DEF"), ("e-ya-aa", "3SG-send-NEG")]
    context := "There were three students: Mary, Sue, and Joe. All of them wrote letters, but none of them sent all of them."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "ko"), ("reading", "existentially closed choice function")] }

def ex_18 : Datum :=
  { id := "zimmermann2026_18"
    source := ⟨"zimmermann-2026", "(18)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Papa bí nó bisa me me nɔma."
    glossedTokens := [("Papa", "man"), ("bí", "INDEF"), ("nó", "DEF"), ("bisa", "ask-PST"), ("me", "1SG"), ("me", "1SG"), ("nɔma", "number")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("co-occurrence", "INDEF and DEF")] }

def ex_19 : Datum :=
  { id := "zimmermann2026_19"
    source := ⟨"zimmermann-2026", "(19)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "tùuluu yaa fashèe"
    glossedTokens := [("tùuluu", "pot"), ("yaa", "3SG.PFV"), ("fashèe", "break")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("bare NP", "definite or indefinite")] }

def all : List Datum := [ex_12, ex_13a, ex_13b, ex_14, ex_15, ex_17, ex_18, ex_19]

end Zimmermann2026.Examples
