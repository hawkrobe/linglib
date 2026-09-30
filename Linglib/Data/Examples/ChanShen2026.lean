module

public import Linglib.Data.Examples.Schema

/-!
# `ChanShen2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ChanShen2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ChanShen2026.Examples`.
-/

@[expose] public section

namespace ChanShen2026.Examples

open Data.Examples

def ex1a : LinguisticExample :=
  { id := "chanshen2026_ex1a"
    source := ⟨"chan-shen-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who loves what the hell?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "theHell"), ("strategy", "inSitu"), ("interveners", "1")] }

def ex1b : LinguisticExample :=
  { id := "chanshen2026_ex1b"
    source := ⟨"chan-shen-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who the hell loves what?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "theHell"), ("strategy", "full"), ("interveners", "0")] }

def ex4a : LinguisticExample :=
  { id := "chanshen2026_ex4a"
    source := ⟨"chan-shen-2026", "(4a)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "What you think Natalie is baking at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("condition", "Wh-Long"), ("strategy", "full")] }

def ex4b : LinguisticExample :=
  { id := "chanshen2026_ex4b"
    source := ⟨"chan-shen-2026", "(4b)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "What the hell you think Natalie is baking at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("condition", "WhHell-Long"), ("modifier", "theHell"), ("strategy", "full"), ("interveners", "0")] }

def ex4c : LinguisticExample :=
  { id := "chanshen2026_ex4c"
    source := ⟨"chan-shen-2026", "(4c)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You think Natalie is baking what at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("condition", "Wh-Situ"), ("strategy", "inSitu")] }

def ex4d : LinguisticExample :=
  { id := "chanshen2026_ex4d"
    source := ⟨"chan-shen-2026", "(4d)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You think Natalie is baking what the hell at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("condition", "WhHell-Situ"), ("modifier", "theHell"), ("strategy", "inSitu"), ("interveners", "0")] }

def ex6c : LinguisticExample :=
  { id := "chanshen2026_ex6c"
    source := ⟨"chan-shen-2026", "(6c)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You think what Natalie is baking at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("condition", "Wh-Partial"), ("strategy", "partial")] }

def ex6d : LinguisticExample :=
  { id := "chanshen2026_ex6d"
    source := ⟨"chan-shen-2026", "(6d)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You think what the hell Natalie is baking at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("condition", "WhHell-Partial"), ("modifier", "theHell"), ("strategy", "partial"), ("interveners", "0")] }

def ex11a : LinguisticExample :=
  { id := "chanshen2026_ex11a"
    source := ⟨"sato-ngui-2017", "(11a)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(11a)"⟩
    language := "sing1272"
    primaryText := "What John like the man that think Mary eat?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "full"), ("island", "complexNP")] }

def ex11b : LinguisticExample :=
  { id := "chanshen2026_ex11b"
    source := ⟨"sato-ngui-2017", "(11b)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(11b)"⟩
    language := "sing1272"
    primaryText := "John like the man that think Mary eat what?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("island", "complexNP")] }

def ex15 : LinguisticExample :=
  { id := "chanshen2026_ex15"
    source := ⟨"sato-ngui-2017", "(15)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(15)"⟩
    language := "sing1272"
    primaryText := "John like the man that think what Mary eat?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "partial"), ("island", "complexNP")] }

def ex17a : LinguisticExample :=
  { id := "chanshen2026_ex17a"
    source := ⟨"cole-hermon-1998", "(17a)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(17a)"⟩
    language := "stan1306"
    primaryText := "Kamu sayang perempuan yang Ali fikir yang telah makan apa?"
    glossedTokens := [("Kamu", "you"), ("sayang", "love"), ("perempuan", "woman"), ("yang", "that"), ("Ali", "Ali"), ("fikir", "think"), ("yang", "that"), ("telah", "already"), ("makan", "eat"), ("apa", "what")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("island", "complexNP")] }

def ex17b : LinguisticExample :=
  { id := "chanshen2026_ex17b"
    source := ⟨"cole-hermon-1998", "(17b)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(17b)"⟩
    language := "stan1306"
    primaryText := "Kamu sayang perempuan yang Ali fikir apa yang telah makan?"
    glossedTokens := [("Kamu", "you"), ("sayang", "love"), ("perempuan", "woman"), ("yang", "that"), ("Ali", "Ali"), ("fikir", "think"), ("apa", "what"), ("yang", "that"), ("telah", "already"), ("makan", "eat")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "partial"), ("island", "complexNP")] }

def ex19 : LinguisticExample :=
  { id := "chanshen2026_ex19"
    source := ⟨"chou-2012", "(19)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(19)"⟩
    language := "mand1415"
    primaryText := "Ni renwei Lisi daodi xihuan shenme?"
    glossedTokens := [("Ni", "you"), ("renwei", "think"), ("Lisi", "Lisi"), ("daodi", "THE-HELL"), ("xihuan", "like"), ("shenme", "what")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "daodi"), ("strategy", "inSitu"), ("interveners", "0")] }

def ex22a : LinguisticExample :=
  { id := "chanshen2026_ex22a"
    source := ⟨"chan-shen-2026", "(22a)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You that time heard that who went hospital for surgery ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("role", "subject")] }

def ex22b : LinguisticExample :=
  { id := "chanshen2026_ex22b"
    source := ⟨"chan-shen-2026", "(22b)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You that time heard that who the hell went hospital for surgery ah?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "theHell"), ("strategy", "inSitu"), ("role", "subject"), ("interveners", "0")] }

def ex25a : LinguisticExample :=
  { id := "chanshen2026_ex25a"
    source := ⟨"chan-shen-2026", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who the hell is in love with who?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "theHell"), ("strategy", "full"), ("interveners", "0")] }

def ex26a : LinguisticExample :=
  { id := "chanshen2026_ex26a"
    source := ⟨"den-dikken-giannakidou-2002", "(71a)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(26a)"⟩
    language := "stan1293"
    primaryText := "Who is in love with who the hell?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "theHell"), ("strategy", "inSitu"), ("interveners", "1")] }

def all : List LinguisticExample := [ex1a, ex1b, ex4a, ex4b, ex4c, ex4d, ex6c, ex6d, ex11a, ex11b, ex15, ex17a, ex17b, ex19, ex22a, ex22b, ex25a, ex26a]

end ChanShen2026.Examples
