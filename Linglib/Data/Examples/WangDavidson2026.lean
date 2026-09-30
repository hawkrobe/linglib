module

public import Linglib.Data.Examples.Schema

/-!
# `WangDavidson2026` — typed example data

Auto-generated from `Linglib/Data/Examples/WangDavidson2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace WangDavidson2026.Examples`.
-/

@[expose] public section

namespace WangDavidson2026.Examples

def ex_1 : Datum :=
  { id := "wangdavidson2026_1"
    source := ⟨"wang-davidson-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's violin is expensive."
    glossedTokens := []
    context := "We don't know whether John has a violin."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("presupposition", "John has a violin"), ("projection", "projects")] }

def ex_2 : Datum :=
  { id := "wangdavidson2026_2"
    source := ⟨"wang-davidson-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's violin is expensive, and he has a good violin."
    glossedTokens := []
    context := "We don't know whether John has a violin."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("presupposition", "John has a violin"), ("projection", "projects"), ("direction", "right-to-left")] }

def ex_3 : Datum :=
  { id := "wangdavidson2026_3"
    source := ⟨"wang-davidson-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has a good violin, and his violin is expensive."
    glossedTokens := []
    context := "We don't know whether John has a violin."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("presupposition", "John has a violin"), ("projection", "filtered"), ("direction", "left-to-right")] }

def ex_4 : Datum :=
  { id := "wangdavidson2026_4"
    source := ⟨"wang-davidson-2026", "(13)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "我相信小张会来或者小王会来"
    glossedTokens := [("我", "I"), ("相信", "believe"), ("小张", "Zhang"), ("会", "will"), ("来", "come"), ("或者", "or"), ("小王", "Wang"), ("会", "will"), ("来", "come")]
    context := "Li said the sentence as a prediction. In fact, afterwards both Zhang and Wang came. Do you consider Li's prediction correct or incorrect?"
    judgment := .acceptable
    alternatives := []
    readings := [("inclusive", .acceptable), ("exclusive", .marginal)]
    paperFeatures := [("task", "norming"), ("monotonicity", "UE")] }

def ex_5 : Datum :=
  { id := "wangdavidson2026_5"
    source := ⟨"wang-davidson-2026", "(15)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "如果小李已经戒酒了或者从来不喝酒，那么他今晚的行为很合理。"
    glossedTokens := [("如果", "if"), ("小李", "Li"), ("已经", "already"), ("戒", "quit"), ("酒", "alcohol"), ("了", "PFV"), ("或者", "or"), ("从来", "always"), ("不", "NEG"), ("喝", "drink"), ("酒", "alcohol"), ("那么", "then"), ("他", "he"), ("今晚的", "tonight-DE"), ("行为", "behavior"), ("很", "very"), ("合理", "reasonable")]
    context := "I didn't know Li at all before, and I didn't know if he ever drank. At tonight's dinner gathering, most people drank, but Li didn't drink a drop, so I thought:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("condition", "PSFIRST"), ("monotonicity", "DE"), ("trigger", "jie"), ("context", "explicitly ignorant")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5]

end WangDavidson2026.Examples
