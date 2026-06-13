import Linglib.Data.Examples.Schema

/-!
# `Rooth1992` — typed example data

Auto-generated from `Linglib/Data/Examples/Rooth1992.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rooth1992.Examples`.
-/

namespace Rooth1992.Examples

open Data.Examples

def only_bill : LinguisticExample :=
  { id := "rooth1992_only_bill"
    source := ⟨"rooth-1992", "UNVERIFIED §2.1 — only with focus on the direct object"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary only introduced BILL to Sue"
    discourseSegments := []
    glossedTokens := []
    translation := "Mary only introduced BILL to Sue"
    context := ""
    judgment := .acceptable
    alternatives := [("Mary introduced Bill to Sue", .acceptable), ("Mary introduced John to Sue", .acceptable), ("Mary introduced Tom to Sue", .acceptable), ("Mary introduced Fred to Sue", .acceptable)]
    readings := []
    paperFeatures := [("focus", "Bill"), ("fip_application", "focusingAdverb")]
    comment := "Migrated from Phenomena/Focus/Basic.lean roothOnlyBill. Focus on 'Bill' makes only quantify over alternative introducees: Bill is the only person Mary introduced to Sue. The alternatives field carries the Roothian focus-alternative set {introduce(m,x,s) : x in {Bill, John, Tom, Fred}} as substituted prejacents; the alternative individuals beyond Bill are illustrative, not verified against the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def only_sue : LinguisticExample :=
  { id := "rooth1992_only_sue"
    source := ⟨"rooth-1992", "UNVERIFIED §2.1 — only with focus on the recipient"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary only introduced Bill to SUE"
    discourseSegments := []
    glossedTokens := []
    translation := "Mary only introduced Bill to SUE"
    context := ""
    judgment := .acceptable
    alternatives := [("Mary introduced Bill to Sue", .acceptable), ("Mary introduced Bill to Jane", .acceptable), ("Mary introduced Bill to Ann", .acceptable), ("Mary introduced Bill to Beth", .acceptable)]
    readings := []
    paperFeatures := [("focus", "Sue"), ("fip_application", "focusingAdverb")]
    comment := "Migrated from Phenomena/Focus/Basic.lean roothOnlySue. Same string as rooth1992_only_bill modulo focus position: focus on 'Sue' makes only exclude alternative recipients instead of alternative introducees. The alternatives field carries the Roothian focus-alternative set {introduce(m,b,y) : y in {Sue, Jane, Ann, Beth}}; the alternative individuals beyond Sue are illustrative, not verified against the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def qa_congruent : LinguisticExample :=
  { id := "rooth1992_qa_congruent"
    source := ⟨"rooth-1992", "UNVERIFIED §4 — congruent answer (subject focus)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "FRED ate the beans"
    discourseSegments := []
    glossedTokens := []
    translation := "FRED ate the beans"
    context := "Who ate the beans?"
    judgment := .acceptable
    alternatives := [("FRED ate the beans", .acceptable), ("MARY ate the beans", .acceptable), ("BILL ate the beans", .acceptable), ("SUE ate the beans", .acceptable)]
    readings := []
    paperFeatures := [("focus", "Fred"), ("fip_application", "qaCongruence")]
    comment := "Migrated from Phenomena/Focus/Basic.lean qaCongruent. Subject focus matches the wh-position of the question, so the answer is congruent. The alternatives field carries the subject-varying focus-alternative set, each member a congruent answer to the question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def qa_incongruent : LinguisticExample :=
  { id := "rooth1992_qa_incongruent"
    source := ⟨"rooth-1992", "UNVERIFIED §4 — incongruent answer (object focus)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "#Fred ate the BEANS"
    discourseSegments := []
    glossedTokens := []
    translation := "Fred ate the BEANS"
    context := "Who ate the beans?"
    judgment := .unacceptable
    alternatives := [("#Fred ate the BEANS", .unacceptable), ("#Fred ate the RICE", .unacceptable), ("#Fred ate the PASTA", .unacceptable), ("#Fred ate the SALAD", .unacceptable)]
    readings := []
    paperFeatures := [("focus", "beans"), ("fip_application", "qaCongruence")]
    comment := "Migrated from Phenomena/Focus/Basic.lean qaIncongruent. Object focus does not match the wh-position of the question, so the answer is infelicitous (#). The alternatives field carries the object-varying focus-alternative set; in this context every member is equally incongruent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [only_bill, only_sue, qa_congruent, qa_incongruent]

end Rooth1992.Examples
