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
    source := ⟨"rooth-1992", "(3a), p. 77"⟩
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
    source := ⟨"rooth-1992", "(3b), p. 77"⟩
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
    source := ⟨"rooth-1992", "(23Qa)/(23Aa), p. 84"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "MARY cut Bill down to size"
    discourseSegments := []
    glossedTokens := []
    translation := "MARY cut Bill down to size"
    context := "Who cut Bill down to size?"
    judgment := .acceptable
    alternatives := [("MARY cut Bill down to size", .acceptable), ("MONIQUE cut Bill down to size", .acceptable), ("MICHIKO cut Bill down to size", .acceptable)]
    readings := []
    paperFeatures := [("focus", "Mary"), ("fip_application", "qaCongruence")]
    comment := "Rooth's (23): the solid line links (23Qa) to the subject-focus answer (23Aa). Subject focus matches the wh-position, so the answer is congruent. The alternatives field carries the subject-varying focus-alternative set from the left column of (24), each member a congruent answer to (23Qa)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def qa_incongruent : LinguisticExample :=
  { id := "rooth1992_qa_incongruent"
    source := ⟨"rooth-1992", "(23Ab) as answer to (23Qa), p. 84"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "#Mary cut BILL down to size"
    discourseSegments := []
    glossedTokens := []
    translation := "Mary cut BILL down to size"
    context := "Who cut Bill down to size?"
    judgment := .unacceptable
    alternatives := [("#Mary cut BILL down to size", .unacceptable), ("#Mary cut BJÖRN down to size", .unacceptable), ("#Mary cut BORIS down to size", .unacceptable)]
    readings := []
    paperFeatures := [("focus", "Bill"), ("fip_application", "qaCongruence")]
    comment := "Rooth's (23): the dotted line marks (23Ab) as an inappropriate answer to (23Qa). Object focus does not match the wh-position, so the answer is infelicitous (#). The alternatives field carries the object-varying set from the right column of (24); in this context every member is equally incongruent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [only_bill, only_sue, qa_congruent, qa_incongruent]

end Rooth1992.Examples
