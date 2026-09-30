module

public import Linglib.Data.Examples.Schema

/-!
# `BhattTakahashi2011` — typed example data

Auto-generated from `Linglib/Data/Examples/BhattTakahashi2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BhattTakahashi2011.Examples`.
-/

@[expose] public section

namespace BhattTakahashi2011.Examples

open Data.Examples

def ex11a : LinguisticExample :=
  { id := "bhatttakahashi2011_ex11a"
    source := ⟨"bhatt-takahashi-2011", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people introduced him_i to Mary than to John_i's mother."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")] }

def ex11b : LinguisticExample :=
  { id := "bhatttakahashi2011_ex11b"
    source := ⟨"bhatt-takahashi-2011", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary introduced him_i to more people than John_i's mother."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "no")] }

def ex12a : LinguisticExample :=
  { id := "bhatttakahashi2011_ex12a"
    source := ⟨"bhatt-takahashi-2011", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people talked to him_i about Sally than about Peter_i's sister."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")] }

def ex12b : LinguisticExample :=
  { id := "bhatttakahashi2011_ex12b"
    source := ⟨"bhatt-takahashi-2011", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people talked to Sally about him_i than to Peter_i's sister."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "no")] }

def ex13a : LinguisticExample :=
  { id := "bhatttakahashi2011_ex13a"
    source := ⟨"bhatt-takahashi-2011", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people expect him_i to overtake Sally than Peter_i's sister."
    glossedTokens := []
    context := "Peter, Peter's sister, and Sally are taking part in a race; people are betting on their prospects."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")] }

def ex13b : LinguisticExample :=
  { id := "bhatttakahashi2011_ex13b"
    source := ⟨"bhatt-takahashi-2011", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people expect Sally to overtake him_i than Peter_i's sister."
    glossedTokens := []
    context := "Peter, Peter's sister, and Sally are taking part in a race; people are betting on their prospects."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "no")] }

def ex35 : LinguisticExample :=
  { id := "bhatttakahashi2011_ex35"
    source := ⟨"bhatt-takahashi-2011", "(35)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "Atif-ne Ravi-kii behen-kii foto-se us-ko Mohan-kii behen-kii foto zyaadaa baar dikhaa-ii."
    glossedTokens := [("Atif-ne", "Atif-ERG"), ("Ravi-kii", "Ravi-GEN"), ("behen-kii", "sister-GEN"), ("foto-se", "picture-than"), ("us-ko", "he-DAT"), ("Mohan-kii", "Mohan-GEN"), ("behen-kii", "sister-GEN"), ("foto", "picture"), ("zyaadaa", "more"), ("baar", "times"), ("dikhaa-ii", "show-PFV.F")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")] }

def ex43a : LinguisticExample :=
  { id := "bhatttakahashi2011_ex43a"
    source := ⟨"bhatt-takahashi-2011", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Craige assigned every first year student more papers than every second year student."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "scope"), ("qp_base_c_commands_degree_trace", "yes"), ("than_internal_scope", "unavailable")] }

def ex43b : LinguisticExample :=
  { id := "bhatttakahashi2011_ex43b"
    source := ⟨"bhatt-takahashi-2011", "(43b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Craige assigned more students every paper by Hellan than every paper by Klein."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "scope"), ("qp_base_c_commands_degree_trace", "no"), ("than_internal_scope", "available")] }

def ex40 : LinguisticExample :=
  { id := "bhatttakahashi2011_ex40"
    source := ⟨"bhatt-takahashi-2011", "(40)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "har syntax paper har semantics paper-se zyaadaa logõ-ne par.h-aa."
    glossedTokens := [("har", "every"), ("syntax", "syntax"), ("paper", "paper"), ("har", "every"), ("semantics", "semantics"), ("paper-se", "paper-than"), ("zyaadaa", "more"), ("logõ-ne", "people-ERG"), ("par.h-aa", "read-PFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "scope"), ("qp_base_c_commands_degree_trace", "no"), ("than_internal_scope", "unavailable")] }

def all : List LinguisticExample := [ex11a, ex11b, ex12a, ex12b, ex13a, ex13b, ex35, ex43a, ex43b, ex40]

end BhattTakahashi2011.Examples
