module

public import Linglib.Data.Examples.Schema

/-!
# `Hyman2003` — typed example data

Auto-generated from `Linglib/Data/Examples/Hyman2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hyman2003.Examples`.
-/

@[expose] public section

namespace Hyman2003.Examples

open Data.Examples

def ex_2a_cr : LinguisticExample :=
  { id := "hyman2003_2a_cr"
    source := ⟨"hyman-mchombo-1992", "(2a)"⟩
    reportedIn := some ⟨"hyman-2003", "(2a)"⟩
    language := "nyan1308"
    primaryText := "mang-its-an-"
    glossedTokens := [("mang-its-an-", "tie-CAUS-REC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "CR"), ("suffixes", "CR")] }

def ex_2a_rc : LinguisticExample :=
  { id := "hyman2003_2a_rc"
    source := ⟨"hyman-mchombo-1992", "(2a)"⟩
    reportedIn := some ⟨"hyman-2003", "(2a)"⟩
    language := "nyan1308"
    primaryText := "mang-its-an-"
    glossedTokens := [("mang-its-an-", "tie-CAUS-REC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "RC"), ("suffixes", "CR")] }

def ex_2b_rc : LinguisticExample :=
  { id := "hyman2003_2b_rc"
    source := ⟨"hyman-mchombo-1992", "(2b)"⟩
    reportedIn := some ⟨"hyman-2003", "(2b)"⟩
    language := "nyan1308"
    primaryText := "mang-an-its-"
    glossedTokens := [("mang-an-its-", "tie-REC-CAUS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "RC"), ("suffixes", "RC")] }

def ex_2b_cr : LinguisticExample :=
  { id := "hyman2003_2b_cr"
    source := ⟨"hyman-mchombo-1992", "(2b)"⟩
    reportedIn := some ⟨"hyman-2003", "(2b)"⟩
    language := "nyan1308"
    primaryText := "mang-an-its-"
    glossedTokens := [("mang-an-its-", "tie-REC-CAUS")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "CR"), ("suffixes", "RC")] }

def ex_3a : LinguisticExample :=
  { id := "hyman2003_3a"
    source := ⟨"hyman-2003", "(3a)"⟩
    reportedIn := some ⟨"hyman-2003", "(3a)"⟩
    language := "nyan1308"
    primaryText := "alenjé a-ku-líl-íts-il-a mwaná ndodo"
    glossedTokens := [("alenjé", "hunters"), ("a-ku-líl-íts-il-a", "3pl-prog-cry-CAUS-APP-fv"), ("mwaná", "child"), ("ndodo", "sticks")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "cry"), ("scope", "CA"), ("suffixes", "CA")] }

def ex_3b : LinguisticExample :=
  { id := "hyman2003_3b"
    source := ⟨"hyman-2003", "(3b)"⟩
    reportedIn := some ⟨"hyman-2003", "(3b)"⟩
    language := "nyan1308"
    primaryText := "alenjé a-ku-tákás-its-il-a mkází mthíko"
    glossedTokens := [("alenjé", "hunters"), ("a-ku-tákás-its-il-a", "3pl-prog-stir-CAUS-APP-fv"), ("mkází", "woman"), ("mthíko", "spoon")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "stir"), ("scope", "AC"), ("suffixes", "CA")] }

def ex_7b : LinguisticExample :=
  { id := "hyman2003_7b"
    source := ⟨"hyman-2003", "(7b)"⟩
    reportedIn := some ⟨"hyman-2003", "(7b)"⟩
    language := "nyan1308"
    primaryText := "mang-il-its-"
    glossedTokens := [("mang-il-its-", "tie-APP-CAUS")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "AC"), ("suffixes", "AC")] }

def ex_8 : LinguisticExample :=
  { id := "hyman2003_8"
    source := ⟨"hyman-2003", "(8)"⟩
    reportedIn := some ⟨"hyman-2003", "(8)"⟩
    language := "nyan1308"
    primaryText := "mang-its-il-an-"
    glossedTokens := [("mang-its-il-an-", "tie-CAUS-APP-REC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "RAC"), ("suffixes", "CAR")] }

def ex_8_star : LinguisticExample :=
  { id := "hyman2003_8_star"
    source := ⟨"hyman-2003", "(8)"⟩
    reportedIn := some ⟨"hyman-2003", "(8)"⟩
    language := "nyan1308"
    primaryText := "mang-an-il-its-"
    glossedTokens := [("mang-an-il-its-", "tie-REC-APP-CAUS")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "RAC"), ("suffixes", "RAC")] }

def ex_13a : LinguisticExample :=
  { id := "hyman2003_13a"
    source := ⟨"hyman-2003", "(13a)"⟩
    reportedIn := some ⟨"hyman-2003", "(13a)"⟩
    language := "nyan1308"
    primaryText := "mang-il-an-"
    glossedTokens := [("mang-il-an-", "tie-APP-REC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "AR"), ("suffixes", "AR")] }

def ex_13b : LinguisticExample :=
  { id := "hyman2003_13b"
    source := ⟨"hyman-2003", "(13b)"⟩
    reportedIn := some ⟨"hyman-2003", "(13b)"⟩
    language := "nyan1308"
    primaryText := "mang-an-il-"
    glossedTokens := [("mang-an-il-", "tie-REC-APP")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "RA"), ("suffixes", "RA")] }

def ex_13c : LinguisticExample :=
  { id := "hyman2003_13c"
    source := ⟨"hyman-2003", "(13c)"⟩
    reportedIn := some ⟨"hyman-2003", "(13c)"⟩
    language := "nyan1308"
    primaryText := "mang-il-an-"
    glossedTokens := [("mang-il-an-", "tie-APP-REC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "RA"), ("suffixes", "AR")] }

def ex_13d : LinguisticExample :=
  { id := "hyman2003_13d"
    source := ⟨"hyman-2003", "(13d)"⟩
    reportedIn := some ⟨"hyman-2003", "(13d)"⟩
    language := "nyan1308"
    primaryText := "mang-an-il-an-"
    glossedTokens := [("mang-an-il-an-", "tie-REC-APP-REC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "RA"), ("suffixes", "RAR")] }

def ex_17b : LinguisticExample :=
  { id := "hyman2003_17b"
    source := ⟨"hyman-2003", "(17b)"⟩
    reportedIn := some ⟨"hyman-2003", "(17b)"⟩
    language := "nyan1308"
    primaryText := "mang-il-an-il-"
    glossedTokens := [("mang-il-an-il-", "tie-APP-REC-APP")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "RA"), ("suffixes", "ARA")] }

def ex_18a : LinguisticExample :=
  { id := "hyman2003_18a"
    source := ⟨"hyman-2003", "(18a)"⟩
    reportedIn := some ⟨"hyman-2003", "(18a)"⟩
    language := "nyan1308"
    primaryText := "mang-il-il-"
    glossedTokens := [("mang-il-il-", "tie-APP-APP")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "AA"), ("suffixes", "AA")] }

def ex_18b : LinguisticExample :=
  { id := "hyman2003_18b"
    source := ⟨"hyman-2003", "(18b)"⟩
    reportedIn := some ⟨"hyman-2003", "(18b)"⟩
    language := "nyan1308"
    primaryText := "mang-its-its-"
    glossedTokens := [("mang-its-its-", "tie-CAUS-CAUS")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("root", "tie"), ("scope", "CC"), ("suffixes", "CC")] }

def ex_20a : LinguisticExample :=
  { id := "hyman2003_20a"
    source := ⟨"hyman-2003", "(20a)"⟩
    reportedIn := some ⟨"hyman-2003", "(20a)"⟩
    language := "chim1312"
    primaryText := "luti, Ji mw-andik-ish-iriz-e mwa:na xati"
    glossedTokens := [("luti", "stick"), ("Ji", "Ji"), ("mw-andik-ish-iriz-e", "he-write-CAUS-APP"), ("mwa:na", "child"), ("xati", "letter")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "write"), ("scope", "CA"), ("suffixes", "CA")] }

def ex_20b : LinguisticExample :=
  { id := "hyman2003_20b"
    source := ⟨"hyman-2003", "(20b)"⟩
    reportedIn := some ⟨"hyman-2003", "(20b)"⟩
    language := "chim1312"
    primaryText := "skuñi, Ari m-pik-ish-iriz-e: muke ṉama"
    glossedTokens := [("skuñi", "firewood"), ("Ari", "Ali"), ("m-pik-ish-iriz-e:", "he-cook-CAUS-APP"), ("muke", "woman"), ("ṉama", "meat")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "cook"), ("scope", "AC"), ("suffixes", "CA")] }

def ex_22a : LinguisticExample :=
  { id := "hyman2003_22a"
    source := ⟨"hyman-2003", "(22a)"⟩
    reportedIn := some ⟨"hyman-2003", "(22a)"⟩
    language := "nyan1308"
    primaryText := "Mchómbó a-ná-líl-its-il-a aná ndodo"
    glossedTokens := [("Mchómbó", "Mchombo"), ("a-ná-líl-its-il-a", "SP-PST-cry-CAUS-APP-fv"), ("aná", "children"), ("ndodo", "stick")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "cry"), ("scope", "CA"), ("suffixes", "CA")] }

def ex_22b : LinguisticExample :=
  { id := "hyman2003_22b"
    source := ⟨"hyman-2003", "(22b)"⟩
    reportedIn := some ⟨"hyman-2003", "(22b)"⟩
    language := "nyan1308"
    primaryText := "ndodo i-ná-líl-its-il-idw-á ána"
    glossedTokens := [("ndodo", "stick"), ("i-ná-líl-its-il-idw-á", "SP-PST-cry-CAUS-APP-PASS-fv"), ("ána", "children")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "cry"), ("scope", "CAP"), ("suffixes", "CAP"), ("subject", "instrument")] }

def ex_22c : LinguisticExample :=
  { id := "hyman2003_22c"
    source := ⟨"hyman-2003", "(22c)"⟩
    reportedIn := some ⟨"hyman-2003", "(22c)"⟩
    language := "nyan1308"
    primaryText := "aná a-ná-líl-its-il-idw-á ndodo"
    glossedTokens := [("aná", "children"), ("a-ná-líl-its-il-idw-á", "SP-PST-cry-CAUS-APP-PASS-fv"), ("ndodo", "stick")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "cry"), ("scope", "CAP"), ("suffixes", "CAP"), ("subject", "causee")] }

def ex_23a : LinguisticExample :=
  { id := "hyman2003_23a"
    source := ⟨"hyman-2003", "(23a)"⟩
    reportedIn := some ⟨"hyman-2003", "(23a)"⟩
    language := "nyan1308"
    primaryText := "Mchómbó a-ná-lím-its-il-a aná makásu"
    glossedTokens := [("Mchómbó", "Mchombo"), ("a-ná-lím-its-il-a", "SP-PST-cultivate-CAUS-APP-fv"), ("aná", "children"), ("makásu", "hoes")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "cultivate"), ("scope", "AC"), ("suffixes", "CA")] }

def ex_23b : LinguisticExample :=
  { id := "hyman2003_23b"
    source := ⟨"hyman-2003", "(23b)"⟩
    reportedIn := some ⟨"hyman-2003", "(23b)"⟩
    language := "nyan1308"
    primaryText := "aná a-ná-lím-its-il-idw-á mákásu"
    glossedTokens := [("aná", "children"), ("a-ná-lím-its-il-idw-á", "SP-PST-cultivate-CAUS-APP-PASS-fv"), ("mákásu", "hoes")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "cultivate"), ("scope", "ACP"), ("suffixes", "CAP"), ("subject", "causee")] }

def ex_23c : LinguisticExample :=
  { id := "hyman2003_23c"
    source := ⟨"hyman-2003", "(23c)"⟩
    reportedIn := some ⟨"hyman-2003", "(23c)"⟩
    language := "nyan1308"
    primaryText := "makású a-ná-lím-its-il-idw-á ána"
    glossedTokens := [("makású", "hoes"), ("a-ná-lím-its-il-idw-á", "SP-PST-cultivate-CAUS-APP-PASS-fv"), ("ána", "children")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "cultivate"), ("scope", "ACP"), ("suffixes", "CAP"), ("subject", "instrument")] }

def ex_32c : LinguisticExample :=
  { id := "hyman2003_32c"
    source := ⟨"hyman-mchombo-1992", "(32c)"⟩
    reportedIn := some ⟨"hyman-2003", "(32c)"⟩
    language := "nyan1308"
    primaryText := "uk-il-its-"
    glossedTokens := [("uk-il-its-", "wake.up-APP-CAUS")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("root", "wake up"), ("scope", "AC"), ("suffixes", "AC")] }

def ex_32d : LinguisticExample :=
  { id := "hyman2003_32d"
    source := ⟨"hyman-mchombo-1992", "(32d)"⟩
    reportedIn := some ⟨"hyman-2003", "(32d)"⟩
    language := "nyan1308"
    primaryText := "uk-its-il-"
    glossedTokens := [("uk-its-il-", "wake.up-CAUS-APP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "wake up"), ("scope", "AC"), ("suffixes", "CA")] }

def all : List LinguisticExample := [ex_2a_cr, ex_2a_rc, ex_2b_rc, ex_2b_cr, ex_3a, ex_3b, ex_7b, ex_8, ex_8_star, ex_13a, ex_13b, ex_13c, ex_13d, ex_17b, ex_18a, ex_18b, ex_20a, ex_20b, ex_22a, ex_22b, ex_22c, ex_23a, ex_23b, ex_23c, ex_32c, ex_32d]

end Hyman2003.Examples
