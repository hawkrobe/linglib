module

public import Linglib.Data.Examples.Schema

/-!
# `Scott2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Scott2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Scott2021.Examples`.
-/

@[expose] public section

namespace Scott2021.Examples

open Data.Examples

def cleft_24_mi : LinguisticExample :=
  { id := "scott2021_cleft_24_mi"
    source := ⟨"scott-2021", "(24)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye Bahati a-li-pika na-mi."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-mi", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "mi")] }

def cleft_24_ye : LinguisticExample :=
  { id := "scott2021_cleft_24_ye"
    source := ⟨"scott-2021", "(24)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye Bahati a-li-pika na-ye."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-ye", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "ye")] }

def cleft_25_we : LinguisticExample :=
  { id := "scott2021_cleft_25_we"
    source := ⟨"scott-2021", "(25)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Wewe ndi-ye amba-ye Bahati a-li-pika na-we."
    glossedTokens := [("Wewe", "2SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-we", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "we")] }

def cleft_25_ye : LinguisticExample :=
  { id := "scott2021_cleft_25_ye"
    source := ⟨"scott-2021", "(25)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Wewe ndi-ye amba-ye Bahati a-li-pika na-ye."
    glossedTokens := [("Wewe", "2SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-ye", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "ye")] }

def cleft_29a_si : LinguisticExample :=
  { id := "scott2021_cleft_29a_si"
    source := ⟨"scott-2021", "(29a)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye Bahati a-li-pika na-si."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-si", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "si")] }

def cleft_29a_o : LinguisticExample :=
  { id := "scott2021_cleft_29a_o"
    source := ⟨"scott-2021", "(29a)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye Bahati a-li-pika na-o."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-o", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "o")] }

def cleft_29b_nyi : LinguisticExample :=
  { id := "scott2021_cleft_29b_nyi"
    source := ⟨"scott-2021", "(29b)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Wewe ndi-ye amba-ye Bahati a-li-pika na-nyi."
    glossedTokens := [("Wewe", "2SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-nyi", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "nyi")] }

def cleft_29b_o : LinguisticExample :=
  { id := "scott2021_cleft_29b_o"
    source := ⟨"scott-2021", "(29b)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Wewe ndi-ye amba-ye Bahati a-li-pika na-o."
    glossedTokens := [("Wewe", "2SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-o", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "o")] }

def island_31_we : LinguisticExample :=
  { id := "scott2021_island_31_we"
    source := ⟨"scott-2021", "(31)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-we"
    glossedTokens := [("na-we", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "we")] }

def island_31_ye : LinguisticExample :=
  { id := "scott2021_island_31_ye"
    source := ⟨"scott-2021", "(31)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye"
    glossedTokens := [("na-ye", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "ye")] }

def island_32_mi : LinguisticExample :=
  { id := "scott2021_island_32_mi"
    source := ⟨"scott-2021", "(32)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi"
    glossedTokens := [("na-mi", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "mi")] }

def island_32_ye : LinguisticExample :=
  { id := "scott2021_island_32_ye"
    source := ⟨"scott-2021", "(32)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye"
    glossedTokens := [("na-ye", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "ye")] }

def island_33_mi : LinguisticExample :=
  { id := "scott2021_island_33_mi"
    source := ⟨"scott-2021", "(33)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi"
    glossedTokens := [("na-mi", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "mi")] }

def island_33_ye : LinguisticExample :=
  { id := "scott2021_island_33_ye"
    source := ⟨"scott-2021", "(33)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye"
    glossedTokens := [("na-ye", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "ye")] }

def pg_36 : LinguisticExample :=
  { id := "scott2021_pg_36"
    source := ⟨"scott-2021", "(36)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye u-li-pika na-ye kabla ya ku-ondoka na-ye."
    glossedTokens := [("na-ye", "with-1"), ("na-ye", "with-1")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "ye")] }

def pg_37 : LinguisticExample :=
  { id := "scott2021_pg_37"
    source := ⟨"scott-2021", "(37)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye u-li-pika na-mi kabla ya ku-cheza na-ye."
    glossedTokens := [("na-mi", "with-1SG"), ("na-ye", "with-1")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "ye")] }

def table4_sp1_ye_ye : LinguisticExample :=
  { id := "scott2021_table4_sp1_ye_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-ye"
    glossedTokens := [("na-ye", "with-PRO"), ("na-ye", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "ye"), ("speaker", "1")] }

def table4_sp1_mi_ye : LinguisticExample :=
  { id := "scott2021_table4_sp1_mi_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-ye"
    glossedTokens := [("na-mi", "with-PRO"), ("na-ye", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "ye"), ("speaker", "1")] }

def table4_sp1_mi_mi : LinguisticExample :=
  { id := "scott2021_table4_sp1_mi_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-mi"
    glossedTokens := [("na-mi", "with-PRO"), ("na-mi", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "mi"), ("speaker", "1")] }

def table4_sp1_ye_mi : LinguisticExample :=
  { id := "scott2021_table4_sp1_ye_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-mi"
    glossedTokens := [("na-ye", "with-PRO"), ("na-mi", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "mi"), ("speaker", "1")] }

def table4_sp2_ye_ye : LinguisticExample :=
  { id := "scott2021_table4_sp2_ye_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-ye"
    glossedTokens := [("na-ye", "with-PRO"), ("na-ye", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "ye"), ("speaker", "2")] }

def table4_sp2_mi_ye : LinguisticExample :=
  { id := "scott2021_table4_sp2_mi_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-ye"
    glossedTokens := [("na-mi", "with-PRO"), ("na-ye", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "ye"), ("speaker", "2")] }

def table4_sp2_mi_mi : LinguisticExample :=
  { id := "scott2021_table4_sp2_mi_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-mi"
    glossedTokens := [("na-mi", "with-PRO"), ("na-mi", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "mi"), ("speaker", "2")] }

def table4_sp2_ye_mi : LinguisticExample :=
  { id := "scott2021_table4_sp2_ye_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-mi"
    glossedTokens := [("na-ye", "with-PRO"), ("na-mi", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "mi"), ("speaker", "2")] }

def table4_sp3_ye_ye : LinguisticExample :=
  { id := "scott2021_table4_sp3_ye_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-ye"
    glossedTokens := [("na-ye", "with-PRO"), ("na-ye", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "ye"), ("speaker", "3")] }

def table4_sp3_mi_ye : LinguisticExample :=
  { id := "scott2021_table4_sp3_mi_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-ye"
    glossedTokens := [("na-mi", "with-PRO"), ("na-ye", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "ye"), ("speaker", "3")] }

def table4_sp3_mi_mi : LinguisticExample :=
  { id := "scott2021_table4_sp3_mi_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-mi"
    glossedTokens := [("na-mi", "with-PRO"), ("na-mi", "with-PRO")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "mi"), ("speaker", "3")] }

def table4_sp3_ye_mi : LinguisticExample :=
  { id := "scott2021_table4_sp3_ye_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-mi"
    glossedTokens := [("na-ye", "with-PRO"), ("na-mi", "with-PRO")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "mi"), ("speaker", "3")] }

def all : List LinguisticExample := [cleft_24_mi, cleft_24_ye, cleft_25_we, cleft_25_ye, cleft_29a_si, cleft_29a_o, cleft_29b_nyi, cleft_29b_o, island_31_we, island_31_ye, island_32_mi, island_32_ye, island_33_mi, island_33_ye, pg_36, pg_37, table4_sp1_ye_ye, table4_sp1_mi_ye, table4_sp1_mi_mi, table4_sp1_ye_mi, table4_sp2_ye_ye, table4_sp2_mi_ye, table4_sp2_mi_mi, table4_sp2_ye_mi, table4_sp3_ye_ye, table4_sp3_mi_ye, table4_sp3_mi_mi, table4_sp3_ye_mi]

end Scott2021.Examples
