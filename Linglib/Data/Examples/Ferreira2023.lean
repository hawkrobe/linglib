import Linglib.Data.Examples.Schema

/-!
# `Ferreira2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Ferreira2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ferreira2023.Examples`.
-/

namespace Ferreira2023.Examples

open Data.Examples

def ex_16 : LinguisticExample :=
  { id := "ferreira2023_16"
    source := ⟨"ferreira-2023", "(16)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem tem que ter sido assassinado, mas ele pode não ter sido."
    discourseSegments := []
    glossedTokens := []
    translation := "This man must have been murdered, but he may not have been."
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "sn_p"), ("second", "pos_notp")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17 : LinguisticExample :=
  { id := "ferreira2023_17"
    source := ⟨"ferreira-2023", "(17)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem deve ter sido assassinado, mas ele pode não ter sido."
    discourseSegments := []
    glossedTokens := []
    translation := "This man ought to have been murdered, but he may not have been."
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "pos_notp")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18 : LinguisticExample :=
  { id := "ferreira2023_18"
    source := ⟨"ferreira-2023", "(18)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem pode ter sido assassinado, mas ele pode não ter sido."
    discourseSegments := []
    glossedTokens := []
    translation := "This man may have been murdered, but he may not have been."
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "pos_p"), ("second", "pos_notp")]
    comment := "Repeated as (23)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19 : LinguisticExample :=
  { id := "ferreira2023_19"
    source := ⟨"ferreira-2023", "(19)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem tem que ter sido assassinado, mas ele não deve ter sido."
    discourseSegments := []
    glossedTokens := []
    translation := "This man must have been murdered, but he ought not to have been."
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "sn_p"), ("second", "not_wn_p")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20 : LinguisticExample :=
  { id := "ferreira2023_20"
    source := ⟨"ferreira-2023", "(20)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem deve ter sido assassinado, mas ele não tem que ter sido."
    discourseSegments := []
    glossedTokens := []
    translation := "This man ought to have been murdered, but he doesn't have to have been."
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "not_sn_p")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21 : LinguisticExample :=
  { id := "ferreira2023_21"
    source := ⟨"ferreira-2023", "(21)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem deve ter sido assassinado, mas ele não pode ter sido."
    discourseSegments := []
    glossedTokens := []
    translation := "This man ought to have been murdered, but he can't have been."
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "not_pos_p")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22 : LinguisticExample :=
  { id := "ferreira2023_22"
    source := ⟨"ferreira-2023", "(22)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem pode ter sido assassinado, mas não deve ter sido."
    discourseSegments := []
    glossedTokens := []
    translation := "This man may have been murdered, but he ought not to have been."
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "pos_p"), ("second", "not_wn_p")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24 : LinguisticExample :=
  { id := "ferreira2023_24"
    source := ⟨"ferreira-2023", "(24)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem deve ter sido assassinado, mas ele deve não ter sido."
    discourseSegments := []
    glossedTokens := []
    translation := "This man ought to have been murdered, but he ought not to have been."
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "wn_notp")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25 : LinguisticExample :=
  { id := "ferreira2023_25"
    source := ⟨"ferreira-2023", "(25)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem tem que ter sido assassinado, mas ele tem que não ter sido."
    discourseSegments := []
    glossedTokens := []
    translation := "This man must have been murdered, but he must not have been."
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "sn_p"), ("second", "sn_notp")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30a : LinguisticExample :=
  { id := "ferreira2023_30a"
    source := ⟨"ferreira-2023", "(30a)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Clientes devem usar máscara, mas eles não têm que."
    discourseSegments := []
    glossedTokens := []
    translation := "Clients ought to wear a mask, but they don't have to."
    context := "Concerning the COVID-19 protocol of this establishment."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "not_sn_p")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30b : LinguisticExample :=
  { id := "ferreira2023_30b"
    source := ⟨"ferreira-2023", "(30b)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Clientes devem usar máscara. Na verdade, eles têm que."
    discourseSegments := []
    glossedTokens := []
    translation := "Clients ought to wear a mask. In fact, they have to."
    context := "Concerning the COVID-19 protocol of this establishment."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "sn_p")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_32a : LinguisticExample :=
  { id := "ferreira2023_32a"
    source := ⟨"ferreira-2023", "(32a)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Tenho que limpar os pratos, mas não estou obrigado."
    discourseSegments := []
    glossedTokens := []
    translation := "I must clean the dishes, but I am not obliged."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "sn_p"), ("second", "not_sn_p")]
    comment := "Not being obliged is read as the negation of the strong necessity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_32b : LinguisticExample :=
  { id := "ferreira2023_32b"
    source := ⟨"ferreira-2023", "(32b)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Devo limpar os pratos, mas não estou obrigado."
    discourseSegments := []
    glossedTokens := []
    translation := "I ought to clean the dishes, but I am not obliged."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "not_sn_p")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_24, ex_25, ex_30a, ex_30b, ex_32a, ex_32b]

end Ferreira2023.Examples
