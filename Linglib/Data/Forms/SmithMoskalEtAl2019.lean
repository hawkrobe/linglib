module

public import Linglib.Data.Forms.Schema

/-!
# `SmithMoskalEtAl2019` — CLDF form data

Auto-generated from `Linglib/Data/Forms/SmithMoskalEtAl2019.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace SmithMoskalEtAl2019.Forms`.
-/

@[expose] public section

namespace SmithMoskalEtAl2019.Forms

open Data.Forms

def wardaman_3sg_abs : Form :=
  { id := "smithmoskaletal2019_wardaman_3sg_abs"
    languageId := "ward1246"
    parameterId := "3sg_abs"
    form := "narnaj"
    segments := ["narnaj"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 25"⟩
    ]
    columns := [("Base", "A")] }

def wardaman_3sg_erg : Form :=
  { id := "smithmoskaletal2019_wardaman_3sg_erg"
    languageId := "ward1246"
    parameterId := "3sg_erg"
    form := "narnaj-(j)i"
    segments := ["narnaj", "(j)i"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 25"⟩
    ]
    columns := [("Base", "A")] }

def wardaman_3sg_dat : Form :=
  { id := "smithmoskaletal2019_wardaman_3sg_dat"
    languageId := "ward1246"
    parameterId := "3sg_dat"
    form := "gunga"
    segments := ["gunga"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 25"⟩
    ]
    columns := [("Base", "B")] }

def khinalugh_2sg_abs : Form :=
  { id := "smithmoskaletal2019_khinalugh_2sg_abs"
    languageId := "khin1240"
    parameterId := "2sg_abs"
    form := "vɨ"
    segments := ["vɨ"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 24"⟩
    ]
    columns := [("Base", "A")] }

def khinalugh_2sg_erg : Form :=
  { id := "smithmoskaletal2019_khinalugh_2sg_erg"
    languageId := "khin1240"
    parameterId := "2sg_erg"
    form := "va"
    segments := ["va"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 24"⟩
    ]
    columns := [("Base", "A")] }

def khinalugh_2sg_dat : Form :=
  { id := "smithmoskaletal2019_khinalugh_2sg_dat"
    languageId := "khin1240"
    parameterId := "2sg_dat"
    form := "oX(ɨr)"
    segments := ["oX(ɨr)"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 24"⟩
    ]
    columns := [("Base", "B")] }

def archi_2sg_abs : Form :=
  { id := "smithmoskaletal2019_archi_2sg_abs"
    languageId := "arch1244"
    parameterId := "2sg_abs"
    form := "un"
    segments := ["un"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 20"⟩
    ]
    columns := [("Base", "A")] }

def archi_2sg_erg : Form :=
  { id := "smithmoskaletal2019_archi_2sg_erg"
    languageId := "arch1244"
    parameterId := "2sg_erg"
    form := "un"
    segments := ["un"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 20"⟩
    ]
    columns := [("Base", "A")] }

def archi_2sg_dat : Form :=
  { id := "smithmoskaletal2019_archi_2sg_dat"
    languageId := "arch1244"
    parameterId := "2sg_dat"
    form := "wa-s"
    segments := ["wa", "s"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 20"⟩
    ]
    columns := [("Base", "B")] }

def icelandic_1sg_nom : Form :=
  { id := "smithmoskaletal2019_icelandic_1sg_nom"
    languageId := "icel1247"
    parameterId := "1sg_nom"
    form := "ég"
    segments := ["ég"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 6"⟩
    ]
    columns := [("Base", "A")] }

def icelandic_1sg_acc : Form :=
  { id := "smithmoskaletal2019_icelandic_1sg_acc"
    languageId := "icel1247"
    parameterId := "1sg_acc"
    form := "mig"
    segments := ["mig"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 6"⟩
    ]
    columns := [("Base", "B")] }

def icelandic_1sg_dat : Form :=
  { id := "smithmoskaletal2019_icelandic_1sg_dat"
    languageId := "icel1247"
    parameterId := "1sg_dat"
    form := "mér"
    segments := ["mér"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 6"⟩
    ]
    columns := [("Base", "B")] }

def russian_1sg_nom : Form :=
  { id := "smithmoskaletal2019_russian_1sg_nom"
    languageId := "russ1263"
    parameterId := "1sg_nom"
    form := "ja"
    segments := ["ja"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 10"⟩
    ]
    columns := [("Base", "A")] }

def russian_1sg_acc : Form :=
  { id := "smithmoskaletal2019_russian_1sg_acc"
    languageId := "russ1263"
    parameterId := "1sg_acc"
    form := "menja"
    segments := ["menja"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 10"⟩
    ]
    columns := [("Base", "B")] }

def russian_1sg_dat : Form :=
  { id := "smithmoskaletal2019_russian_1sg_dat"
    languageId := "russ1263"
    parameterId := "1sg_dat"
    form := "mnje"
    segments := ["mnje"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 10"⟩
    ]
    columns := [("Base", "B")] }

def lezgian_1sg_abs : Form :=
  { id := "smithmoskaletal2019_lezgian_1sg_abs"
    languageId := "lezg1247"
    parameterId := "1sg_abs"
    form := "zun"
    segments := ["zun"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 11"⟩
    ]
    columns := [("Base", "A")] }

def lezgian_1sg_erg : Form :=
  { id := "smithmoskaletal2019_lezgian_1sg_erg"
    languageId := "lezg1247"
    parameterId := "1sg_erg"
    form := "za"
    segments := ["za"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 11"⟩
    ]
    columns := [("Base", "A")] }

def lezgian_1sg_dat : Form :=
  { id := "smithmoskaletal2019_lezgian_1sg_dat"
    languageId := "lezg1247"
    parameterId := "1sg_dat"
    form := "zaz"
    segments := ["zaz"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 11"⟩
    ]
    columns := [("Base", "A")] }

def awtuw_1_sg : Form :=
  { id := "smithmoskaletal2019_awtuw_1_sg"
    languageId := "awtu1239"
    parameterId := "1_sg"
    form := "wan"
    segments := ["wan"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 33"⟩
    ]
    columns := [("Base", "A")] }

def awtuw_1_pl : Form :=
  { id := "smithmoskaletal2019_awtuw_1_pl"
    languageId := "awtu1239"
    parameterId := "1_pl"
    form := "nom"
    segments := ["nom"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 33"⟩
    ]
    columns := [("Base", "B")] }

def awtuw_1_dl : Form :=
  { id := "smithmoskaletal2019_awtuw_1_dl"
    languageId := "awtu1239"
    parameterId := "1_dl"
    form := "nan"
    segments := ["nan"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 33"⟩
    ]
    columns := [("Base", "B")] }

def yagua_2_sg : Form :=
  { id := "smithmoskaletal2019_yagua_2_sg"
    languageId := "yagu1244"
    parameterId := "2_sg"
    form := "jiy"
    segments := ["jiy"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ]
    columns := [("Base", "A")] }

def yagua_2_pl : Form :=
  { id := "smithmoskaletal2019_yagua_2_pl"
    languageId := "yagu1244"
    parameterId := "2_pl"
    form := "jiryéy"
    segments := ["jiryéy"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ]
    columns := [("Base", "A")] }

def yagua_2_dl : Form :=
  { id := "smithmoskaletal2019_yagua_2_dl"
    languageId := "yagu1244"
    parameterId := "2_dl"
    form := "sááda"
    segments := ["sááda"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ]
    columns := [("Base", "B")] }

def wambaya_1incl_sg : Form :=
  { id := "smithmoskaletal2019_wambaya_1incl_sg"
    languageId := "wamb1258"
    parameterId := "1incl_sg"
    form := "ngawu(rniji)"
    segments := ["ngawu(rniji)"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ]
    columns := [("Base", "A")] }

def wambaya_1incl_pl : Form :=
  { id := "smithmoskaletal2019_wambaya_1incl_pl"
    languageId := "wamb1258"
    parameterId := "1incl_pl"
    form := "ngurruwani"
    segments := ["ngurruwani"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ]
    columns := [("Base", "A")] }

def wambaya_1incl_dl : Form :=
  { id := "smithmoskaletal2019_wambaya_1incl_dl"
    languageId := "wamb1258"
    parameterId := "1incl_dl"
    form := "mrindiyani"
    segments := ["mrindiyani"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ]
    columns := [("Base", "B")] }

def dehu_3m_sg : Form :=
  { id := "smithmoskaletal2019_dehu_3m_sg"
    languageId := "dehu1237"
    parameterId := "3m_sg"
    form := "angeice"
    segments := ["angeice"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ]
    columns := [("Base", "A")] }

def dehu_3m_pl : Form :=
  { id := "smithmoskaletal2019_dehu_3m_pl"
    languageId := "dehu1237"
    parameterId := "3m_pl"
    form := "angate"
    segments := ["angate"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ]
    columns := [("Base", "A")] }

def dehu_3m_dl : Form :=
  { id := "smithmoskaletal2019_dehu_3m_dl"
    languageId := "dehu1237"
    parameterId := "3m_dl"
    form := "nyido"
    segments := ["nyido"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ]
    columns := [("Base", "B")] }

def all : List Form := [wardaman_3sg_abs, wardaman_3sg_erg, wardaman_3sg_dat, khinalugh_2sg_abs, khinalugh_2sg_erg, khinalugh_2sg_dat, archi_2sg_abs, archi_2sg_erg, archi_2sg_dat, icelandic_1sg_nom, icelandic_1sg_acc, icelandic_1sg_dat, russian_1sg_nom, russian_1sg_acc, russian_1sg_dat, lezgian_1sg_abs, lezgian_1sg_erg, lezgian_1sg_dat, awtuw_1_sg, awtuw_1_pl, awtuw_1_dl, yagua_2_sg, yagua_2_pl, yagua_2_dl, wambaya_1incl_sg, wambaya_1incl_pl, wambaya_1incl_dl, dehu_3m_sg, dehu_3m_pl, dehu_3m_dl]

def relations : List FormRelation := []

end SmithMoskalEtAl2019.Forms
