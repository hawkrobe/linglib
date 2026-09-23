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
    comment := "AAB without syncretism: the ergative carries a case suffix the absolutive lacks, the dative is suppletive"
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
    comment := "AAB without syncretism: the ergative carries a case suffix the absolutive lacks, the dative is suppletive"
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
    comment := "AAB without syncretism: the ergative carries a case suffix the absolutive lacks, the dative is suppletive"
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
    comment := "AAB without syncretism: the ergative is irregular relative to the absolutive, the dative is suppletive"
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
    comment := "AAB without syncretism: the ergative is irregular relative to the absolutive, the dative is suppletive"
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
    comment := "AAB without syncretism: the ergative is irregular relative to the absolutive, the dative is suppletive"
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
    comment := "syncretic {A=A}B: the absolutive and the ergative are identical, a two-way contrast the paper does not count as AAB"
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
    comment := "syncretic {A=A}B: the absolutive and the ergative are identical, a two-way contrast the paper does not count as AAB"
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
    comment := "syncretic {A=A}B: the absolutive and the ergative are identical, a two-way contrast the paper does not count as AAB"
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
    comment := "ABB, the rules (15): an accusative-conditioned m- and an elsewhere ég"
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
    comment := "ABB, the rules (15): an accusative-conditioned m- and an elsewhere ég"
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
    comment := "ABB, the rules (15): an accusative-conditioned m- and an elsewhere ég"
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
    comment := "the inherited Indo-European ABB"
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
    comment := "the inherited Indo-European ABB"
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
    comment := "the inherited Indo-European ABB"
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
    comment := "AAA on a constant z(a)-base"
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
    comment := "AAA on a constant z(a)-base"
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
    comment := "AAA on a constant z(a)-base"
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
    comment := "ABB: the plural and the dual share a suppletive n-base"
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
    comment := "ABB: the plural and the dual share a suppletive n-base"
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
    comment := "ABB: the plural and the dual share a suppletive n-base"
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
    comment := "AAB for number: the plural contains the singular base, the dual is suppletive"
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
    comment := "AAB for number: the plural contains the singular base, the dual is suppletive"
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
    comment := "AAB for number: the plural contains the singular base, the dual is suppletive"
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
    comment := "AAB for number"
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
    comment := "AAB for number"
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
    comment := "AAB for number"
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
    comment := "AAB for number"
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
    comment := "AAB for number"
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
    comment := "AAB for number"
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ]
    columns := [("Base", "B")] }

def all : List Form := [wardaman_3sg_abs, wardaman_3sg_erg, wardaman_3sg_dat, khinalugh_2sg_abs, khinalugh_2sg_erg, khinalugh_2sg_dat, archi_2sg_abs, archi_2sg_erg, archi_2sg_dat, icelandic_1sg_nom, icelandic_1sg_acc, icelandic_1sg_dat, russian_1sg_nom, russian_1sg_acc, russian_1sg_dat, lezgian_1sg_abs, lezgian_1sg_erg, lezgian_1sg_dat, awtuw_1_sg, awtuw_1_pl, awtuw_1_dl, yagua_2_sg, yagua_2_pl, yagua_2_dl, wambaya_1incl_sg, wambaya_1incl_pl, wambaya_1incl_dl, dehu_3m_sg, dehu_3m_pl, dehu_3m_dl]

def parameters : List Parameter := [
  { id := "3sg_abs", name := "3SG pronoun, absolutive", description := "" },
  { id := "3sg_erg", name := "3SG pronoun, ergative", description := "" },
  { id := "3sg_dat", name := "3SG pronoun, dative", description := "" },
  { id := "2sg_abs", name := "2SG pronoun, absolutive", description := "" },
  { id := "2sg_erg", name := "2SG pronoun, ergative", description := "" },
  { id := "2sg_dat", name := "2SG pronoun, dative", description := "" },
  { id := "1sg_nom", name := "1SG pronoun, nominative", description := "" },
  { id := "1sg_acc", name := "1SG pronoun, accusative", description := "" },
  { id := "1sg_dat", name := "1SG pronoun, dative", description := "" },
  { id := "1sg_abs", name := "1SG pronoun, absolutive", description := "" },
  { id := "1sg_erg", name := "1SG pronoun, ergative", description := "" },
  { id := "1_sg", name := "1 pronoun, singular", description := "" },
  { id := "1_pl", name := "1 pronoun, plural", description := "" },
  { id := "1_dl", name := "1 pronoun, dual", description := "" },
  { id := "2_sg", name := "2 pronoun, singular", description := "" },
  { id := "2_pl", name := "2 pronoun, plural", description := "" },
  { id := "2_dl", name := "2 pronoun, dual", description := "" },
  { id := "1incl_sg", name := "1INCL pronoun, singular", description := "" },
  { id := "1incl_pl", name := "1INCL pronoun, plural", description := "" },
  { id := "1incl_dl", name := "1INCL pronoun, dual", description := "" },
  { id := "3m_sg", name := "3M pronoun, singular", description := "" },
  { id := "3m_pl", name := "3M pronoun, plural", description := "" },
  { id := "3m_dl", name := "3M pronoun, dual", description := "" }
]

def relations : List FormRelation := []

end SmithMoskalEtAl2019.Forms
