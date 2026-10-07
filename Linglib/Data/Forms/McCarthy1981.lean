module

public import Linglib.Data.Forms.Schema

/-!
# `McCarthy1981` — CLDF form data

Auto-generated from `Linglib/Data/Forms/McCarthy1981.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace McCarthy1981.Forms`.
-/

@[expose] public section

namespace McCarthy1981.Forms

open Data.Forms

def ktb_I_perf_act : Form :=
  { id := "mccarthy1981_ktb_I_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "katab"
    segments := ["k", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "I"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_I_perf_pas : Form :=
  { id := "mccarthy1981_ktb_I_perf_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "kutib"
    segments := ["k", "u", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "I"), ("Aspect", "perfective"), ("Voice", "passive")] }

def ktb_I_impe_act : Form :=
  { id := "mccarthy1981_ktb_I_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "aktub"
    segments := ["a", "k", "t", "u", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "I"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_I_impe_pas : Form :=
  { id := "mccarthy1981_ktb_I_impe_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "uktab"
    segments := ["u", "k", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "I"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def ktb_I_part_act : Form :=
  { id := "mccarthy1981_ktb_I_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "kaatib"
    segments := ["k", "a", "a", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "I"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_I_part_pas : Form :=
  { id := "mccarthy1981_ktb_I_part_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "maktuub"
    segments := ["m", "a", "k", "t", "u", "u", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "I"), ("Aspect", "participle"), ("Voice", "passive")] }

def ktb_II_perf_act : Form :=
  { id := "mccarthy1981_ktb_II_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "kattab"
    segments := ["k", "a", "t", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "II"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_II_perf_pas : Form :=
  { id := "mccarthy1981_ktb_II_perf_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "kuttib"
    segments := ["k", "u", "t", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "II"), ("Aspect", "perfective"), ("Voice", "passive")] }

def ktb_II_impe_act : Form :=
  { id := "mccarthy1981_ktb_II_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "ukattib"
    segments := ["u", "k", "a", "t", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "II"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_II_impe_pas : Form :=
  { id := "mccarthy1981_ktb_II_impe_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "ukattab"
    segments := ["u", "k", "a", "t", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "II"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def ktb_II_part_act : Form :=
  { id := "mccarthy1981_ktb_II_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "mukattib"
    segments := ["m", "u", "k", "a", "t", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "II"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_II_part_pas : Form :=
  { id := "mccarthy1981_ktb_II_part_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "mukattab"
    segments := ["m", "u", "k", "a", "t", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "II"), ("Aspect", "participle"), ("Voice", "passive")] }

def ktb_III_perf_act : Form :=
  { id := "mccarthy1981_ktb_III_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "kaatab"
    segments := ["k", "a", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "III"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_III_perf_pas : Form :=
  { id := "mccarthy1981_ktb_III_perf_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "kuutib"
    segments := ["k", "u", "u", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "III"), ("Aspect", "perfective"), ("Voice", "passive")] }

def ktb_III_impe_act : Form :=
  { id := "mccarthy1981_ktb_III_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "ukaatib"
    segments := ["u", "k", "a", "a", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "III"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_III_impe_pas : Form :=
  { id := "mccarthy1981_ktb_III_impe_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "ukaatab"
    segments := ["u", "k", "a", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "III"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def ktb_III_part_act : Form :=
  { id := "mccarthy1981_ktb_III_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "mukaatib"
    segments := ["m", "u", "k", "a", "a", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "III"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_III_part_pas : Form :=
  { id := "mccarthy1981_ktb_III_part_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "mukaatab"
    segments := ["m", "u", "k", "a", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "III"), ("Aspect", "participle"), ("Voice", "passive")] }

def ktb_IV_perf_act : Form :=
  { id := "mccarthy1981_ktb_IV_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "ʔaktab"
    segments := ["ʔ", "a", "k", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "IV"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_IV_perf_pas : Form :=
  { id := "mccarthy1981_ktb_IV_perf_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "ʔuktib"
    segments := ["ʔ", "u", "k", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "IV"), ("Aspect", "perfective"), ("Voice", "passive")] }

def ktb_IV_impe_act : Form :=
  { id := "mccarthy1981_ktb_IV_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "uʔaktib"
    segments := ["u", "ʔ", "a", "k", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "IV"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_IV_impe_pas : Form :=
  { id := "mccarthy1981_ktb_IV_impe_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "uʔaktab"
    segments := ["u", "ʔ", "a", "k", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "IV"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def ktb_IV_part_act : Form :=
  { id := "mccarthy1981_ktb_IV_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "muʔaktib"
    segments := ["m", "u", "ʔ", "a", "k", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "IV"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_IV_part_pas : Form :=
  { id := "mccarthy1981_ktb_IV_part_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "muʔaktab"
    segments := ["m", "u", "ʔ", "a", "k", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "IV"), ("Aspect", "participle"), ("Voice", "passive")] }

def ktb_V_perf_act : Form :=
  { id := "mccarthy1981_ktb_V_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "takattab"
    segments := ["t", "a", "k", "a", "t", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "V"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_V_perf_pas : Form :=
  { id := "mccarthy1981_ktb_V_perf_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "tukuttib"
    segments := ["t", "u", "k", "u", "t", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "V"), ("Aspect", "perfective"), ("Voice", "passive")] }

def ktb_V_impe_act : Form :=
  { id := "mccarthy1981_ktb_V_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "atakattab"
    segments := ["a", "t", "a", "k", "a", "t", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "V"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_V_impe_pas : Form :=
  { id := "mccarthy1981_ktb_V_impe_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "utakattab"
    segments := ["u", "t", "a", "k", "a", "t", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "V"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def ktb_V_part_act : Form :=
  { id := "mccarthy1981_ktb_V_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "mutakattib"
    segments := ["m", "u", "t", "a", "k", "a", "t", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "V"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_V_part_pas : Form :=
  { id := "mccarthy1981_ktb_V_part_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "mutakattab"
    segments := ["m", "u", "t", "a", "k", "a", "t", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "V"), ("Aspect", "participle"), ("Voice", "passive")] }

def ktb_VI_perf_act : Form :=
  { id := "mccarthy1981_ktb_VI_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "takaatab"
    segments := ["t", "a", "k", "a", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VI"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_VI_perf_pas : Form :=
  { id := "mccarthy1981_ktb_VI_perf_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "tukuutib"
    segments := ["t", "u", "k", "u", "u", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VI"), ("Aspect", "perfective"), ("Voice", "passive")] }

def ktb_VI_impe_act : Form :=
  { id := "mccarthy1981_ktb_VI_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "atakaatab"
    segments := ["a", "t", "a", "k", "a", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VI"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_VI_impe_pas : Form :=
  { id := "mccarthy1981_ktb_VI_impe_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "utakaatab"
    segments := ["u", "t", "a", "k", "a", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VI"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def ktb_VI_part_act : Form :=
  { id := "mccarthy1981_ktb_VI_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "mutakaatib"
    segments := ["m", "u", "t", "a", "k", "a", "a", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VI"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_VI_part_pas : Form :=
  { id := "mccarthy1981_ktb_VI_part_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "mutakaatab"
    segments := ["m", "u", "t", "a", "k", "a", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VI"), ("Aspect", "participle"), ("Voice", "passive")] }

def ktb_VII_perf_act : Form :=
  { id := "mccarthy1981_ktb_VII_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "nkatab"
    segments := ["n", "k", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VII"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_VII_perf_pas : Form :=
  { id := "mccarthy1981_ktb_VII_perf_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "nkutib"
    segments := ["n", "k", "u", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VII"), ("Aspect", "perfective"), ("Voice", "passive")] }

def ktb_VII_impe_act : Form :=
  { id := "mccarthy1981_ktb_VII_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "ankatib"
    segments := ["a", "n", "k", "a", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VII"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_VII_impe_pas : Form :=
  { id := "mccarthy1981_ktb_VII_impe_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "unkatab"
    segments := ["u", "n", "k", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VII"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def ktb_VII_part_act : Form :=
  { id := "mccarthy1981_ktb_VII_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "munkatib"
    segments := ["m", "u", "n", "k", "a", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VII"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_VII_part_pas : Form :=
  { id := "mccarthy1981_ktb_VII_part_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "munkatab"
    segments := ["m", "u", "n", "k", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VII"), ("Aspect", "participle"), ("Voice", "passive")] }

def ktb_VIII_perf_act : Form :=
  { id := "mccarthy1981_ktb_VIII_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "ktatab"
    segments := ["k", "t", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VIII"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_VIII_perf_pas : Form :=
  { id := "mccarthy1981_ktb_VIII_perf_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "ktutib"
    segments := ["k", "t", "u", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VIII"), ("Aspect", "perfective"), ("Voice", "passive")] }

def ktb_VIII_impe_act : Form :=
  { id := "mccarthy1981_ktb_VIII_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "aktatib"
    segments := ["a", "k", "t", "a", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VIII"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_VIII_impe_pas : Form :=
  { id := "mccarthy1981_ktb_VIII_impe_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "uktatab"
    segments := ["u", "k", "t", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VIII"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def ktb_VIII_part_act : Form :=
  { id := "mccarthy1981_ktb_VIII_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "muktatib"
    segments := ["m", "u", "k", "t", "a", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VIII"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_VIII_part_pas : Form :=
  { id := "mccarthy1981_ktb_VIII_part_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "muktatab"
    segments := ["m", "u", "k", "t", "a", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "VIII"), ("Aspect", "participle"), ("Voice", "passive")] }

def ktb_IX_perf_act : Form :=
  { id := "mccarthy1981_ktb_IX_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "ktabab"
    segments := ["k", "t", "a", "b", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "IX"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_IX_impe_act : Form :=
  { id := "mccarthy1981_ktb_IX_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "aktabib"
    segments := ["a", "k", "t", "a", "b", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "IX"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_IX_part_act : Form :=
  { id := "mccarthy1981_ktb_IX_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "muktabib"
    segments := ["m", "u", "k", "t", "a", "b", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "IX"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_X_perf_act : Form :=
  { id := "mccarthy1981_ktb_X_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "staktab"
    segments := ["s", "t", "a", "k", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "X"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_X_perf_pas : Form :=
  { id := "mccarthy1981_ktb_X_perf_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "stuktib"
    segments := ["s", "t", "u", "k", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "X"), ("Aspect", "perfective"), ("Voice", "passive")] }

def ktb_X_impe_act : Form :=
  { id := "mccarthy1981_ktb_X_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "astaktib"
    segments := ["a", "s", "t", "a", "k", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "X"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_X_impe_pas : Form :=
  { id := "mccarthy1981_ktb_X_impe_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "ustaktab"
    segments := ["u", "s", "t", "a", "k", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "X"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def ktb_X_part_act : Form :=
  { id := "mccarthy1981_ktb_X_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "mustaktib"
    segments := ["m", "u", "s", "t", "a", "k", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "X"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_X_part_pas : Form :=
  { id := "mccarthy1981_ktb_X_part_pas"
    languageId := "clas1259"
    parameterId := "write"
    form := "mustaktab"
    segments := ["m", "u", "s", "t", "a", "k", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "X"), ("Aspect", "participle"), ("Voice", "passive")] }

def ktb_XI_perf_act : Form :=
  { id := "mccarthy1981_ktb_XI_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "ktaabab"
    segments := ["k", "t", "a", "a", "b", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XI"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_XI_impe_act : Form :=
  { id := "mccarthy1981_ktb_XI_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "aktaabib"
    segments := ["a", "k", "t", "a", "a", "b", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XI"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_XI_part_act : Form :=
  { id := "mccarthy1981_ktb_XI_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "muktaabib"
    segments := ["m", "u", "k", "t", "a", "a", "b", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XI"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_XII_perf_act : Form :=
  { id := "mccarthy1981_ktb_XII_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "ktawtab"
    segments := ["k", "t", "a", "w", "t", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XII"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_XII_impe_act : Form :=
  { id := "mccarthy1981_ktb_XII_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "aktawtib"
    segments := ["a", "k", "t", "a", "w", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XII"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_XII_part_act : Form :=
  { id := "mccarthy1981_ktb_XII_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "muktawtib"
    segments := ["m", "u", "k", "t", "a", "w", "t", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XII"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_XIII_perf_act : Form :=
  { id := "mccarthy1981_ktb_XIII_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "ktawwab"
    segments := ["k", "t", "a", "w", "w", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XIII"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_XIII_impe_act : Form :=
  { id := "mccarthy1981_ktb_XIII_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "aktawwib"
    segments := ["a", "k", "t", "a", "w", "w", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XIII"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_XIII_part_act : Form :=
  { id := "mccarthy1981_ktb_XIII_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "muktawwib"
    segments := ["m", "u", "k", "t", "a", "w", "w", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XIII"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_XIV_perf_act : Form :=
  { id := "mccarthy1981_ktb_XIV_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "ktanbab"
    segments := ["k", "t", "a", "n", "b", "a", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XIV"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_XIV_impe_act : Form :=
  { id := "mccarthy1981_ktb_XIV_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "aktanbib"
    segments := ["a", "k", "t", "a", "n", "b", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XIV"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_XIV_part_act : Form :=
  { id := "mccarthy1981_ktb_XIV_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "muktanbib"
    segments := ["m", "u", "k", "t", "a", "n", "b", "i", "b"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XIV"), ("Aspect", "participle"), ("Voice", "active")] }

def ktb_XV_perf_act : Form :=
  { id := "mccarthy1981_ktb_XV_perf_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "ktanbay"
    segments := ["k", "t", "a", "n", "b", "a", "y"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XV"), ("Aspect", "perfective"), ("Voice", "active")] }

def ktb_XV_impe_act : Form :=
  { id := "mccarthy1981_ktb_XV_impe_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "aktanbiy"
    segments := ["a", "k", "t", "a", "n", "b", "i", "y"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XV"), ("Aspect", "imperfective"), ("Voice", "active")] }

def ktb_XV_part_act : Form :=
  { id := "mccarthy1981_ktb_XV_part_act"
    languageId := "clas1259"
    parameterId := "write"
    form := "muktanbiy"
    segments := ["m", "u", "k", "t", "a", "n", "b", "i", "y"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "XV"), ("Aspect", "participle"), ("Voice", "active")] }

def dhrj_QI_perf_act : Form :=
  { id := "mccarthy1981_dhrj_QI_perf_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "daḥraj"
    segments := ["d", "a", "ḥ", "r", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QI"), ("Aspect", "perfective"), ("Voice", "active")] }

def dhrj_QI_perf_pas : Form :=
  { id := "mccarthy1981_dhrj_QI_perf_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "duḥrij"
    segments := ["d", "u", "ḥ", "r", "i", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QI"), ("Aspect", "perfective"), ("Voice", "passive")] }

def dhrj_QI_impe_act : Form :=
  { id := "mccarthy1981_dhrj_QI_impe_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "udaḥrij"
    segments := ["u", "d", "a", "ḥ", "r", "i", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QI"), ("Aspect", "imperfective"), ("Voice", "active")] }

def dhrj_QI_impe_pas : Form :=
  { id := "mccarthy1981_dhrj_QI_impe_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "udaḥraj"
    segments := ["u", "d", "a", "ḥ", "r", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QI"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def dhrj_QI_part_act : Form :=
  { id := "mccarthy1981_dhrj_QI_part_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "mudaḥrij"
    segments := ["m", "u", "d", "a", "ḥ", "r", "i", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QI"), ("Aspect", "participle"), ("Voice", "active")] }

def dhrj_QI_part_pas : Form :=
  { id := "mccarthy1981_dhrj_QI_part_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "mudaḥraj"
    segments := ["m", "u", "d", "a", "ḥ", "r", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QI"), ("Aspect", "participle"), ("Voice", "passive")] }

def dhrj_QII_perf_act : Form :=
  { id := "mccarthy1981_dhrj_QII_perf_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "tadaḥraj"
    segments := ["t", "a", "d", "a", "ḥ", "r", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QII"), ("Aspect", "perfective"), ("Voice", "active")] }

def dhrj_QII_perf_pas : Form :=
  { id := "mccarthy1981_dhrj_QII_perf_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "tuduḥrij"
    segments := ["t", "u", "d", "u", "ḥ", "r", "i", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QII"), ("Aspect", "perfective"), ("Voice", "passive")] }

def dhrj_QII_impe_act : Form :=
  { id := "mccarthy1981_dhrj_QII_impe_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "atadaḥraj"
    segments := ["a", "t", "a", "d", "a", "ḥ", "r", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QII"), ("Aspect", "imperfective"), ("Voice", "active")] }

def dhrj_QII_impe_pas : Form :=
  { id := "mccarthy1981_dhrj_QII_impe_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "utadaḥraj"
    segments := ["u", "t", "a", "d", "a", "ḥ", "r", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QII"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def dhrj_QII_part_act : Form :=
  { id := "mccarthy1981_dhrj_QII_part_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "mutadaḥrij"
    segments := ["m", "u", "t", "a", "d", "a", "ḥ", "r", "i", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QII"), ("Aspect", "participle"), ("Voice", "active")] }

def dhrj_QII_part_pas : Form :=
  { id := "mccarthy1981_dhrj_QII_part_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "mutadaḥraj"
    segments := ["m", "u", "t", "a", "d", "a", "ḥ", "r", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QII"), ("Aspect", "participle"), ("Voice", "passive")] }

def dhrj_QIII_perf_act : Form :=
  { id := "mccarthy1981_dhrj_QIII_perf_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "dḥanraj"
    segments := ["d", "ḥ", "a", "n", "r", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIII"), ("Aspect", "perfective"), ("Voice", "active")] }

def dhrj_QIII_perf_pas : Form :=
  { id := "mccarthy1981_dhrj_QIII_perf_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "dḥunrij"
    segments := ["d", "ḥ", "u", "n", "r", "i", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIII"), ("Aspect", "perfective"), ("Voice", "passive")] }

def dhrj_QIII_impe_act : Form :=
  { id := "mccarthy1981_dhrj_QIII_impe_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "adḥanrij"
    segments := ["a", "d", "ḥ", "a", "n", "r", "i", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIII"), ("Aspect", "imperfective"), ("Voice", "active")] }

def dhrj_QIII_impe_pas : Form :=
  { id := "mccarthy1981_dhrj_QIII_impe_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "udḥanraj"
    segments := ["u", "d", "ḥ", "a", "n", "r", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIII"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def dhrj_QIII_part_act : Form :=
  { id := "mccarthy1981_dhrj_QIII_part_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "mudḥanrij"
    segments := ["m", "u", "d", "ḥ", "a", "n", "r", "i", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIII"), ("Aspect", "participle"), ("Voice", "active")] }

def dhrj_QIII_part_pas : Form :=
  { id := "mccarthy1981_dhrj_QIII_part_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "mudḥanraj"
    segments := ["m", "u", "d", "ḥ", "a", "n", "r", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIII"), ("Aspect", "participle"), ("Voice", "passive")] }

def dhrj_QIV_perf_act : Form :=
  { id := "mccarthy1981_dhrj_QIV_perf_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "dḥarjaj"
    segments := ["d", "ḥ", "a", "r", "j", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIV"), ("Aspect", "perfective"), ("Voice", "active")] }

def dhrj_QIV_perf_pas : Form :=
  { id := "mccarthy1981_dhrj_QIV_perf_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "dḥurjij"
    segments := ["d", "ḥ", "u", "r", "j", "i", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIV"), ("Aspect", "perfective"), ("Voice", "passive")] }

def dhrj_QIV_impe_act : Form :=
  { id := "mccarthy1981_dhrj_QIV_impe_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "adḥarjij"
    segments := ["a", "d", "ḥ", "a", "r", "j", "i", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIV"), ("Aspect", "imperfective"), ("Voice", "active")] }

def dhrj_QIV_impe_pas : Form :=
  { id := "mccarthy1981_dhrj_QIV_impe_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "udḥarjaj"
    segments := ["u", "d", "ḥ", "a", "r", "j", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIV"), ("Aspect", "imperfective"), ("Voice", "passive")] }

def dhrj_QIV_part_act : Form :=
  { id := "mccarthy1981_dhrj_QIV_part_act"
    languageId := "clas1259"
    parameterId := "roll"
    form := "mudḥarjij"
    segments := ["m", "u", "d", "ḥ", "a", "r", "j", "i", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIV"), ("Aspect", "participle"), ("Voice", "active")] }

def dhrj_QIV_part_pas : Form :=
  { id := "mccarthy1981_dhrj_QIV_part_pas"
    languageId := "clas1259"
    parameterId := "roll"
    form := "mudḥarjaj"
    segments := ["m", "u", "d", "ḥ", "a", "r", "j", "a", "j"]
    comment := ""
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ]
    columns := [("Binyan", "QIV"), ("Aspect", "participle"), ("Voice", "passive")] }

def poison_I_perf_act : Form :=
  { id := "mccarthy1981_poison_I_perf_act"
    languageId := "clas1259"
    parameterId := "poison"
    form := "samam"
    segments := ["s", "a", "m", "a", "m"]
    comment := "the biliteral root sm"
    source := [
      ⟨"mccarthy-1981", "(33)"⟩
    ]
    columns := [("Binyan", "I"), ("Aspect", "perfective"), ("Voice", "active")] }

def poison_II_perf_act : Form :=
  { id := "mccarthy1981_poison_II_perf_act"
    languageId := "clas1259"
    parameterId := "poison"
    form := "sammam"
    segments := ["s", "a", "m", "m", "a", "m"]
    comment := "the biliteral root sm"
    source := [
      ⟨"mccarthy-1981", "(34a)"⟩
    ]
    columns := [("Binyan", "II"), ("Aspect", "perfective"), ("Voice", "active")] }

def poison_V_perf_act : Form :=
  { id := "mccarthy1981_poison_V_perf_act"
    languageId := "clas1259"
    parameterId := "poison"
    form := "tasammam"
    segments := ["t", "a", "s", "a", "m", "m", "a", "m"]
    comment := "the biliteral root sm"
    source := [
      ⟨"mccarthy-1981", "(34b)"⟩
    ]
    columns := [("Binyan", "V"), ("Aspect", "perfective"), ("Voice", "active")] }

def magnetize_QI_perf_act : Form :=
  { id := "mccarthy1981_magnetize_QI_perf_act"
    languageId := "clas1259"
    parameterId := "magnetize"
    form := "mağnaṭ"
    segments := ["m", "a", "ğ", "n", "a", "ṭ"]
    comment := "the quinqueliteral root mğnṭš, from mağnaṭiiš 'magnet'"
    source := [
      ⟨"mccarthy-1981", "(38)"⟩
    ]
    columns := [("Binyan", "QI"), ("Aspect", "perfective"), ("Voice", "active")] }

def all : List Form := [ktb_I_perf_act, ktb_I_perf_pas, ktb_I_impe_act, ktb_I_impe_pas, ktb_I_part_act, ktb_I_part_pas, ktb_II_perf_act, ktb_II_perf_pas, ktb_II_impe_act, ktb_II_impe_pas, ktb_II_part_act, ktb_II_part_pas, ktb_III_perf_act, ktb_III_perf_pas, ktb_III_impe_act, ktb_III_impe_pas, ktb_III_part_act, ktb_III_part_pas, ktb_IV_perf_act, ktb_IV_perf_pas, ktb_IV_impe_act, ktb_IV_impe_pas, ktb_IV_part_act, ktb_IV_part_pas, ktb_V_perf_act, ktb_V_perf_pas, ktb_V_impe_act, ktb_V_impe_pas, ktb_V_part_act, ktb_V_part_pas, ktb_VI_perf_act, ktb_VI_perf_pas, ktb_VI_impe_act, ktb_VI_impe_pas, ktb_VI_part_act, ktb_VI_part_pas, ktb_VII_perf_act, ktb_VII_perf_pas, ktb_VII_impe_act, ktb_VII_impe_pas, ktb_VII_part_act, ktb_VII_part_pas, ktb_VIII_perf_act, ktb_VIII_perf_pas, ktb_VIII_impe_act, ktb_VIII_impe_pas, ktb_VIII_part_act, ktb_VIII_part_pas, ktb_IX_perf_act, ktb_IX_impe_act, ktb_IX_part_act, ktb_X_perf_act, ktb_X_perf_pas, ktb_X_impe_act, ktb_X_impe_pas, ktb_X_part_act, ktb_X_part_pas, ktb_XI_perf_act, ktb_XI_impe_act, ktb_XI_part_act, ktb_XII_perf_act, ktb_XII_impe_act, ktb_XII_part_act, ktb_XIII_perf_act, ktb_XIII_impe_act, ktb_XIII_part_act, ktb_XIV_perf_act, ktb_XIV_impe_act, ktb_XIV_part_act, ktb_XV_perf_act, ktb_XV_impe_act, ktb_XV_part_act, dhrj_QI_perf_act, dhrj_QI_perf_pas, dhrj_QI_impe_act, dhrj_QI_impe_pas, dhrj_QI_part_act, dhrj_QI_part_pas, dhrj_QII_perf_act, dhrj_QII_perf_pas, dhrj_QII_impe_act, dhrj_QII_impe_pas, dhrj_QII_part_act, dhrj_QII_part_pas, dhrj_QIII_perf_act, dhrj_QIII_perf_pas, dhrj_QIII_impe_act, dhrj_QIII_impe_pas, dhrj_QIII_part_act, dhrj_QIII_part_pas, dhrj_QIV_perf_act, dhrj_QIV_perf_pas, dhrj_QIV_impe_act, dhrj_QIV_impe_pas, dhrj_QIV_part_act, dhrj_QIV_part_pas, poison_I_perf_act, poison_II_perf_act, poison_V_perf_act, magnetize_QI_perf_act]

def parameters : List Parameter := [
  { id := "write", name := "write", description := "the root ktb" },
  { id := "roll", name := "roll", description := "the root dḥrj" },
  { id := "poison", name := "poison", description := "the root sm" },
  { id := "magnetize", name := "magnetize", description := "the root mğnṭš" }
]

def relations : List FormRelation := []

end McCarthy1981.Forms
