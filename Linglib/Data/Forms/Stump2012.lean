import Linglib.Data.Forms.Schema

/-!
# `Stump2012` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Stump2012.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Stump2012.Forms`.
-/

namespace Stump2012.Forms

open Data.Forms

def begin_perf_s1 : Form :=
  { id := "stump2012_begin_perf_s1"
    languageId := "lati1261"
    parameterId := "begin"
    form := "coepī"
    segments := ["c", "o", "e", "p", "ī"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ]
    columns := [("Lexeme", "COEPISSE"), ("System", "perf"), ("Agr", "s1")] }

def begin_perf_s2 : Form :=
  { id := "stump2012_begin_perf_s2"
    languageId := "lati1261"
    parameterId := "begin"
    form := "coepistī"
    segments := ["c", "o", "e", "p", "i", "s", "t", "ī"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ]
    columns := [("Lexeme", "COEPISSE"), ("System", "perf"), ("Agr", "s2")] }

def begin_perf_s3 : Form :=
  { id := "stump2012_begin_perf_s3"
    languageId := "lati1261"
    parameterId := "begin"
    form := "coepit"
    segments := ["c", "o", "e", "p", "i", "t"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ]
    columns := [("Lexeme", "COEPISSE"), ("System", "perf"), ("Agr", "s3")] }

def begin_perf_p1 : Form :=
  { id := "stump2012_begin_perf_p1"
    languageId := "lati1261"
    parameterId := "begin"
    form := "coepimus"
    segments := ["c", "o", "e", "p", "i", "m", "u", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ]
    columns := [("Lexeme", "COEPISSE"), ("System", "perf"), ("Agr", "p1")] }

def begin_perf_p2 : Form :=
  { id := "stump2012_begin_perf_p2"
    languageId := "lati1261"
    parameterId := "begin"
    form := "coepistis"
    segments := ["c", "o", "e", "p", "i", "s", "t", "i", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ]
    columns := [("Lexeme", "COEPISSE"), ("System", "perf"), ("Agr", "p2")] }

def begin_perf_p3 : Form :=
  { id := "stump2012_begin_perf_p3"
    languageId := "lati1261"
    parameterId := "begin"
    form := "coepērunt"
    segments := ["c", "o", "e", "p", "ē", "r", "u", "n", "t"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ]
    columns := [("Lexeme", "COEPISSE"), ("System", "perf"), ("Agr", "p3")] }

def war_acc_sg : Form :=
  { id := "stump2012_war_acc_sg"
    languageId := "lati1261"
    parameterId := "war"
    form := "bellum"
    segments := ["b", "e", "l", "l", "u", "m"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ]
    columns := [("Lexeme", "BELLUM"), ("Case", "acc"), ("Number", "sg")] }

def war_gen_sg : Form :=
  { id := "stump2012_war_gen_sg"
    languageId := "lati1261"
    parameterId := "war"
    form := "bellī"
    segments := ["b", "e", "l", "l", "ī"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ]
    columns := [("Lexeme", "BELLUM"), ("Case", "gen"), ("Number", "sg")] }

def war_dat_sg : Form :=
  { id := "stump2012_war_dat_sg"
    languageId := "lati1261"
    parameterId := "war"
    form := "bellō"
    segments := ["b", "e", "l", "l", "ō"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ]
    columns := [("Lexeme", "BELLUM"), ("Case", "dat"), ("Number", "sg")] }

def war_acc_pl : Form :=
  { id := "stump2012_war_acc_pl"
    languageId := "lati1261"
    parameterId := "war"
    form := "bella"
    segments := ["b", "e", "l", "l", "a"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ]
    columns := [("Lexeme", "BELLUM"), ("Case", "acc"), ("Number", "pl")] }

def war_gen_pl : Form :=
  { id := "stump2012_war_gen_pl"
    languageId := "lati1261"
    parameterId := "war"
    form := "bellōrum"
    segments := ["b", "e", "l", "l", "ō", "r", "u", "m"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ]
    columns := [("Lexeme", "BELLUM"), ("Case", "gen"), ("Number", "pl")] }

def war_dat_pl : Form :=
  { id := "stump2012_war_dat_pl"
    languageId := "lati1261"
    parameterId := "war"
    form := "bellīs"
    segments := ["b", "e", "l", "l", "ī", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ]
    columns := [("Lexeme", "BELLUM"), ("Case", "dat"), ("Number", "pl")] }

def praise_act_s1 : Form :=
  { id := "stump2012_praise_act_s1"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudō"
    segments := ["l", "a", "u", "d", "ō"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "act"), ("Agr", "s1")] }

def praise_act_s2 : Form :=
  { id := "stump2012_praise_act_s2"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudās"
    segments := ["l", "a", "u", "d", "ā", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "act"), ("Agr", "s2")] }

def praise_act_s3 : Form :=
  { id := "stump2012_praise_act_s3"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudat"
    segments := ["l", "a", "u", "d", "a", "t"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "act"), ("Agr", "s3")] }

def praise_act_p1 : Form :=
  { id := "stump2012_praise_act_p1"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudāmus"
    segments := ["l", "a", "u", "d", "ā", "m", "u", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "act"), ("Agr", "p1")] }

def praise_act_p2 : Form :=
  { id := "stump2012_praise_act_p2"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudātis"
    segments := ["l", "a", "u", "d", "ā", "t", "i", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "act"), ("Agr", "p2")] }

def praise_act_p3 : Form :=
  { id := "stump2012_praise_act_p3"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudant"
    segments := ["l", "a", "u", "d", "a", "n", "t"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "act"), ("Agr", "p3")] }

def praise_pass_s1 : Form :=
  { id := "stump2012_praise_pass_s1"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudor"
    segments := ["l", "a", "u", "d", "o", "r"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "pass"), ("Agr", "s1")] }

def praise_pass_s2 : Form :=
  { id := "stump2012_praise_pass_s2"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudāris"
    segments := ["l", "a", "u", "d", "ā", "r", "i", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "pass"), ("Agr", "s2")] }

def praise_pass_s3 : Form :=
  { id := "stump2012_praise_pass_s3"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudātur"
    segments := ["l", "a", "u", "d", "ā", "t", "u", "r"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "pass"), ("Agr", "s3")] }

def praise_pass_p1 : Form :=
  { id := "stump2012_praise_pass_p1"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudāmur"
    segments := ["l", "a", "u", "d", "ā", "m", "u", "r"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "pass"), ("Agr", "p1")] }

def praise_pass_p2 : Form :=
  { id := "stump2012_praise_pass_p2"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudāminī"
    segments := ["l", "a", "u", "d", "ā", "m", "i", "n", "ī"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "pass"), ("Agr", "p2")] }

def praise_pass_p3 : Form :=
  { id := "stump2012_praise_pass_p3"
    languageId := "lati1261"
    parameterId := "praise"
    form := "laudantur"
    segments := ["l", "a", "u", "d", "a", "n", "t", "u", "r"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "LAUDĀRE"), ("Voice", "pass"), ("Agr", "p3")] }

def urge_pass_s1 : Form :=
  { id := "stump2012_urge_pass_s1"
    languageId := "lati1261"
    parameterId := "urge"
    form := "hortor"
    segments := ["h", "o", "r", "t", "o", "r"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "HORTĀRĪ"), ("Voice", "pass"), ("Agr", "s1")] }

def urge_pass_s2 : Form :=
  { id := "stump2012_urge_pass_s2"
    languageId := "lati1261"
    parameterId := "urge"
    form := "hortāris"
    segments := ["h", "o", "r", "t", "ā", "r", "i", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "HORTĀRĪ"), ("Voice", "pass"), ("Agr", "s2")] }

def urge_pass_s3 : Form :=
  { id := "stump2012_urge_pass_s3"
    languageId := "lati1261"
    parameterId := "urge"
    form := "hortātur"
    segments := ["h", "o", "r", "t", "ā", "t", "u", "r"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "HORTĀRĪ"), ("Voice", "pass"), ("Agr", "s3")] }

def urge_pass_p1 : Form :=
  { id := "stump2012_urge_pass_p1"
    languageId := "lati1261"
    parameterId := "urge"
    form := "hortāmur"
    segments := ["h", "o", "r", "t", "ā", "m", "u", "r"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "HORTĀRĪ"), ("Voice", "pass"), ("Agr", "p1")] }

def urge_pass_p2 : Form :=
  { id := "stump2012_urge_pass_p2"
    languageId := "lati1261"
    parameterId := "urge"
    form := "hortāminī"
    segments := ["h", "o", "r", "t", "ā", "m", "i", "n", "ī"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "HORTĀRĪ"), ("Voice", "pass"), ("Agr", "p2")] }

def urge_pass_p3 : Form :=
  { id := "stump2012_urge_pass_p3"
    languageId := "lati1261"
    parameterId := "urge"
    form := "hortantur"
    segments := ["h", "o", "r", "t", "a", "n", "t", "u", "r"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ]
    columns := [("Lexeme", "HORTĀRĪ"), ("Voice", "pass"), ("Agr", "p3")] }

def carry_pres_s1 : Form :=
  { id := "stump2012_carry_pres_s1"
    languageId := "lati1261"
    parameterId := "carry"
    form := "ferō"
    segments := ["f", "e", "r", "ō"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "pres"), ("Agr", "s1")] }

def carry_pres_s2 : Form :=
  { id := "stump2012_carry_pres_s2"
    languageId := "lati1261"
    parameterId := "carry"
    form := "fers"
    segments := ["f", "e", "r", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "pres"), ("Agr", "s2")] }

def carry_pres_s3 : Form :=
  { id := "stump2012_carry_pres_s3"
    languageId := "lati1261"
    parameterId := "carry"
    form := "fert"
    segments := ["f", "e", "r", "t"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "pres"), ("Agr", "s3")] }

def carry_pres_p1 : Form :=
  { id := "stump2012_carry_pres_p1"
    languageId := "lati1261"
    parameterId := "carry"
    form := "ferimus"
    segments := ["f", "e", "r", "i", "m", "u", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "pres"), ("Agr", "p1")] }

def carry_pres_p2 : Form :=
  { id := "stump2012_carry_pres_p2"
    languageId := "lati1261"
    parameterId := "carry"
    form := "fertis"
    segments := ["f", "e", "r", "t", "i", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "pres"), ("Agr", "p2")] }

def carry_pres_p3 : Form :=
  { id := "stump2012_carry_pres_p3"
    languageId := "lati1261"
    parameterId := "carry"
    form := "ferunt"
    segments := ["f", "e", "r", "u", "n", "t"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "pres"), ("Agr", "p3")] }

def carry_perf_s1 : Form :=
  { id := "stump2012_carry_perf_s1"
    languageId := "lati1261"
    parameterId := "carry"
    form := "tulī"
    segments := ["t", "u", "l", "ī"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "perf"), ("Agr", "s1")] }

def carry_perf_s2 : Form :=
  { id := "stump2012_carry_perf_s2"
    languageId := "lati1261"
    parameterId := "carry"
    form := "tulistī"
    segments := ["t", "u", "l", "i", "s", "t", "ī"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "perf"), ("Agr", "s2")] }

def carry_perf_s3 : Form :=
  { id := "stump2012_carry_perf_s3"
    languageId := "lati1261"
    parameterId := "carry"
    form := "tulit"
    segments := ["t", "u", "l", "i", "t"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "perf"), ("Agr", "s3")] }

def carry_perf_p1 : Form :=
  { id := "stump2012_carry_perf_p1"
    languageId := "lati1261"
    parameterId := "carry"
    form := "tulimus"
    segments := ["t", "u", "l", "i", "m", "u", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "perf"), ("Agr", "p1")] }

def carry_perf_p2 : Form :=
  { id := "stump2012_carry_perf_p2"
    languageId := "lati1261"
    parameterId := "carry"
    form := "tulistis"
    segments := ["t", "u", "l", "i", "s", "t", "i", "s"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "perf"), ("Agr", "p2")] }

def carry_perf_p3 : Form :=
  { id := "stump2012_carry_perf_p3"
    languageId := "lati1261"
    parameterId := "carry"
    form := "tulērunt"
    segments := ["t", "u", "l", "ē", "r", "u", "n", "t"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ]
    columns := [("Lexeme", "FERRE"), ("System", "perf"), ("Agr", "p3")] }

def nek_p1sg : Form :=
  { id := "stump2012_nek_p1sg"
    languageId := "hung1274"
    parameterId := "nek"
    form := "nekem"
    segments := ["n", "e", "k", "e", "m"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ]
    columns := [("Lexeme", "NEK"), ("PersNum", "p1sg")] }

def nek_p2sg : Form :=
  { id := "stump2012_nek_p2sg"
    languageId := "hung1274"
    parameterId := "nek"
    form := "neked"
    segments := ["n", "e", "k", "e", "d"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ]
    columns := [("Lexeme", "NEK"), ("PersNum", "p2sg")] }

def benn_p1sg : Form :=
  { id := "stump2012_benn_p1sg"
    languageId := "hung1274"
    parameterId := "benn"
    form := "bennem"
    segments := ["b", "e", "n", "n", "e", "m"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ]
    columns := [("Lexeme", "BENN"), ("PersNum", "p1sg")] }

def benn_p2sg : Form :=
  { id := "stump2012_benn_p2sg"
    languageId := "hung1274"
    parameterId := "benn"
    form := "benned"
    segments := ["b", "e", "n", "n", "e", "d"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ]
    columns := [("Lexeme", "BENN"), ("PersNum", "p2sg")] }

def rajt_p1sg : Form :=
  { id := "stump2012_rajt_p1sg"
    languageId := "hung1274"
    parameterId := "rajt"
    form := "rajtam"
    segments := ["r", "a", "j", "t", "a", "m"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ]
    columns := [("Lexeme", "RAJT"), ("PersNum", "p1sg")] }

def rajt_p2sg : Form :=
  { id := "stump2012_rajt_p2sg"
    languageId := "hung1274"
    parameterId := "rajt"
    form := "rajtad"
    segments := ["r", "a", "j", "t", "a", "d"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ]
    columns := [("Lexeme", "RAJT"), ("PersNum", "p2sg")] }

def need_pres_s1 : Form :=
  { id := "stump2012_need_pres_s1"
    languageId := "oldn1244"
    parameterId := "need"
    form := "þarf"
    segments := ["þ", "a", "r", "f"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ]
    columns := [("Lexeme", "ÞURFA"), ("Tense", "pres"), ("Agr", "s1")] }

def need_pres_s2 : Form :=
  { id := "stump2012_need_pres_s2"
    languageId := "oldn1244"
    parameterId := "need"
    form := "þarft"
    segments := ["þ", "a", "r", "f", "t"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ]
    columns := [("Lexeme", "ÞURFA"), ("Tense", "pres"), ("Agr", "s2")] }

def need_pres_s3 : Form :=
  { id := "stump2012_need_pres_s3"
    languageId := "oldn1244"
    parameterId := "need"
    form := "þarf"
    segments := ["þ", "a", "r", "f"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ]
    columns := [("Lexeme", "ÞURFA"), ("Tense", "pres"), ("Agr", "s3")] }

def need_past_s1 : Form :=
  { id := "stump2012_need_past_s1"
    languageId := "oldn1244"
    parameterId := "need"
    form := "þurfta"
    segments := ["þ", "u", "r", "f", "t", "a"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ]
    columns := [("Lexeme", "ÞURFA"), ("Tense", "past"), ("Agr", "s1")] }

def need_past_s2 : Form :=
  { id := "stump2012_need_past_s2"
    languageId := "oldn1244"
    parameterId := "need"
    form := "þurftir"
    segments := ["þ", "u", "r", "f", "t", "i", "r"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ]
    columns := [("Lexeme", "ÞURFA"), ("Tense", "past"), ("Agr", "s2")] }

def need_past_s3 : Form :=
  { id := "stump2012_need_past_s3"
    languageId := "oldn1244"
    parameterId := "need"
    form := "þurfti"
    segments := ["þ", "u", "r", "f", "t", "i"]
    comment := ""
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ]
    columns := [("Lexeme", "ÞURFA"), ("Tense", "past"), ("Agr", "s3")] }

def all : List Form := [begin_perf_s1, begin_perf_s2, begin_perf_s3, begin_perf_p1, begin_perf_p2, begin_perf_p3, war_acc_sg, war_gen_sg, war_dat_sg, war_acc_pl, war_gen_pl, war_dat_pl, praise_act_s1, praise_act_s2, praise_act_s3, praise_act_p1, praise_act_p2, praise_act_p3, praise_pass_s1, praise_pass_s2, praise_pass_s3, praise_pass_p1, praise_pass_p2, praise_pass_p3, urge_pass_s1, urge_pass_s2, urge_pass_s3, urge_pass_p1, urge_pass_p2, urge_pass_p3, carry_pres_s1, carry_pres_s2, carry_pres_s3, carry_pres_p1, carry_pres_p2, carry_pres_p3, carry_perf_s1, carry_perf_s2, carry_perf_s3, carry_perf_p1, carry_perf_p2, carry_perf_p3, nek_p1sg, nek_p2sg, benn_p1sg, benn_p2sg, rajt_p1sg, rajt_p2sg, need_pres_s1, need_pres_s2, need_pres_s3, need_past_s1, need_past_s2, need_past_s3]

def parameters : List Parameter := [
  { id := "begin", name := "begin", description := "" },
  { id := "war", name := "war", description := "" },
  { id := "praise", name := "praise", description := "" },
  { id := "urge", name := "urge", description := "" },
  { id := "carry", name := "carry", description := "" },
  { id := "nek", name := "nek", description := "" },
  { id := "benn", name := "benn", description := "" },
  { id := "rajt", name := "rajt", description := "" },
  { id := "need", name := "need", description := "" }
]

def relations : List FormRelation := []

end Stump2012.Forms
