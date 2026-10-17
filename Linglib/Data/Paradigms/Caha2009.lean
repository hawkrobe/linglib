module

public import Linglib.Data.Paradigms.Schema

/-!
# `Caha2009`: paradigm data

Auto-generated from `Linglib/Data/Paradigms/Caha2009.json` by `scripts/gen_paradigms.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in
`namespace Caha2009.Paradigms`.
-/

@[expose] public section

namespace Caha2009.Paradigms

open Data.Paradigms

/-- The nominative singular cell, `Case=Nom|Number=Sing`. -/
def nom_sg : UD.MorphFeatures := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Sing }

/-- The nominative singular fem cell, `Case=Nom|Number=Sing|Gender=Fem`. -/
def nom_sg_f : UD.MorphFeatures := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The nominative singular masc cell, `Case=Nom|Number=Sing|Gender=Masc`. -/
def nom_sg_m : UD.MorphFeatures := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The nominative singular neut cell, `Case=Nom|Number=Sing|Gender=Neut`. -/
def nom_sg_n : UD.MorphFeatures := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The accusative singular cell, `Case=Acc|Number=Sing`. -/
def acc_sg : UD.MorphFeatures := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Sing }

/-- The accusative singular fem cell, `Case=Acc|Number=Sing|Gender=Fem`. -/
def acc_sg_f : UD.MorphFeatures := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The accusative singular masc cell, `Case=Acc|Number=Sing|Gender=Masc`. -/
def acc_sg_m : UD.MorphFeatures := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The accusative singular neut cell, `Case=Acc|Number=Sing|Gender=Neut`. -/
def acc_sg_n : UD.MorphFeatures := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The genitive singular cell, `Case=Gen|Number=Sing`. -/
def gen_sg : UD.MorphFeatures := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Sing }

/-- The genitive singular fem cell, `Case=Gen|Number=Sing|Gender=Fem`. -/
def gen_sg_f : UD.MorphFeatures := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The genitive singular masc cell, `Case=Gen|Number=Sing|Gender=Masc`. -/
def gen_sg_m : UD.MorphFeatures := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The genitive singular neut cell, `Case=Gen|Number=Sing|Gender=Neut`. -/
def gen_sg_n : UD.MorphFeatures := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The prepositional singular cell, `Case=Loc|Number=Sing`. -/
def prep_sg : UD.MorphFeatures := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Sing }

/-- The prepositional singular fem cell, `Case=Loc|Number=Sing|Gender=Fem`. -/
def prep_sg_f : UD.MorphFeatures := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The prepositional singular masc cell, `Case=Loc|Number=Sing|Gender=Masc`. -/
def prep_sg_m : UD.MorphFeatures := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The prepositional singular neut cell, `Case=Loc|Number=Sing|Gender=Neut`. -/
def prep_sg_n : UD.MorphFeatures := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The dative singular cell, `Case=Dat|Number=Sing`. -/
def dat_sg : UD.MorphFeatures := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Sing }

/-- The dative singular fem cell, `Case=Dat|Number=Sing|Gender=Fem`. -/
def dat_sg_f : UD.MorphFeatures := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The dative singular masc cell, `Case=Dat|Number=Sing|Gender=Masc`. -/
def dat_sg_m : UD.MorphFeatures := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The dative singular neut cell, `Case=Dat|Number=Sing|Gender=Neut`. -/
def dat_sg_n : UD.MorphFeatures := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The instrumental singular cell, `Case=Ins|Number=Sing`. -/
def ins_sg : UD.MorphFeatures := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Sing }

/-- The instrumental singular fem cell, `Case=Ins|Number=Sing|Gender=Fem`. -/
def ins_sg_f : UD.MorphFeatures := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The instrumental singular masc cell, `Case=Ins|Number=Sing|Gender=Masc`. -/
def ins_sg_m : UD.MorphFeatures := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The instrumental singular neut cell, `Case=Ins|Number=Sing|Gender=Neut`. -/
def ins_sg_n : UD.MorphFeatures := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The nominative dual cell, `Case=Nom|Number=Dual`. -/
def nom_du : UD.MorphFeatures := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Dual }

/-- The nominative dual masc cell, `Case=Nom|Number=Dual|Gender=Masc`. -/
def nom_du_m : UD.MorphFeatures := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The accusative dual cell, `Case=Acc|Number=Dual`. -/
def acc_du : UD.MorphFeatures := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Dual }

/-- The accusative dual masc cell, `Case=Acc|Number=Dual|Gender=Masc`. -/
def acc_du_m : UD.MorphFeatures := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The genitive dual cell, `Case=Gen|Number=Dual`. -/
def gen_du : UD.MorphFeatures := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Dual }

/-- The genitive dual masc cell, `Case=Gen|Number=Dual|Gender=Masc`. -/
def gen_du_m : UD.MorphFeatures := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The prepositional dual cell, `Case=Loc|Number=Dual`. -/
def prep_du : UD.MorphFeatures := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Dual }

/-- The prepositional dual masc cell, `Case=Loc|Number=Dual|Gender=Masc`. -/
def prep_du_m : UD.MorphFeatures := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The dative dual cell, `Case=Dat|Number=Dual`. -/
def dat_du : UD.MorphFeatures := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Dual }

/-- The dative dual masc cell, `Case=Dat|Number=Dual|Gender=Masc`. -/
def dat_du_m : UD.MorphFeatures := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The instrumental dual cell, `Case=Ins|Number=Dual`. -/
def ins_du : UD.MorphFeatures := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Dual }

/-- The instrumental dual masc cell, `Case=Ins|Number=Dual|Gender=Masc`. -/
def ins_du_m : UD.MorphFeatures := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The nominative plural cell, `Case=Nom|Number=Plur`. -/
def nom_pl : UD.MorphFeatures := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Plur }

/-- The nominative plural fem cell, `Case=Nom|Number=Plur|Gender=Fem`. -/
def nom_pl_f : UD.MorphFeatures := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The nominative plural masc cell, `Case=Nom|Number=Plur|Gender=Masc`. -/
def nom_pl_m : UD.MorphFeatures := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The nominative plural neut cell, `Case=Nom|Number=Plur|Gender=Neut`. -/
def nom_pl_n : UD.MorphFeatures := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The accusative plural cell, `Case=Acc|Number=Plur`. -/
def acc_pl : UD.MorphFeatures := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Plur }

/-- The accusative plural fem cell, `Case=Acc|Number=Plur|Gender=Fem`. -/
def acc_pl_f : UD.MorphFeatures := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The accusative plural masc cell, `Case=Acc|Number=Plur|Gender=Masc`. -/
def acc_pl_m : UD.MorphFeatures := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The accusative plural neut cell, `Case=Acc|Number=Plur|Gender=Neut`. -/
def acc_pl_n : UD.MorphFeatures := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The genitive plural cell, `Case=Gen|Number=Plur`. -/
def gen_pl : UD.MorphFeatures := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Plur }

/-- The genitive plural fem cell, `Case=Gen|Number=Plur|Gender=Fem`. -/
def gen_pl_f : UD.MorphFeatures := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The genitive plural masc cell, `Case=Gen|Number=Plur|Gender=Masc`. -/
def gen_pl_m : UD.MorphFeatures := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The genitive plural neut cell, `Case=Gen|Number=Plur|Gender=Neut`. -/
def gen_pl_n : UD.MorphFeatures := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The prepositional plural cell, `Case=Loc|Number=Plur`. -/
def prep_pl : UD.MorphFeatures := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Plur }

/-- The prepositional plural fem cell, `Case=Loc|Number=Plur|Gender=Fem`. -/
def prep_pl_f : UD.MorphFeatures := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The prepositional plural masc cell, `Case=Loc|Number=Plur|Gender=Masc`. -/
def prep_pl_m : UD.MorphFeatures := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The prepositional plural neut cell, `Case=Loc|Number=Plur|Gender=Neut`. -/
def prep_pl_n : UD.MorphFeatures := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The dative plural cell, `Case=Dat|Number=Plur`. -/
def dat_pl : UD.MorphFeatures := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Plur }

/-- The dative plural fem cell, `Case=Dat|Number=Plur|Gender=Fem`. -/
def dat_pl_f : UD.MorphFeatures := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The dative plural masc cell, `Case=Dat|Number=Plur|Gender=Masc`. -/
def dat_pl_m : UD.MorphFeatures := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The dative plural neut cell, `Case=Dat|Number=Plur|Gender=Neut`. -/
def dat_pl_n : UD.MorphFeatures := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The instrumental plural cell, `Case=Ins|Number=Plur`. -/
def ins_pl : UD.MorphFeatures := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Plur }

/-- The instrumental plural fem cell, `Case=Ins|Number=Plur|Gender=Fem`. -/
def ins_pl_f : UD.MorphFeatures := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The instrumental plural masc cell, `Case=Ins|Number=Plur|Gender=Masc`. -/
def ins_pl_m : UD.MorphFeatures := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The instrumental plural neut cell, `Case=Ins|Number=Plur|Gender=Neut`. -/
def ins_pl_n : UD.MorphFeatures := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

def srp_sin : Lexeme :=
  { id := "srp_sin", languageId := "sout1528", label := "sîn", meaning := "son" }

def srp_grad : Lexeme :=
  { id := "srp_grad", languageId := "sout1528", label := "grâd", meaning := "city" }

def srp_muz : Lexeme :=
  { id := "srp_muz", languageId := "sout1528", label := "muž", meaning := "man" }

def srp_selo : Lexeme :=
  { id := "srp_selo", languageId := "sout1528", label := "sèlo", meaning := "village" }

def srp_srce : Lexeme :=
  { id := "srp_srce", languageId := "sout1528", label := "srce", meaning := "heart" }

def srp_ovca : Lexeme :=
  { id := "srp_ovca", languageId := "sout1528", label := "òvca", meaning := "sheep" }

def srp_smrt : Lexeme :=
  { id := "srp_smrt", languageId := "sout1528", label := "smȑt", meaning := "death" }

def srp_ja : Lexeme :=
  { id := "srp_ja", languageId := "sout1528", label := "ja", meaning := "I" }

def srp_ti : Lexeme :=
  { id := "srp_ti", languageId := "sout1528", label := "ti", meaning := "you" }

def srp_on : Lexeme :=
  { id := "srp_on", languageId := "sout1528", label := "on/ono", meaning := "he, it" }

def srp_ona : Lexeme :=
  { id := "srp_ona", languageId := "sout1528", label := "ona", meaning := "she" }

def srp_mi : Lexeme :=
  { id := "srp_mi", languageId := "sout1528", label := "mi", meaning := "we" }

def srp_vi : Lexeme :=
  { id := "srp_vi", languageId := "sout1528", label := "vi", meaning := "you" }

def srp_oni : Lexeme :=
  { id := "srp_oni", languageId := "sout1528", label := "oni/ona/one", meaning := "they" }

def slv_miza : Lexeme :=
  { id := "slv_miza", languageId := "slov1268", label := "mízi", meaning := "table" }

def slv_breskev : Lexeme :=
  { id := "slv_breskev", languageId := "slov1268", label := "brêskev", meaning := "peach" }

def slv_jabolko : Lexeme :=
  { id := "slv_jabolko", languageId := "slov1268", label := "jábolko", meaning := "apple" }

def slv_kmet : Lexeme :=
  { id := "slv_kmet", languageId := "slov1268", label := "kmèta", meaning := "farmer" }

def slv_jaz : Lexeme :=
  { id := "slv_jaz", languageId := "slov1268", label := "jàz", meaning := "I" }

def slv_moj : Lexeme :=
  { id := "slv_moj", languageId := "slov1268", label := "mój", meaning := "my" }

def slv_dva : Lexeme :=
  { id := "slv_dva", languageId := "slov1268", label := "dvâ", meaning := "two" }

def slv_mi : Lexeme :=
  { id := "slv_mi", languageId := "slov1268", label := "mî", meaning := "we" }

def slv_midva : Lexeme :=
  { id := "slv_midva", languageId := "slov1268", label := "mîdva", meaning := "we two" }

def slv_nit : Lexeme :=
  { id := "slv_nit", languageId := "slov1268", label := "nìt", meaning := "thread" }

def slv_gospa : Lexeme :=
  { id := "slv_gospa", languageId := "slov1268", label := "gospá", meaning := "lady" }

def slv_dan : Lexeme :=
  { id := "slv_dan", languageId := "slov1268", label := "dní", meaning := "day" }

def slv_racunovodja : Lexeme :=
  { id := "slv_racunovodja", languageId := "slov1268", label := "računovodja", meaning := "accountant" }

def slv_ta : Lexeme :=
  { id := "slv_ta", languageId := "slov1268", label := "ta", meaning := "this" }

def slv_potnik : Lexeme :=
  { id := "slv_potnik", languageId := "slov1268", label := "pótnik", meaning := "traveller" }

def slv_tisti : Lexeme :=
  { id := "slv_tisti", languageId := "slov1268", label := "tîsto", meaning := "that" }

def slv_vas : Lexeme :=
  { id := "slv_vas", languageId := "slov1268", label := "váše", meaning := "your" }

def ces_okno : Lexeme :=
  { id := "ces_okno", languageId := "czec1258", label := "okno", meaning := "window" }

def ces_ulice : Lexeme :=
  { id := "ces_ulice", languageId := "czec1258", label := "ulice", meaning := "street" }

def ces_muz : Lexeme :=
  { id := "ces_muz", languageId := "czec1258", label := "muži", meaning := "man" }

def ces_dobry : Lexeme :=
  { id := "ces_dobry", languageId := "czec1258", label := "dobrý", meaning := "good" }

def ces_vetsi : Lexeme :=
  { id := "ces_vetsi", languageId := "czec1258", label := "větší", meaning := "bigger" }

def ces_oba : Lexeme :=
  { id := "ces_oba", languageId := "czec1258", label := "oba", meaning := "both" }

def ces_stroj : Lexeme :=
  { id := "ces_stroj", languageId := "czec1258", label := "stroj", meaning := "machine" }

def ces_kost : Lexeme :=
  { id := "ces_kost", languageId := "czec1258", label := "kosti", meaning := "bone" }

def ces_ten : Lexeme :=
  { id := "ces_ten", languageId := "czec1258", label := "ten", meaning := "that" }

def ces_vila : Lexeme :=
  { id := "ces_vila", languageId := "czec1258", label := "vila", meaning := "villa" }

def ces_misa : Lexeme :=
  { id := "ces_misa", languageId := "czec1258", label := "Míša", meaning := "Michelle" }

def ces_vul : Lexeme :=
  { id := "ces_vul", languageId := "czec1258", label := "vůl", meaning := "ox" }

def ces_hoch : Lexeme :=
  { id := "ces_hoch", languageId := "czec1258", label := "hoch", meaning := "boy" }

def ces_pan : Lexeme :=
  { id := "ces_pan", languageId := "czec1258", label := "pán", meaning := "sir" }

def ces_my : Lexeme :=
  { id := "ces_my", languageId := "czec1258", label := "my", meaning := "we" }

def ces_ona : Lexeme :=
  { id := "ces_ona", languageId := "czec1258", label := "ona", meaning := "she" }

def ces_nase : Lexeme :=
  { id := "ces_nase", languageId := "czec1258", label := "náš", meaning := "our" }

def ces_zatez : Lexeme :=
  { id := "ces_zatez", languageId := "czec1258", label := "zátěž", meaning := "stress" }

def ces_zena : Lexeme :=
  { id := "ces_zena", languageId := "czec1258", label := "žena", meaning := "woman" }

def ces_kluk : Lexeme :=
  { id := "ces_kluk", languageId := "czec1258", label := "kluk", meaning := "boy" }

def ces_pisen : Lexeme :=
  { id := "ces_pisen", languageId := "czec1258", label := "píseň", meaning := "song" }

def ces_hrad : Lexeme :=
  { id := "ces_hrad", languageId := "czec1258", label := "hrad", meaning := "castle" }

def ces_mesto : Lexeme :=
  { id := "ces_mesto", languageId := "czec1258", label := "město", meaning := "city" }

def ces_ono : Lexeme :=
  { id := "ces_ono", languageId := "czec1258", label := "ono", meaning := "it" }

def ces_oni : Lexeme :=
  { id := "ces_oni", languageId := "czec1258", label := "oni", meaning := "they" }

def ces_dva : Lexeme :=
  { id := "ces_dva", languageId := "czec1258", label := "dva", meaning := "two" }

def ces_pet : Lexeme :=
  { id := "ces_pet", languageId := "czec1258", label := "pět", meaning := "five" }

def slk_ona : Lexeme :=
  { id := "slk_ona", languageId := "slov1269", label := "ona", meaning := "she" }

def slk_nase : Lexeme :=
  { id := "slk_nase", languageId := "slov1269", label := "náš", meaning := "our" }

def slk_ulica : Lexeme :=
  { id := "slk_ulica", languageId := "slov1269", label := "ulica", meaning := "street" }

def slk_tlac : Lexeme :=
  { id := "slk_tlac", languageId := "slov1269", label := "tlač", meaning := "press" }

def ukr_kraj : Lexeme :=
  { id := "ukr_kraj", languageId := "ukra1253", label := "kraj", meaning := "region" }

def ukr_velykyj : Lexeme :=
  { id := "ukr_velykyj", languageId := "ukra1253", label := "velíkıj", meaning := "big" }

def ukr_znannja : Lexeme :=
  { id := "ukr_znannja", languageId := "ukra1253", label := "znannjá", meaning := "knowledge" }

def ukr_my : Lexeme :=
  { id := "ukr_my", languageId := "ukra1253", label := "mı", meaning := "we" }

def ukr_kasyr : Lexeme :=
  { id := "ukr_kasyr", languageId := "ukra1253", label := "kasír", meaning := "cashier" }

def ukr_maty : Lexeme :=
  { id := "ukr_maty", languageId := "ukra1253", label := "mátı", meaning := "mother" }

def ukr_ruka : Lexeme :=
  { id := "ukr_ruka", languageId := "ukra1253", label := "ruká", meaning := "hand" }

def ukr_ja : Lexeme :=
  { id := "ukr_ja", languageId := "ukra1253", label := "ja", meaning := "I" }

def ukr_sto : Lexeme :=
  { id := "ukr_sto", languageId := "ukra1253", label := "sto", meaning := "hundred" }

def ukr_bezkrajij : Lexeme :=
  { id := "ukr_bezkrajij", languageId := "ukra1253", label := "bezkrajij", meaning := "endless" }

def srp_sin_sg_nom : Form :=
  { id := "srp_sin_sg_nom", lexeme := srp_sin, cell := nom_sg, form := "sîn",
    analysed := "sîn", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_sg_acc : Form :=
  { id := "srp_sin_sg_acc", lexeme := srp_sin, cell := acc_sg, form := "sîna",
    analysed := "sîna", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_sg_gen : Form :=
  { id := "srp_sin_sg_gen", lexeme := srp_sin, cell := gen_sg, form := "sîna",
    analysed := "sîna", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_sg_prep : Form :=
  { id := "srp_sin_sg_prep", lexeme := srp_sin, cell := prep_sg, form := "sînu",
    analysed := "sînu", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_sg_dat : Form :=
  { id := "srp_sin_sg_dat", lexeme := srp_sin, cell := dat_sg, form := "sînu",
    analysed := "sînu", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_sg_ins : Form :=
  { id := "srp_sin_sg_ins", lexeme := srp_sin, cell := ins_sg, form := "sînom",
    analysed := "sînom", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_nom : Form :=
  { id := "srp_grad_sg_nom", lexeme := srp_grad, cell := nom_sg, form := "grâd",
    analysed := "grâd", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_acc : Form :=
  { id := "srp_grad_sg_acc", lexeme := srp_grad, cell := acc_sg, form := "grâd",
    analysed := "grâd", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_gen : Form :=
  { id := "srp_grad_sg_gen", lexeme := srp_grad, cell := gen_sg, form := "grâda",
    analysed := "grâda", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_prep : Form :=
  { id := "srp_grad_sg_prep", lexeme := srp_grad, cell := prep_sg, form := "grádu",
    analysed := "grádu", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_dat : Form :=
  { id := "srp_grad_sg_dat", lexeme := srp_grad, cell := dat_sg, form := "grâdu",
    analysed := "grâdu", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_ins : Form :=
  { id := "srp_grad_sg_ins", lexeme := srp_grad, cell := ins_sg, form := "grâdom",
    analysed := "grâdom", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_nom : Form :=
  { id := "srp_muz_sg_nom", lexeme := srp_muz, cell := nom_sg, form := "muž",
    analysed := "muž", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_acc : Form :=
  { id := "srp_muz_sg_acc", lexeme := srp_muz, cell := acc_sg, form := "muža",
    analysed := "muža", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_gen : Form :=
  { id := "srp_muz_sg_gen", lexeme := srp_muz, cell := gen_sg, form := "muža",
    analysed := "muža", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_prep : Form :=
  { id := "srp_muz_sg_prep", lexeme := srp_muz, cell := prep_sg, form := "mužu",
    analysed := "mužu", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_dat : Form :=
  { id := "srp_muz_sg_dat", lexeme := srp_muz, cell := dat_sg, form := "mužu",
    analysed := "mužu", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_ins : Form :=
  { id := "srp_muz_sg_ins", lexeme := srp_muz, cell := ins_sg, form := "mužem",
    analysed := "mužem", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_nom : Form :=
  { id := "srp_selo_sg_nom", lexeme := srp_selo, cell := nom_sg, form := "sèlo",
    analysed := "sèlo", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_acc : Form :=
  { id := "srp_selo_sg_acc", lexeme := srp_selo, cell := acc_sg, form := "sèlo",
    analysed := "sèlo", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_gen : Form :=
  { id := "srp_selo_sg_gen", lexeme := srp_selo, cell := gen_sg, form := "sèla",
    analysed := "sèla", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_prep : Form :=
  { id := "srp_selo_sg_prep", lexeme := srp_selo, cell := prep_sg, form := "sèlu",
    analysed := "sèlu", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_dat : Form :=
  { id := "srp_selo_sg_dat", lexeme := srp_selo, cell := dat_sg, form := "sèlu",
    analysed := "sèlu", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_ins : Form :=
  { id := "srp_selo_sg_ins", lexeme := srp_selo, cell := ins_sg, form := "sèlom",
    analysed := "sèlom", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_nom : Form :=
  { id := "srp_srce_sg_nom", lexeme := srp_srce, cell := nom_sg, form := "srce",
    analysed := "srce", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_acc : Form :=
  { id := "srp_srce_sg_acc", lexeme := srp_srce, cell := acc_sg, form := "srce",
    analysed := "srce", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_gen : Form :=
  { id := "srp_srce_sg_gen", lexeme := srp_srce, cell := gen_sg, form := "srca",
    analysed := "srca", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_prep : Form :=
  { id := "srp_srce_sg_prep", lexeme := srp_srce, cell := prep_sg, form := "srcu",
    analysed := "srcu", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_dat : Form :=
  { id := "srp_srce_sg_dat", lexeme := srp_srce, cell := dat_sg, form := "srcu",
    analysed := "srcu", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_ins : Form :=
  { id := "srp_srce_sg_ins", lexeme := srp_srce, cell := ins_sg, form := "srcem",
    analysed := "srcem", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_nom : Form :=
  { id := "srp_ovca_sg_nom", lexeme := srp_ovca, cell := nom_sg, form := "òvca",
    analysed := "òvca", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_acc : Form :=
  { id := "srp_ovca_sg_acc", lexeme := srp_ovca, cell := acc_sg, form := "òvcu",
    analysed := "òvcu", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_gen : Form :=
  { id := "srp_ovca_sg_gen", lexeme := srp_ovca, cell := gen_sg, form := "òvcē",
    analysed := "òvcē", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_prep : Form :=
  { id := "srp_ovca_sg_prep", lexeme := srp_ovca, cell := prep_sg, form := "òvci",
    analysed := "òvci", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_dat : Form :=
  { id := "srp_ovca_sg_dat", lexeme := srp_ovca, cell := dat_sg, form := "òvci",
    analysed := "òvci", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_ins : Form :=
  { id := "srp_ovca_sg_ins", lexeme := srp_ovca, cell := ins_sg, form := "òvcōm",
    analysed := "òvcōm", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_nom : Form :=
  { id := "srp_smrt_sg_nom", lexeme := srp_smrt, cell := nom_sg, form := "smȑt",
    analysed := "smȑt", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_acc : Form :=
  { id := "srp_smrt_sg_acc", lexeme := srp_smrt, cell := acc_sg, form := "smȑt",
    analysed := "smȑt", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_gen : Form :=
  { id := "srp_smrt_sg_gen", lexeme := srp_smrt, cell := gen_sg, form := "smȑti",
    analysed := "smȑti", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_prep : Form :=
  { id := "srp_smrt_sg_prep", lexeme := srp_smrt, cell := prep_sg, form := "smȑti",
    analysed := "smȑti", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_dat : Form :=
  { id := "srp_smrt_sg_dat", lexeme := srp_smrt, cell := dat_sg, form := "smȑti",
    analysed := "smȑti", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_ins : Form :=
  { id := "srp_smrt_sg_ins", lexeme := srp_smrt, cell := ins_sg, form := "smr̀ću",
    analysed := "smr̀ću", source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_pl_nom : Form :=
  { id := "srp_sin_pl_nom", lexeme := srp_sin, cell := nom_pl, form := "sȉnovi",
    analysed := "sȉnovi", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_sin_pl_acc : Form :=
  { id := "srp_sin_pl_acc", lexeme := srp_sin, cell := acc_pl, form := "sȉnove",
    analysed := "sȉnove", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_sin_pl_gen : Form :=
  { id := "srp_sin_pl_gen", lexeme := srp_sin, cell := gen_pl, form := "sinóvā",
    analysed := "sinóvā", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_sin_pl_prep : Form :=
  { id := "srp_sin_pl_prep", lexeme := srp_sin, cell := prep_pl, form := "sȉnovima",
    analysed := "sȉnovima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_sin_pl_dat : Form :=
  { id := "srp_sin_pl_dat", lexeme := srp_sin, cell := dat_pl, form := "sȉnovima",
    analysed := "sȉnovima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_sin_pl_ins : Form :=
  { id := "srp_sin_pl_ins", lexeme := srp_sin, cell := ins_pl, form := "sȉnovima",
    analysed := "sȉnovima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_nom : Form :=
  { id := "srp_grad_pl_nom", lexeme := srp_grad, cell := nom_pl, form := "grȁdovi",
    analysed := "grȁdovi", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_acc : Form :=
  { id := "srp_grad_pl_acc", lexeme := srp_grad, cell := acc_pl, form := "grȁdove",
    analysed := "grȁdove", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_gen : Form :=
  { id := "srp_grad_pl_gen", lexeme := srp_grad, cell := gen_pl, form := "gradóvā",
    analysed := "gradóvā", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_prep : Form :=
  { id := "srp_grad_pl_prep", lexeme := srp_grad, cell := prep_pl, form := "grȁdovima",
    analysed := "grȁdovima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_dat : Form :=
  { id := "srp_grad_pl_dat", lexeme := srp_grad, cell := dat_pl, form := "grȁdovima",
    analysed := "grȁdovima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_ins : Form :=
  { id := "srp_grad_pl_ins", lexeme := srp_grad, cell := ins_pl, form := "grȁdovima",
    analysed := "grȁdovima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_nom : Form :=
  { id := "srp_muz_pl_nom", lexeme := srp_muz, cell := nom_pl, form := "muževi",
    analysed := "muževi", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_acc : Form :=
  { id := "srp_muz_pl_acc", lexeme := srp_muz, cell := acc_pl, form := "muževe",
    analysed := "muževe", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_gen : Form :=
  { id := "srp_muz_pl_gen", lexeme := srp_muz, cell := gen_pl, form := "mȕžēvā",
    analysed := "mȕžēvā", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_prep : Form :=
  { id := "srp_muz_pl_prep", lexeme := srp_muz, cell := prep_pl, form := "muževima",
    analysed := "muževima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_dat : Form :=
  { id := "srp_muz_pl_dat", lexeme := srp_muz, cell := dat_pl, form := "muževima",
    analysed := "muževima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_ins : Form :=
  { id := "srp_muz_pl_ins", lexeme := srp_muz, cell := ins_pl, form := "muževima",
    analysed := "muževima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_nom : Form :=
  { id := "srp_selo_pl_nom", lexeme := srp_selo, cell := nom_pl, form := "sȅla",
    analysed := "sȅla", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_acc : Form :=
  { id := "srp_selo_pl_acc", lexeme := srp_selo, cell := acc_pl, form := "sȅla",
    analysed := "sȅla", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_gen : Form :=
  { id := "srp_selo_pl_gen", lexeme := srp_selo, cell := gen_pl, form := "sêlā",
    analysed := "sêlā", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_prep : Form :=
  { id := "srp_selo_pl_prep", lexeme := srp_selo, cell := prep_pl, form := "sȅlima",
    analysed := "sȅlima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_dat : Form :=
  { id := "srp_selo_pl_dat", lexeme := srp_selo, cell := dat_pl, form := "sȅlima",
    analysed := "sȅlima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_ins : Form :=
  { id := "srp_selo_pl_ins", lexeme := srp_selo, cell := ins_pl, form := "sȅlima",
    analysed := "sȅlima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_nom : Form :=
  { id := "srp_srce_pl_nom", lexeme := srp_srce, cell := nom_pl, form := "srca",
    analysed := "srca", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_acc : Form :=
  { id := "srp_srce_pl_acc", lexeme := srp_srce, cell := acc_pl, form := "srca",
    analysed := "srca", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_gen : Form :=
  { id := "srp_srce_pl_gen", lexeme := srp_srce, cell := gen_pl, form := "sr̂cā",
    analysed := "sr̂cā", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_prep : Form :=
  { id := "srp_srce_pl_prep", lexeme := srp_srce, cell := prep_pl, form := "srcima",
    analysed := "srcima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_dat : Form :=
  { id := "srp_srce_pl_dat", lexeme := srp_srce, cell := dat_pl, form := "srcima",
    analysed := "srcima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_ins : Form :=
  { id := "srp_srce_pl_ins", lexeme := srp_srce, cell := ins_pl, form := "srcima",
    analysed := "srcima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_nom : Form :=
  { id := "srp_ovca_pl_nom", lexeme := srp_ovca, cell := nom_pl, form := "ôvce",
    analysed := "ôvce", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_acc : Form :=
  { id := "srp_ovca_pl_acc", lexeme := srp_ovca, cell := acc_pl, form := "ôvce",
    analysed := "ôvce", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_gen : Form :=
  { id := "srp_ovca_pl_gen", lexeme := srp_ovca, cell := gen_pl, form := "ovácā",
    analysed := "ovácā", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_prep : Form :=
  { id := "srp_ovca_pl_prep", lexeme := srp_ovca, cell := prep_pl, form := "óvcama",
    analysed := "óvcama", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_dat : Form :=
  { id := "srp_ovca_pl_dat", lexeme := srp_ovca, cell := dat_pl, form := "óvcama",
    analysed := "óvcama", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_ins : Form :=
  { id := "srp_ovca_pl_ins", lexeme := srp_ovca, cell := ins_pl, form := "óvcama",
    analysed := "óvcama", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_nom : Form :=
  { id := "srp_smrt_pl_nom", lexeme := srp_smrt, cell := nom_pl, form := "smȑti",
    analysed := "smȑti", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_acc : Form :=
  { id := "srp_smrt_pl_acc", lexeme := srp_smrt, cell := acc_pl, form := "smȑti",
    analysed := "smȑti", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_gen : Form :=
  { id := "srp_smrt_pl_gen", lexeme := srp_smrt, cell := gen_pl, form := "smr̂tī",
    analysed := "smr̂tī", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_prep : Form :=
  { id := "srp_smrt_pl_prep", lexeme := srp_smrt, cell := prep_pl, form := "smȑtima",
    analysed := "smȑtima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_dat : Form :=
  { id := "srp_smrt_pl_dat", lexeme := srp_smrt, cell := dat_pl, form := "smȑtima",
    analysed := "smȑtima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_ins : Form :=
  { id := "srp_smrt_pl_ins", lexeme := srp_smrt, cell := ins_pl, form := "smȑtima",
    analysed := "smȑtima", source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ja_nom : Form :=
  { id := "srp_ja_nom", lexeme := srp_ja, cell := nom_sg, form := "ja",
    analysed := "ja", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ja_acc : Form :=
  { id := "srp_ja_acc", lexeme := srp_ja, cell := acc_sg, form := "mene",
    analysed := "mene", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ja_gen : Form :=
  { id := "srp_ja_gen", lexeme := srp_ja, cell := gen_sg, form := "mene",
    analysed := "mene", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ja_prep : Form :=
  { id := "srp_ja_prep", lexeme := srp_ja, cell := prep_sg, form := "meni",
    analysed := "meni", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ja_dat : Form :=
  { id := "srp_ja_dat", lexeme := srp_ja, cell := dat_sg, form := "meni",
    analysed := "meni", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ja_ins : Form :=
  { id := "srp_ja_ins", lexeme := srp_ja, cell := ins_sg, form := "mnom",
    analysed := "mnom", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_nom : Form :=
  { id := "srp_ti_nom", lexeme := srp_ti, cell := nom_sg, form := "ti",
    analysed := "ti", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_acc : Form :=
  { id := "srp_ti_acc", lexeme := srp_ti, cell := acc_sg, form := "tebe",
    analysed := "tebe", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_gen : Form :=
  { id := "srp_ti_gen", lexeme := srp_ti, cell := gen_sg, form := "tebe",
    analysed := "tebe", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_prep : Form :=
  { id := "srp_ti_prep", lexeme := srp_ti, cell := prep_sg, form := "tebi",
    analysed := "tebi", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_dat : Form :=
  { id := "srp_ti_dat", lexeme := srp_ti, cell := dat_sg, form := "tebi",
    analysed := "tebi", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_ins : Form :=
  { id := "srp_ti_ins", lexeme := srp_ti, cell := ins_sg, form := "tobom",
    analysed := "tobom", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_nom : Form :=
  { id := "srp_on_nom", lexeme := srp_on, cell := nom_sg, form := "on/ono",
    analysed := "on/ono", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_acc : Form :=
  { id := "srp_on_acc", lexeme := srp_on, cell := acc_sg, form := "njega",
    analysed := "njega", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_gen : Form :=
  { id := "srp_on_gen", lexeme := srp_on, cell := gen_sg, form := "njega",
    analysed := "njega", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_prep : Form :=
  { id := "srp_on_prep", lexeme := srp_on, cell := prep_sg, form := "njemu",
    analysed := "njemu", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_dat : Form :=
  { id := "srp_on_dat", lexeme := srp_on, cell := dat_sg, form := "njemu",
    analysed := "njemu", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_ins : Form :=
  { id := "srp_on_ins", lexeme := srp_on, cell := ins_sg, form := "njim",
    analysed := "njim", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_nom : Form :=
  { id := "srp_ona_nom", lexeme := srp_ona, cell := nom_sg, form := "ona",
    analysed := "ona", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_acc : Form :=
  { id := "srp_ona_acc", lexeme := srp_ona, cell := acc_sg, form := "nju",
    analysed := "nju", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_gen : Form :=
  { id := "srp_ona_gen", lexeme := srp_ona, cell := gen_sg, form := "nje",
    analysed := "nje", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_prep : Form :=
  { id := "srp_ona_prep", lexeme := srp_ona, cell := prep_sg, form := "njoj",
    analysed := "njoj", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_dat : Form :=
  { id := "srp_ona_dat", lexeme := srp_ona, cell := dat_sg, form := "njoj",
    analysed := "njoj", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_ins : Form :=
  { id := "srp_ona_ins", lexeme := srp_ona, cell := ins_sg, form := "njom",
    analysed := "njom", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_nom : Form :=
  { id := "srp_mi_nom", lexeme := srp_mi, cell := nom_pl, form := "mi",
    analysed := "mi", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_acc : Form :=
  { id := "srp_mi_acc", lexeme := srp_mi, cell := acc_pl, form := "nas",
    analysed := "nas", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_gen : Form :=
  { id := "srp_mi_gen", lexeme := srp_mi, cell := gen_pl, form := "nas",
    analysed := "nas", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_prep : Form :=
  { id := "srp_mi_prep", lexeme := srp_mi, cell := prep_pl, form := "nama",
    analysed := "nama", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_dat : Form :=
  { id := "srp_mi_dat", lexeme := srp_mi, cell := dat_pl, form := "nama",
    analysed := "nama", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_ins : Form :=
  { id := "srp_mi_ins", lexeme := srp_mi, cell := ins_pl, form := "nama",
    analysed := "nama", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_nom : Form :=
  { id := "srp_vi_nom", lexeme := srp_vi, cell := nom_pl, form := "vi",
    analysed := "vi", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_acc : Form :=
  { id := "srp_vi_acc", lexeme := srp_vi, cell := acc_pl, form := "vas",
    analysed := "vas", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_gen : Form :=
  { id := "srp_vi_gen", lexeme := srp_vi, cell := gen_pl, form := "vas",
    analysed := "vas", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_prep : Form :=
  { id := "srp_vi_prep", lexeme := srp_vi, cell := prep_pl, form := "vama",
    analysed := "vama", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_dat : Form :=
  { id := "srp_vi_dat", lexeme := srp_vi, cell := dat_pl, form := "vama",
    analysed := "vama", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_ins : Form :=
  { id := "srp_vi_ins", lexeme := srp_vi, cell := ins_pl, form := "vama",
    analysed := "vama", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_nom : Form :=
  { id := "srp_oni_nom", lexeme := srp_oni, cell := nom_pl, form := "oni/ona/one",
    analysed := "oni/ona/one", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_acc : Form :=
  { id := "srp_oni_acc", lexeme := srp_oni, cell := acc_pl, form := "njih",
    analysed := "njih", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_gen : Form :=
  { id := "srp_oni_gen", lexeme := srp_oni, cell := gen_pl, form := "njih",
    analysed := "njih", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_prep : Form :=
  { id := "srp_oni_prep", lexeme := srp_oni, cell := prep_pl, form := "njima",
    analysed := "njima", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_dat : Form :=
  { id := "srp_oni_dat", lexeme := srp_oni, cell := dat_pl, form := "njima",
    analysed := "njima", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_ins : Form :=
  { id := "srp_oni_ins", lexeme := srp_oni, cell := ins_pl, form := "njima",
    analysed := "njima", source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def slv_miza_du_nom : Form :=
  { id := "slv_miza_du_nom", lexeme := slv_miza, cell := nom_du, form := "mízi",
    analysed := "míz-i", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_miza_du_acc : Form :=
  { id := "slv_miza_du_acc", lexeme := slv_miza, cell := acc_du, form := "mízi",
    analysed := "míz-i", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_miza_du_gen : Form :=
  { id := "slv_miza_du_gen", lexeme := slv_miza, cell := gen_du, form := "mîz",
    analysed := "mîz", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_miza_du_prep : Form :=
  { id := "slv_miza_du_prep", lexeme := slv_miza, cell := prep_du, form := "mízah",
    analysed := "míz-ah", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_miza_du_dat : Form :=
  { id := "slv_miza_du_dat", lexeme := slv_miza, cell := dat_du, form := "mízama",
    analysed := "míz-ama", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_miza_du_ins : Form :=
  { id := "slv_miza_du_ins", lexeme := slv_miza, cell := ins_du, form := "mízama",
    analysed := "míz-ama", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_nom : Form :=
  { id := "slv_breskev_sg_nom", lexeme := slv_breskev, cell := nom_sg, form := "brêskev",
    analysed := "brêskev-ø", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_acc : Form :=
  { id := "slv_breskev_sg_acc", lexeme := slv_breskev, cell := acc_sg, form := "brêskev",
    analysed := "brêskev-ø", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_gen : Form :=
  { id := "slv_breskev_sg_gen", lexeme := slv_breskev, cell := gen_sg, form := "brêskve",
    analysed := "brêskv-e", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_prep : Form :=
  { id := "slv_breskev_sg_prep", lexeme := slv_breskev, cell := prep_sg, form := "brêskvi",
    analysed := "brêskv-i", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_dat : Form :=
  { id := "slv_breskev_sg_dat", lexeme := slv_breskev, cell := dat_sg, form := "brêskvi",
    analysed := "brêskv-i", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_ins : Form :=
  { id := "slv_breskev_sg_ins", lexeme := slv_breskev, cell := ins_sg, form := "brêskvijo",
    analysed := "brêskv-ijo", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_nom : Form :=
  { id := "slv_breskev_pl_nom", lexeme := slv_breskev, cell := nom_pl, form := "brêskve",
    analysed := "brêskv-e", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_acc : Form :=
  { id := "slv_breskev_pl_acc", lexeme := slv_breskev, cell := acc_pl, form := "brêskve",
    analysed := "brêskv-e", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_gen : Form :=
  { id := "slv_breskev_pl_gen", lexeme := slv_breskev, cell := gen_pl, form := "brêskv",
    analysed := "brêskv-ø", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_prep : Form :=
  { id := "slv_breskev_pl_prep", lexeme := slv_breskev, cell := prep_pl, form := "brêskvah",
    analysed := "brêskv-ah", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_dat : Form :=
  { id := "slv_breskev_pl_dat", lexeme := slv_breskev, cell := dat_pl, form := "brêskvam",
    analysed := "brêskv-am", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_ins : Form :=
  { id := "slv_breskev_pl_ins", lexeme := slv_breskev, cell := ins_pl, form := "brêskvami",
    analysed := "brêskv-ami", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_nom : Form :=
  { id := "slv_jabolko_sg_nom", lexeme := slv_jabolko, cell := nom_sg, form := "jábolko",
    analysed := "jábolk-o", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_acc : Form :=
  { id := "slv_jabolko_sg_acc", lexeme := slv_jabolko, cell := acc_sg, form := "jábolko",
    analysed := "jábolk-o", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_gen : Form :=
  { id := "slv_jabolko_sg_gen", lexeme := slv_jabolko, cell := gen_sg, form := "jábolka",
    analysed := "jábolk-a", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_prep : Form :=
  { id := "slv_jabolko_sg_prep", lexeme := slv_jabolko, cell := prep_sg, form := "jábolku",
    analysed := "jábolk-u", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_dat : Form :=
  { id := "slv_jabolko_sg_dat", lexeme := slv_jabolko, cell := dat_sg, form := "jábolku",
    analysed := "jábolk-u", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_ins : Form :=
  { id := "slv_jabolko_sg_ins", lexeme := slv_jabolko, cell := ins_sg, form := "jábolkom",
    analysed := "jábolk-om", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_nom : Form :=
  { id := "slv_kmet_du_nom", lexeme := slv_kmet, cell := nom_du, form := "kmèta",
    analysed := "kmèt-a", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_acc : Form :=
  { id := "slv_kmet_du_acc", lexeme := slv_kmet, cell := acc_du, form := "kmèta",
    analysed := "kmèt-a", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_gen : Form :=
  { id := "slv_kmet_du_gen", lexeme := slv_kmet, cell := gen_du, form := "kmêtov",
    analysed := "kmêt-ov", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_prep : Form :=
  { id := "slv_kmet_du_prep", lexeme := slv_kmet, cell := prep_du, form := "kmētih",
    analysed := "kmēt-ih", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_dat : Form :=
  { id := "slv_kmet_du_dat", lexeme := slv_kmet, cell := dat_du, form := "kmétoma",
    analysed := "kmét-oma", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_ins : Form :=
  { id := "slv_kmet_du_ins", lexeme := slv_kmet, cell := ins_du, form := "kmétoma",
    analysed := "kmét-oma", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_nom : Form :=
  { id := "slv_kmet_sg_nom", lexeme := slv_kmet, cell := nom_sg, form := "kmèt",
    analysed := "kmèt-ø", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_acc : Form :=
  { id := "slv_kmet_sg_acc", lexeme := slv_kmet, cell := acc_sg, form := "kméta",
    analysed := "kmét-a", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_gen : Form :=
  { id := "slv_kmet_sg_gen", lexeme := slv_kmet, cell := gen_sg, form := "kméta",
    analysed := "kmét-a", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_prep : Form :=
  { id := "slv_kmet_sg_prep", lexeme := slv_kmet, cell := prep_sg, form := "kmêtu",
    analysed := "kmêt-u", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_dat : Form :=
  { id := "slv_kmet_sg_dat", lexeme := slv_kmet, cell := dat_sg, form := "kmétu",
    analysed := "kmét-u", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_ins : Form :=
  { id := "slv_kmet_sg_ins", lexeme := slv_kmet, cell := ins_sg, form := "kmétom",
    analysed := "kmét-om", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_nom : Form :=
  { id := "slv_jaz_nom", lexeme := slv_jaz, cell := nom_sg, form := "jàz",
    analysed := "jàz", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_acc : Form :=
  { id := "slv_jaz_acc", lexeme := slv_jaz, cell := acc_sg, form := "mȩ́ne",
    analysed := "mȩ́n-e", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_gen : Form :=
  { id := "slv_jaz_gen", lexeme := slv_jaz, cell := gen_sg, form := "mȩ́ne",
    analysed := "mȩ́n-e", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_prep : Form :=
  { id := "slv_jaz_prep", lexeme := slv_jaz, cell := prep_sg, form := "mȩ́ni",
    analysed := "mȩ́n-i", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_dat : Form :=
  { id := "slv_jaz_dat", lexeme := slv_jaz, cell := dat_sg, form := "mȩ́ni",
    analysed := "mȩ́n-i", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_ins : Form :=
  { id := "slv_jaz_ins", lexeme := slv_jaz, cell := ins_sg, form := "menój",
    analysed := "men-ój", source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_moj_mpl_nom : Form :=
  { id := "slv_moj_mpl_nom", lexeme := slv_moj, cell := nom_pl_m, form := "mo̧ji",
    analysed := "mo̧j-i", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_moj_mpl_acc : Form :=
  { id := "slv_moj_mpl_acc", lexeme := slv_moj, cell := acc_pl_m, form := "mo̧ji",
    analysed := "mo̧j-i", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_moj_mpl_gen : Form :=
  { id := "slv_moj_mpl_gen", lexeme := slv_moj, cell := gen_pl_m, form := "mo̧jih",
    analysed := "mo̧j-ih", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_moj_mpl_prep : Form :=
  { id := "slv_moj_mpl_prep", lexeme := slv_moj, cell := prep_pl_m, form := "mo̧jih",
    analysed := "mo̧j-ih", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_moj_mpl_dat : Form :=
  { id := "slv_moj_mpl_dat", lexeme := slv_moj, cell := dat_pl_m, form := "mo̧jim",
    analysed := "mo̧j-im", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_moj_mpl_ins : Form :=
  { id := "slv_moj_mpl_ins", lexeme := slv_moj, cell := ins_pl_m, form := "mo̧jimi",
    analysed := "mo̧j-imi", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_nom : Form :=
  { id := "slv_dva_nom", lexeme := slv_dva, cell := nom_du, form := "dvâ",
    analysed := "dv-â", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_acc : Form :=
  { id := "slv_dva_acc", lexeme := slv_dva, cell := acc_du, form := "dvâ",
    analysed := "dv-â", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_gen : Form :=
  { id := "slv_dva_gen", lexeme := slv_dva, cell := gen_du, form := "dvēh",
    analysed := "dv-ēh", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_prep : Form :=
  { id := "slv_dva_prep", lexeme := slv_dva, cell := prep_du, form := "dvēh",
    analysed := "dv-ēh", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_dat : Form :=
  { id := "slv_dva_dat", lexeme := slv_dva, cell := dat_du, form := "dvēma",
    analysed := "dv-ēma", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_ins : Form :=
  { id := "slv_dva_ins", lexeme := slv_dva, cell := ins_du, form := "dvēma",
    analysed := "dv-ēma", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_nom : Form :=
  { id := "slv_mi_nom", lexeme := slv_mi, cell := nom_pl, form := "mî",
    analysed := "mî", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_acc : Form :=
  { id := "slv_mi_acc", lexeme := slv_mi, cell := acc_pl, form := "nàs",
    analysed := "nà-s", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_gen : Form :=
  { id := "slv_mi_gen", lexeme := slv_mi, cell := gen_pl, form := "nàs",
    analysed := "nà-s", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_prep : Form :=
  { id := "slv_mi_prep", lexeme := slv_mi, cell := prep_pl, form := "nàs",
    analysed := "nà-s", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_dat : Form :=
  { id := "slv_mi_dat", lexeme := slv_mi, cell := dat_pl, form := "nàm",
    analysed := "nàm", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_ins : Form :=
  { id := "slv_mi_ins", lexeme := slv_mi, cell := ins_pl, form := "na̧mi",
    analysed := "na̧mi", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_nom : Form :=
  { id := "slv_midva_nom", lexeme := slv_midva, cell := nom_du, form := "mîdva",
    analysed := "mîdva", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_acc : Form :=
  { id := "slv_midva_acc", lexeme := slv_midva, cell := acc_du, form := "náju",
    analysed := "ná-ju", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_gen : Form :=
  { id := "slv_midva_gen", lexeme := slv_midva, cell := gen_du, form := "náju",
    analysed := "ná-ju", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_prep : Form :=
  { id := "slv_midva_prep", lexeme := slv_midva, cell := prep_du, form := "náju",
    analysed := "ná-ju", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_dat : Form :=
  { id := "slv_midva_dat", lexeme := slv_midva, cell := dat_du, form := "náma",
    analysed := "ná-ma", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_ins : Form :=
  { id := "slv_midva_ins", lexeme := slv_midva, cell := ins_du, form := "náma",
    analysed := "ná-ma", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_nom : Form :=
  { id := "slv_nit_sg_nom", lexeme := slv_nit, cell := nom_sg, form := "nìt",
    analysed := "nìt", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_acc : Form :=
  { id := "slv_nit_sg_acc", lexeme := slv_nit, cell := acc_sg, form := "nìt",
    analysed := "nìt", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_gen : Form :=
  { id := "slv_nit_sg_gen", lexeme := slv_nit, cell := gen_sg, form := "níti",
    analysed := "nít-i", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_prep : Form :=
  { id := "slv_nit_sg_prep", lexeme := slv_nit, cell := prep_sg, form := "níti",
    analysed := "nít-i", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_dat : Form :=
  { id := "slv_nit_sg_dat", lexeme := slv_nit, cell := dat_sg, form := "níti",
    analysed := "nít-i", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_ins : Form :=
  { id := "slv_nit_sg_ins", lexeme := slv_nit, cell := ins_sg, form := "nítjo",
    analysed := "nít-jo", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_nom : Form :=
  { id := "slv_gospa_sg_nom", lexeme := slv_gospa, cell := nom_sg, form := "gospá",
    analysed := "gosp-á", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_acc : Form :=
  { id := "slv_gospa_sg_acc", lexeme := slv_gospa, cell := acc_sg, form := "gospó",
    analysed := "gosp-ó", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_gen : Form :=
  { id := "slv_gospa_sg_gen", lexeme := slv_gospa, cell := gen_sg, form := "gospé",
    analysed := "gosp-é", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_prep : Form :=
  { id := "slv_gospa_sg_prep", lexeme := slv_gospa, cell := prep_sg, form := "gospé",
    analysed := "gosp-é", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_dat : Form :=
  { id := "slv_gospa_sg_dat", lexeme := slv_gospa, cell := dat_sg, form := "gospé",
    analysed := "gosp-é", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_ins : Form :=
  { id := "slv_gospa_sg_ins", lexeme := slv_gospa, cell := ins_sg, form := "gospó",
    analysed := "gosp-ó", source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dan_du_nom : Form :=
  { id := "slv_dan_du_nom", lexeme := slv_dan, cell := nom_du, form := "dní",
    analysed := "dn-í", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_dan_du_acc : Form :=
  { id := "slv_dan_du_acc", lexeme := slv_dan, cell := acc_du, form := "dní",
    analysed := "dn-í", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_dan_du_gen : Form :=
  { id := "slv_dan_du_gen", lexeme := slv_dan, cell := gen_du, form := "dní",
    analysed := "dn-í", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_dan_du_prep : Form :=
  { id := "slv_dan_du_prep", lexeme := slv_dan, cell := prep_du, form := "dnéh",
    analysed := "dn-éh", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_dan_du_dat : Form :=
  { id := "slv_dan_du_dat", lexeme := slv_dan, cell := dat_du, form := "dnéma",
    analysed := "dn-éma", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_dan_du_ins : Form :=
  { id := "slv_dan_du_ins", lexeme := slv_dan, cell := ins_du, form := "dnéma",
    analysed := "dn-éma", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_nom : Form :=
  { id := "slv_racunovodja_sg_nom", lexeme := slv_racunovodja, cell := nom_sg, form := "računovodja",
    analysed := "računovod-ja", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_acc : Form :=
  { id := "slv_racunovodja_sg_acc", lexeme := slv_racunovodja, cell := acc_sg, form := "računovodja",
    analysed := "računovod-ja", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_gen : Form :=
  { id := "slv_racunovodja_sg_gen", lexeme := slv_racunovodja, cell := gen_sg, form := "računovodja",
    analysed := "računovod-ja", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_prep : Form :=
  { id := "slv_racunovodja_sg_prep", lexeme := slv_racunovodja, cell := prep_sg, form := "računovodju",
    analysed := "računovod-ju", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_dat : Form :=
  { id := "slv_racunovodja_sg_dat", lexeme := slv_racunovodja, cell := dat_sg, form := "računovodju",
    analysed := "računovod-ju", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_ins : Form :=
  { id := "slv_racunovodja_sg_ins", lexeme := slv_racunovodja, cell := ins_sg, form := "računovodjem",
    analysed := "računovod-jem", source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_ta_n_nom : Form :=
  { id := "slv_ta_n_nom", lexeme := slv_ta, cell := nom_sg_n, form := "tô",
    analysed := "tô", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_n_acc : Form :=
  { id := "slv_ta_n_acc", lexeme := slv_ta, cell := acc_sg_n, form := "tô",
    analysed := "tô", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_n_gen : Form :=
  { id := "slv_ta_n_gen", lexeme := slv_ta, cell := gen_sg_n, form := "têga",
    analysed := "têga", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_n_prep : Form :=
  { id := "slv_ta_n_prep", lexeme := slv_ta, cell := prep_sg_n, form := "têm",
    analysed := "têm", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_n_dat : Form :=
  { id := "slv_ta_n_dat", lexeme := slv_ta, cell := dat_sg_n, form := "têmu",
    analysed := "têmu", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_n_ins : Form :=
  { id := "slv_ta_n_ins", lexeme := slv_ta, cell := ins_sg_n, form := "têm",
    analysed := "têm", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_nom : Form :=
  { id := "slv_potnik_pl_nom", lexeme := slv_potnik, cell := nom_pl, form := "pótniki",
    analysed := "pótnik-i", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_acc : Form :=
  { id := "slv_potnik_pl_acc", lexeme := slv_potnik, cell := acc_pl, form := "pótnike",
    analysed := "pótnik-e", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_gen : Form :=
  { id := "slv_potnik_pl_gen", lexeme := slv_potnik, cell := gen_pl, form := "pótnikov",
    analysed := "pótnik-ov", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_prep : Form :=
  { id := "slv_potnik_pl_prep", lexeme := slv_potnik, cell := prep_pl, form := "pótnikih",
    analysed := "pótnik-ih", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_dat : Form :=
  { id := "slv_potnik_pl_dat", lexeme := slv_potnik, cell := dat_pl, form := "pótnikom",
    analysed := "pótnik-om", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_ins : Form :=
  { id := "slv_potnik_pl_ins", lexeme := slv_potnik, cell := ins_pl, form := "pótniki",
    analysed := "pótnik-i", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_nom : Form :=
  { id := "slv_ta_f_nom", lexeme := slv_ta, cell := nom_sg_f, form := "tâ",
    analysed := "tâ", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_acc : Form :=
  { id := "slv_ta_f_acc", lexeme := slv_ta, cell := acc_sg_f, form := "tô",
    analysed := "tô", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_gen : Form :=
  { id := "slv_ta_f_gen", lexeme := slv_ta, cell := gen_sg_f, form := "tê",
    analysed := "tê", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_prep : Form :=
  { id := "slv_ta_f_prep", lexeme := slv_ta, cell := prep_sg_f, form := "têj",
    analysed := "têj", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_dat : Form :=
  { id := "slv_ta_f_dat", lexeme := slv_ta, cell := dat_sg_f, form := "têj",
    analysed := "têj", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_ins : Form :=
  { id := "slv_ta_f_ins", lexeme := slv_ta, cell := ins_sg_f, form := "tô",
    analysed := "tô", source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_tisti_n_nom : Form :=
  { id := "slv_tisti_n_nom", lexeme := slv_tisti, cell := nom_sg_n, form := "tîsto",
    analysed := "tîs-t-o", source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_tisti_n_acc : Form :=
  { id := "slv_tisti_n_acc", lexeme := slv_tisti, cell := acc_sg_n, form := "tîsto",
    analysed := "tîs-t-o", source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_tisti_n_gen : Form :=
  { id := "slv_tisti_n_gen", lexeme := slv_tisti, cell := gen_sg_n, form := "tîstega",
    analysed := "tîs-t-ega", source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_tisti_n_prep : Form :=
  { id := "slv_tisti_n_prep", lexeme := slv_tisti, cell := prep_sg_n, form := "tîstem",
    analysed := "tîs-t-em", source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_tisti_n_dat : Form :=
  { id := "slv_tisti_n_dat", lexeme := slv_tisti, cell := dat_sg_n, form := "tîstemu",
    analysed := "tîs-t-emu", source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_tisti_n_ins : Form :=
  { id := "slv_tisti_n_ins", lexeme := slv_tisti, cell := ins_sg_n, form := "tîstim",
    analysed := "tîs-t-im", source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_vas_n_nom : Form :=
  { id := "slv_vas_n_nom", lexeme := slv_vas, cell := nom_sg_n, form := "váše",
    analysed := "váš-e", source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def slv_vas_n_acc : Form :=
  { id := "slv_vas_n_acc", lexeme := slv_vas, cell := acc_sg_n, form := "váše",
    analysed := "váš-e", source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def slv_vas_n_gen : Form :=
  { id := "slv_vas_n_gen", lexeme := slv_vas, cell := gen_sg_n, form := "vášega",
    analysed := "váš-ega", source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def slv_vas_n_prep : Form :=
  { id := "slv_vas_n_prep", lexeme := slv_vas, cell := prep_sg_n, form := "vášem",
    analysed := "váš-em", source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def slv_vas_n_dat : Form :=
  { id := "slv_vas_n_dat", lexeme := slv_vas, cell := dat_sg_n, form := "vášemu",
    analysed := "váš-emu", source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def slv_vas_n_ins : Form :=
  { id := "slv_vas_n_ins", lexeme := slv_vas, cell := ins_sg_n, form := "vášim",
    analysed := "váš-im", source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def ces_okno_sg_nom : Form :=
  { id := "ces_okno_sg_nom", lexeme := ces_okno, cell := nom_sg, form := "okno",
    analysed := "okn-o", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_okno_sg_acc : Form :=
  { id := "ces_okno_sg_acc", lexeme := ces_okno, cell := acc_sg, form := "okno",
    analysed := "okn-o", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_okno_sg_gen : Form :=
  { id := "ces_okno_sg_gen", lexeme := ces_okno, cell := gen_sg, form := "okna",
    analysed := "okn-a", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_okno_sg_prep : Form :=
  { id := "ces_okno_sg_prep", lexeme := ces_okno, cell := prep_sg, form := "okně",
    analysed := "okn-ě", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_okno_sg_dat : Form :=
  { id := "ces_okno_sg_dat", lexeme := ces_okno, cell := dat_sg, form := "oknu",
    analysed := "okn-u", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_okno_sg_ins : Form :=
  { id := "ces_okno_sg_ins", lexeme := ces_okno, cell := ins_sg, form := "oknem",
    analysed := "okn-em", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_nom : Form :=
  { id := "ces_ulice_sg_nom", lexeme := ces_ulice, cell := nom_sg, form := "ulice",
    analysed := "ulic-e", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_acc : Form :=
  { id := "ces_ulice_sg_acc", lexeme := ces_ulice, cell := acc_sg, form := "ulici",
    analysed := "ulic-i", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_gen : Form :=
  { id := "ces_ulice_sg_gen", lexeme := ces_ulice, cell := gen_sg, form := "ulice",
    analysed := "ulic-e", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_prep : Form :=
  { id := "ces_ulice_sg_prep", lexeme := ces_ulice, cell := prep_sg, form := "ulici",
    analysed := "ulic-i", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_dat : Form :=
  { id := "ces_ulice_sg_dat", lexeme := ces_ulice, cell := dat_sg, form := "ulici",
    analysed := "ulic-i", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_ins : Form :=
  { id := "ces_ulice_sg_ins", lexeme := ces_ulice, cell := ins_sg, form := "ulicí",
    analysed := "ulic-í", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_nom : Form :=
  { id := "ces_muz_pl_nom", lexeme := ces_muz, cell := nom_pl, form := "muži",
    analysed := "muž-i", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_acc : Form :=
  { id := "ces_muz_pl_acc", lexeme := ces_muz, cell := acc_pl, form := "muže",
    analysed := "muž-e", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_gen : Form :=
  { id := "ces_muz_pl_gen", lexeme := ces_muz, cell := gen_pl, form := "mužů",
    analysed := "muž-ů", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_prep : Form :=
  { id := "ces_muz_pl_prep", lexeme := ces_muz, cell := prep_pl, form := "mužích",
    analysed := "muž-ích", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_dat : Form :=
  { id := "ces_muz_pl_dat", lexeme := ces_muz, cell := dat_pl, form := "mužům",
    analysed := "muž-ům", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_ins : Form :=
  { id := "ces_muz_pl_ins", lexeme := ces_muz, cell := ins_pl, form := "muži",
    analysed := "muž-i", source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_sg_nom : Form :=
  { id := "ces_muz_sg_nom", lexeme := ces_muz, cell := nom_sg, form := "muž",
    analysed := "muž", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_muz_sg_acc : Form :=
  { id := "ces_muz_sg_acc", lexeme := ces_muz, cell := acc_sg, form := "muže",
    analysed := "muž-e", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_muz_sg_gen : Form :=
  { id := "ces_muz_sg_gen", lexeme := ces_muz, cell := gen_sg, form := "muže",
    analysed := "muž-e", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_muz_sg_prep : Form :=
  { id := "ces_muz_sg_prep", lexeme := ces_muz, cell := prep_sg, form := "muži",
    analysed := "muž-i", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_muz_sg_dat : Form :=
  { id := "ces_muz_sg_dat", lexeme := ces_muz, cell := dat_sg, form := "muži",
    analysed := "muž-i", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_muz_sg_ins : Form :=
  { id := "ces_muz_sg_ins", lexeme := ces_muz, cell := ins_sg, form := "mužem",
    analysed := "muž-em", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_nom : Form :=
  { id := "ces_dobry_fsg_nom", lexeme := ces_dobry, cell := nom_sg_f, form := "dobrá",
    analysed := "dobr-á", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_acc : Form :=
  { id := "ces_dobry_fsg_acc", lexeme := ces_dobry, cell := acc_sg_f, form := "dobrou",
    analysed := "dobr-ou", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_gen : Form :=
  { id := "ces_dobry_fsg_gen", lexeme := ces_dobry, cell := gen_sg_f, form := "dobré",
    analysed := "dobr-é", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_prep : Form :=
  { id := "ces_dobry_fsg_prep", lexeme := ces_dobry, cell := prep_sg_f, form := "dobré",
    analysed := "dobr-é", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_dat : Form :=
  { id := "ces_dobry_fsg_dat", lexeme := ces_dobry, cell := dat_sg_f, form := "dobré",
    analysed := "dobr-é", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_ins : Form :=
  { id := "ces_dobry_fsg_ins", lexeme := ces_dobry, cell := ins_sg_f, form := "dobrou",
    analysed := "dobr-ou", source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_mpl_2_nom : Form :=
  { id := "ces_dobry_mpl_2_nom", lexeme := ces_dobry, cell := nom_pl_m, form := "dobrý",
    analysed := "dobrý", source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_dobry_mpl_2_acc : Form :=
  { id := "ces_dobry_mpl_2_acc", lexeme := ces_dobry, cell := acc_pl_m, form := "dobrý",
    analysed := "dobrý", source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_dobry_mpl_2_gen : Form :=
  { id := "ces_dobry_mpl_2_gen", lexeme := ces_dobry, cell := gen_pl_m, form := "dobrých",
    analysed := "dobrý-ch", source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_dobry_mpl_2_prep : Form :=
  { id := "ces_dobry_mpl_2_prep", lexeme := ces_dobry, cell := prep_pl_m, form := "dobrých",
    analysed := "dobrý-ch", source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_dobry_mpl_2_dat : Form :=
  { id := "ces_dobry_mpl_2_dat", lexeme := ces_dobry, cell := dat_pl_m, form := "dobrým",
    analysed := "dobrý-m", source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_dobry_mpl_2_ins : Form :=
  { id := "ces_dobry_mpl_2_ins", lexeme := ces_dobry, cell := ins_pl_m, form := "dobrými",
    analysed := "dobrý-mi", source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_vetsi_msg_nom : Form :=
  { id := "ces_vetsi_msg_nom", lexeme := ces_vetsi, cell := nom_sg_m, form := "větší",
    analysed := "větš-í", source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_vetsi_msg_acc : Form :=
  { id := "ces_vetsi_msg_acc", lexeme := ces_vetsi, cell := acc_sg_m, form := "většího",
    analysed := "větš-ího", source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_vetsi_msg_gen : Form :=
  { id := "ces_vetsi_msg_gen", lexeme := ces_vetsi, cell := gen_sg_m, form := "většího",
    analysed := "větš-ího", source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_vetsi_msg_prep : Form :=
  { id := "ces_vetsi_msg_prep", lexeme := ces_vetsi, cell := prep_sg_m, form := "větším",
    analysed := "větš-ím", source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_vetsi_msg_dat : Form :=
  { id := "ces_vetsi_msg_dat", lexeme := ces_vetsi, cell := dat_sg_m, form := "většímu",
    analysed := "větš-ímu", source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_vetsi_msg_ins : Form :=
  { id := "ces_vetsi_msg_ins", lexeme := ces_vetsi, cell := ins_sg_m, form := "větším",
    analysed := "větš-ím", source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_oba_nom : Form :=
  { id := "ces_oba_nom", lexeme := ces_oba, cell := nom_du, form := "oba",
    analysed := "ob-a", source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_oba_acc : Form :=
  { id := "ces_oba_acc", lexeme := ces_oba, cell := acc_du, form := "oba",
    analysed := "ob-a", source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_oba_gen : Form :=
  { id := "ces_oba_gen", lexeme := ces_oba, cell := gen_du, form := "obou",
    analysed := "ob-ou", source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_oba_prep : Form :=
  { id := "ces_oba_prep", lexeme := ces_oba, cell := prep_du, form := "obou",
    analysed := "ob-ou", source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_oba_dat : Form :=
  { id := "ces_oba_dat", lexeme := ces_oba, cell := dat_du, form := "oběma",
    analysed := "ob-ěma", source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_oba_ins : Form :=
  { id := "ces_oba_ins", lexeme := ces_oba, cell := ins_du, form := "oběma",
    analysed := "ob-ěma", source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_stroj_sg_nom : Form :=
  { id := "ces_stroj_sg_nom", lexeme := ces_stroj, cell := nom_sg, form := "stroj",
    analysed := "stroj-ø", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_sg_acc : Form :=
  { id := "ces_stroj_sg_acc", lexeme := ces_stroj, cell := acc_sg, form := "stroj",
    analysed := "stroj-ø", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_sg_gen : Form :=
  { id := "ces_stroj_sg_gen", lexeme := ces_stroj, cell := gen_sg, form := "stroje",
    analysed := "stroj-e", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_sg_prep : Form :=
  { id := "ces_stroj_sg_prep", lexeme := ces_stroj, cell := prep_sg, form := "stroji",
    analysed := "stroj-i", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_sg_dat : Form :=
  { id := "ces_stroj_sg_dat", lexeme := ces_stroj, cell := dat_sg, form := "stroji",
    analysed := "stroj-i", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_sg_ins : Form :=
  { id := "ces_stroj_sg_ins", lexeme := ces_stroj, cell := ins_sg, form := "strojem",
    analysed := "stroj-em", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_nom : Form :=
  { id := "ces_stroj_pl_nom", lexeme := ces_stroj, cell := nom_pl, form := "stroje",
    analysed := "stroj-e", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_acc : Form :=
  { id := "ces_stroj_pl_acc", lexeme := ces_stroj, cell := acc_pl, form := "stroje",
    analysed := "stroj-e", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_gen : Form :=
  { id := "ces_stroj_pl_gen", lexeme := ces_stroj, cell := gen_pl, form := "strojů",
    analysed := "stroj-ů", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_prep : Form :=
  { id := "ces_stroj_pl_prep", lexeme := ces_stroj, cell := prep_pl, form := "strojích",
    analysed := "stroj-ích", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_dat : Form :=
  { id := "ces_stroj_pl_dat", lexeme := ces_stroj, cell := dat_pl, form := "strojům",
    analysed := "stroj-ům", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_ins : Form :=
  { id := "ces_stroj_pl_ins", lexeme := ces_stroj, cell := ins_pl, form := "stroji",
    analysed := "stroj-i", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_nom : Form :=
  { id := "ces_kost_pl_nom", lexeme := ces_kost, cell := nom_pl, form := "kosti",
    analysed := "kost-i", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_acc : Form :=
  { id := "ces_kost_pl_acc", lexeme := ces_kost, cell := acc_pl, form := "kosti",
    analysed := "kost-i", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_gen : Form :=
  { id := "ces_kost_pl_gen", lexeme := ces_kost, cell := gen_pl, form := "kostí",
    analysed := "kost-í", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_prep : Form :=
  { id := "ces_kost_pl_prep", lexeme := ces_kost, cell := prep_pl, form := "kostech",
    analysed := "kost-ech", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_dat : Form :=
  { id := "ces_kost_pl_dat", lexeme := ces_kost, cell := dat_pl, form := "kostem",
    analysed := "kost-em", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_ins : Form :=
  { id := "ces_kost_pl_ins", lexeme := ces_kost, cell := ins_pl, form := "kostmi",
    analysed := "kost-mi", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_nom : Form :=
  { id := "ces_ty_nom", lexeme := ces_ten, cell := nom_pl_f, form := "ty",
    analysed := "t-y", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_acc : Form :=
  { id := "ces_ty_acc", lexeme := ces_ten, cell := acc_pl_f, form := "ty",
    analysed := "t-y", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_gen : Form :=
  { id := "ces_ty_gen", lexeme := ces_ten, cell := gen_pl_f, form := "těch",
    analysed := "t-ěch", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_prep : Form :=
  { id := "ces_ty_prep", lexeme := ces_ten, cell := prep_pl_f, form := "těch",
    analysed := "t-ěch", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_dat : Form :=
  { id := "ces_ty_dat", lexeme := ces_ten, cell := dat_pl_f, form := "těm",
    analysed := "t-ěm", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_ins : Form :=
  { id := "ces_ty_ins", lexeme := ces_ten, cell := ins_pl_f, form := "těmi",
    analysed := "t-ěmi", source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_vila_sg_nom : Form :=
  { id := "ces_vila_sg_nom", lexeme := ces_vila, cell := nom_sg, form := "vila",
    analysed := "vil-a", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vila_sg_acc : Form :=
  { id := "ces_vila_sg_acc", lexeme := ces_vila, cell := acc_sg, form := "vilu",
    analysed := "vil-u", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vila_sg_gen : Form :=
  { id := "ces_vila_sg_gen", lexeme := ces_vila, cell := gen_sg, form := "vily",
    analysed := "vil-y", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vila_sg_prep : Form :=
  { id := "ces_vila_sg_prep", lexeme := ces_vila, cell := prep_sg, form := "vile",
    analysed := "vil-e", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vila_sg_dat : Form :=
  { id := "ces_vila_sg_dat", lexeme := ces_vila, cell := dat_sg, form := "vile",
    analysed := "vil-e", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vila_sg_ins : Form :=
  { id := "ces_vila_sg_ins", lexeme := ces_vila, cell := ins_sg, form := "vilou",
    analysed := "vil-ou", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_nom : Form :=
  { id := "ces_misa_sg_nom", lexeme := ces_misa, cell := nom_sg, form := "Míša",
    analysed := "Míš-a", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_acc : Form :=
  { id := "ces_misa_sg_acc", lexeme := ces_misa, cell := acc_sg, form := "Míšu",
    analysed := "Míš-u", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_gen : Form :=
  { id := "ces_misa_sg_gen", lexeme := ces_misa, cell := gen_sg, form := "Míši",
    analysed := "Míš-i", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_prep : Form :=
  { id := "ces_misa_sg_prep", lexeme := ces_misa, cell := prep_sg, form := "Míše",
    analysed := "Míš-e", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_dat : Form :=
  { id := "ces_misa_sg_dat", lexeme := ces_misa, cell := dat_sg, form := "Míše",
    analysed := "Míš-e", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_ins : Form :=
  { id := "ces_misa_sg_ins", lexeme := ces_misa, cell := ins_sg, form := "Míšou",
    analysed := "Míš-ou", source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vul_pl_nom : Form :=
  { id := "ces_vul_pl_nom", lexeme := ces_vul, cell := nom_pl, form := "voli",
    analysed := "vol-i", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_vul_pl_acc : Form :=
  { id := "ces_vul_pl_acc", lexeme := ces_vul, cell := acc_pl, form := "voly",
    analysed := "vol-y", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_vul_pl_gen : Form :=
  { id := "ces_vul_pl_gen", lexeme := ces_vul, cell := gen_pl, form := "volů",
    analysed := "vol-ů", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_vul_pl_prep : Form :=
  { id := "ces_vul_pl_prep", lexeme := ces_vul, cell := prep_pl, form := "volech",
    analysed := "vol-ech", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_vul_pl_dat : Form :=
  { id := "ces_vul_pl_dat", lexeme := ces_vul, cell := dat_pl, form := "volům",
    analysed := "vol-ům", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_vul_pl_ins : Form :=
  { id := "ces_vul_pl_ins", lexeme := ces_vul, cell := ins_pl, form := "voly",
    analysed := "vol-y", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_nom : Form :=
  { id := "ces_hoch_pl_nom", lexeme := ces_hoch, cell := nom_pl, form := "hoši",
    analysed := "hoš-i", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_acc : Form :=
  { id := "ces_hoch_pl_acc", lexeme := ces_hoch, cell := acc_pl, form := "hochy",
    analysed := "hoch-y", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_gen : Form :=
  { id := "ces_hoch_pl_gen", lexeme := ces_hoch, cell := gen_pl, form := "hochů",
    analysed := "hoch-ů", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_prep : Form :=
  { id := "ces_hoch_pl_prep", lexeme := ces_hoch, cell := prep_pl, form := "hoších",
    analysed := "hoš-ích", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_dat : Form :=
  { id := "ces_hoch_pl_dat", lexeme := ces_hoch, cell := dat_pl, form := "hochům",
    analysed := "hoch-ům", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_ins : Form :=
  { id := "ces_hoch_pl_ins", lexeme := ces_hoch, cell := ins_pl, form := "hochy",
    analysed := "hoch-y", source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_pan_sg_nom : Form :=
  { id := "ces_pan_sg_nom", lexeme := ces_pan, cell := nom_sg, form := "pán",
    analysed := "pán", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_pan_sg_acc : Form :=
  { id := "ces_pan_sg_acc", lexeme := ces_pan, cell := acc_sg, form := "pána",
    analysed := "pán-a", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_pan_sg_gen : Form :=
  { id := "ces_pan_sg_gen", lexeme := ces_pan, cell := gen_sg, form := "pána",
    analysed := "pán-a", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_pan_sg_prep : Form :=
  { id := "ces_pan_sg_prep", lexeme := ces_pan, cell := prep_sg, form := "pánovi",
    analysed := "pán-ovi", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_pan_sg_dat : Form :=
  { id := "ces_pan_sg_dat", lexeme := ces_pan, cell := dat_sg, form := "pánovi",
    analysed := "pán-ovi", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_pan_sg_ins : Form :=
  { id := "ces_pan_sg_ins", lexeme := ces_pan, cell := ins_sg, form := "pánem",
    analysed := "pán-em", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_nom : Form :=
  { id := "ces_ten_nom", lexeme := ces_ten, cell := nom_sg_m, form := "ten",
    analysed := "t-en", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_acc : Form :=
  { id := "ces_ten_acc", lexeme := ces_ten, cell := acc_sg_m, form := "toho",
    analysed := "t-oho", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_gen : Form :=
  { id := "ces_ten_gen", lexeme := ces_ten, cell := gen_sg_m, form := "toho",
    analysed := "t-oho", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_prep : Form :=
  { id := "ces_ten_prep", lexeme := ces_ten, cell := prep_sg_m, form := "tom",
    analysed := "t-om", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_dat : Form :=
  { id := "ces_ten_dat", lexeme := ces_ten, cell := dat_sg_m, form := "tomu",
    analysed := "t-omu", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_ins : Form :=
  { id := "ces_ten_ins", lexeme := ces_ten, cell := ins_sg_m, form := "tím",
    analysed := "t-ím", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_nom : Form :=
  { id := "ces_my_2_nom", lexeme := ces_my, cell := nom_pl, form := "my",
    analysed := "my", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_acc : Form :=
  { id := "ces_my_2_acc", lexeme := ces_my, cell := acc_pl, form := "nás",
    analysed := "ná-s", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_gen : Form :=
  { id := "ces_my_2_gen", lexeme := ces_my, cell := gen_pl, form := "nás",
    analysed := "ná-s", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_prep : Form :=
  { id := "ces_my_2_prep", lexeme := ces_my, cell := prep_pl, form := "nás",
    analysed := "ná-s", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_dat : Form :=
  { id := "ces_my_2_dat", lexeme := ces_my, cell := dat_pl, form := "nám",
    analysed := "ná-m", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_ins : Form :=
  { id := "ces_my_2_ins", lexeme := ces_my, cell := ins_pl, form := "náma",
    analysed := "ná-ma", source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ona_nom : Form :=
  { id := "ces_ona_nom", lexeme := ces_ona, cell := nom_sg, form := "ona",
    analysed := "ona", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_ona_acc : Form :=
  { id := "ces_ona_acc", lexeme := ces_ona, cell := acc_sg, form := "ji",
    analysed := "j-i", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_ona_gen : Form :=
  { id := "ces_ona_gen", lexeme := ces_ona, cell := gen_sg, form := "jí",
    analysed := "j-í", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_ona_prep : Form :=
  { id := "ces_ona_prep", lexeme := ces_ona, cell := prep_sg, form := "jí",
    analysed := "j-í", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_ona_dat : Form :=
  { id := "ces_ona_dat", lexeme := ces_ona, cell := dat_sg, form := "jí",
    analysed := "j-í", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_ona_ins : Form :=
  { id := "ces_ona_ins", lexeme := ces_ona, cell := ins_sg, form := "jí",
    analysed := "j-í", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_nom : Form :=
  { id := "ces_nase_fsg_nom", lexeme := ces_nase, cell := nom_sg_f, form := "naše",
    analysed := "naš-e", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_acc : Form :=
  { id := "ces_nase_fsg_acc", lexeme := ces_nase, cell := acc_sg_f, form := "naši",
    analysed := "naš-i", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_gen : Form :=
  { id := "ces_nase_fsg_gen", lexeme := ces_nase, cell := gen_sg_f, form := "naší",
    analysed := "naš-í", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_prep : Form :=
  { id := "ces_nase_fsg_prep", lexeme := ces_nase, cell := prep_sg_f, form := "naší",
    analysed := "naš-í", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_dat : Form :=
  { id := "ces_nase_fsg_dat", lexeme := ces_nase, cell := dat_sg_f, form := "naší",
    analysed := "naš-í", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_ins : Form :=
  { id := "ces_nase_fsg_ins", lexeme := ces_nase, cell := ins_sg_f, form := "naší",
    analysed := "naš-í", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_nom : Form :=
  { id := "ces_zatez_sg_nom", lexeme := ces_zatez, cell := nom_sg, form := "zátěž",
    analysed := "zátěž-ø", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_acc : Form :=
  { id := "ces_zatez_sg_acc", lexeme := ces_zatez, cell := acc_sg, form := "zátěž",
    analysed := "zátěž-ø", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_gen : Form :=
  { id := "ces_zatez_sg_gen", lexeme := ces_zatez, cell := gen_sg, form := "zátěže",
    analysed := "zátěž-e", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_prep : Form :=
  { id := "ces_zatez_sg_prep", lexeme := ces_zatez, cell := prep_sg, form := "zátěži",
    analysed := "zátěž-i", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_dat : Form :=
  { id := "ces_zatez_sg_dat", lexeme := ces_zatez, cell := dat_sg, form := "zátěži",
    analysed := "zátěž-i", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_ins : Form :=
  { id := "ces_zatez_sg_ins", lexeme := ces_zatez, cell := ins_sg, form := "zátěží",
    analysed := "zátěž-í", source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zena_sg_nom : Form :=
  { id := "ces_zena_sg_nom", lexeme := ces_zena, cell := nom_sg, form := "žena",
    analysed := "žen-a", source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_zena_sg_acc : Form :=
  { id := "ces_zena_sg_acc", lexeme := ces_zena, cell := acc_sg, form := "ženu",
    analysed := "žen-u", source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_zena_sg_gen : Form :=
  { id := "ces_zena_sg_gen", lexeme := ces_zena, cell := gen_sg, form := "ženy",
    analysed := "žen-y", source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_zena_sg_prep : Form :=
  { id := "ces_zena_sg_prep", lexeme := ces_zena, cell := prep_sg, form := "ženě",
    analysed := "žen-ě", source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_zena_sg_dat : Form :=
  { id := "ces_zena_sg_dat", lexeme := ces_zena, cell := dat_sg, form := "ženě",
    analysed := "žen-ě", source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_zena_sg_ins : Form :=
  { id := "ces_zena_sg_ins", lexeme := ces_zena, cell := ins_sg, form := "ženou",
    analysed := "žen-ou", source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_kluk_pl_nom : Form :=
  { id := "ces_kluk_pl_nom", lexeme := ces_kluk, cell := nom_pl, form := "kluci",
    analysed := "kluc-i", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_acc : Form :=
  { id := "ces_kluk_pl_acc", lexeme := ces_kluk, cell := acc_pl, form := "kluky",
    analysed := "kluk-y", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_gen : Form :=
  { id := "ces_kluk_pl_gen", lexeme := ces_kluk, cell := gen_pl, form := "kluků",
    analysed := "kluk-ů", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_prep : Form :=
  { id := "ces_kluk_pl_prep", lexeme := ces_kluk, cell := prep_pl, form := "klucích",
    analysed := "kluc-ích", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_dat : Form :=
  { id := "ces_kluk_pl_dat", lexeme := ces_kluk, cell := dat_pl, form := "klukům",
    analysed := "kluk-ům", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_ins : Form :=
  { id := "ces_kluk_pl_ins", lexeme := ces_kluk, cell := ins_pl, form := "kluky",
    analysed := "kluk-y", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_nom : Form :=
  { id := "ces_kluk_pl_colloquial_nom", lexeme := ces_kluk, cell := nom_pl, form := "kluci",
    analysed := "kluc-i", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_acc : Form :=
  { id := "ces_kluk_pl_colloquial_acc", lexeme := ces_kluk, cell := acc_pl, form := "kluky",
    analysed := "kluk-y", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_gen : Form :=
  { id := "ces_kluk_pl_colloquial_gen", lexeme := ces_kluk, cell := gen_pl, form := "kluků",
    analysed := "kluk-ů", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_prep : Form :=
  { id := "ces_kluk_pl_colloquial_prep", lexeme := ces_kluk, cell := prep_pl, form := "klukách",
    analysed := "kluk-ách", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_dat : Form :=
  { id := "ces_kluk_pl_colloquial_dat", lexeme := ces_kluk, cell := dat_pl, form := "klukům",
    analysed := "kluk-ům", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_ins : Form :=
  { id := "ces_kluk_pl_colloquial_ins", lexeme := ces_kluk, cell := ins_pl, form := "klukama",
    analysed := "kluk-ama", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_nom : Form :=
  { id := "ces_muz_pl_colloquial_nom", lexeme := ces_muz, cell := nom_pl, form := "muži",
    analysed := "muž-i", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_acc : Form :=
  { id := "ces_muz_pl_colloquial_acc", lexeme := ces_muz, cell := acc_pl, form := "muže",
    analysed := "muž-e", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_gen : Form :=
  { id := "ces_muz_pl_colloquial_gen", lexeme := ces_muz, cell := gen_pl, form := "mužů",
    analysed := "muž-ů", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_prep : Form :=
  { id := "ces_muz_pl_colloquial_prep", lexeme := ces_muz, cell := prep_pl, form := "mužích",
    analysed := "muž-ích", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_dat : Form :=
  { id := "ces_muz_pl_colloquial_dat", lexeme := ces_muz, cell := dat_pl, form := "mužům",
    analysed := "muž-ům", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_ins : Form :=
  { id := "ces_muz_pl_colloquial_ins", lexeme := ces_muz, cell := ins_pl, form := "mužema",
    analysed := "muž-ema", source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_zena_pl_nom : Form :=
  { id := "ces_zena_pl_nom", lexeme := ces_zena, cell := nom_pl, form := "ženy",
    analysed := "žen-y", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_zena_pl_acc : Form :=
  { id := "ces_zena_pl_acc", lexeme := ces_zena, cell := acc_pl, form := "ženy",
    analysed := "žen-y", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_zena_pl_gen : Form :=
  { id := "ces_zena_pl_gen", lexeme := ces_zena, cell := gen_pl, form := "žen",
    analysed := "žen-ø", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_zena_pl_prep : Form :=
  { id := "ces_zena_pl_prep", lexeme := ces_zena, cell := prep_pl, form := "ženách",
    analysed := "žen-á-ch", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_zena_pl_dat : Form :=
  { id := "ces_zena_pl_dat", lexeme := ces_zena, cell := dat_pl, form := "ženám",
    analysed := "žen-á-m", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_zena_pl_ins : Form :=
  { id := "ces_zena_pl_ins", lexeme := ces_zena, cell := ins_pl, form := "ženami",
    analysed := "žen-a-mi", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_nom : Form :=
  { id := "ces_pisen_pl_nom", lexeme := ces_pisen, cell := nom_pl, form := "písně",
    analysed := "písn-ě", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_acc : Form :=
  { id := "ces_pisen_pl_acc", lexeme := ces_pisen, cell := acc_pl, form := "písně",
    analysed := "písn-ě", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_gen : Form :=
  { id := "ces_pisen_pl_gen", lexeme := ces_pisen, cell := gen_pl, form := "písní",
    analysed := "písn-í", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_prep : Form :=
  { id := "ces_pisen_pl_prep", lexeme := ces_pisen, cell := prep_pl, form := "písních",
    analysed := "písn-í-ch", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_dat : Form :=
  { id := "ces_pisen_pl_dat", lexeme := ces_pisen, cell := dat_pl, form := "písním",
    analysed := "písn-í-m", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_ins : Form :=
  { id := "ces_pisen_pl_ins", lexeme := ces_pisen, cell := ins_pl, form := "písněmi",
    analysed := "písn-ě-mi", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_nom : Form :=
  { id := "ces_dobry_mpl_nom", lexeme := ces_dobry, cell := nom_pl_m, form := "dobré",
    analysed := "dobr-é", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_acc : Form :=
  { id := "ces_dobry_mpl_acc", lexeme := ces_dobry, cell := acc_pl_m, form := "dobré",
    analysed := "dobr-é", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_gen : Form :=
  { id := "ces_dobry_mpl_gen", lexeme := ces_dobry, cell := gen_pl_m, form := "dobrých",
    analysed := "dobr-ý-ch", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_prep : Form :=
  { id := "ces_dobry_mpl_prep", lexeme := ces_dobry, cell := prep_pl_m, form := "dobrých",
    analysed := "dobr-ý-ch", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_dat : Form :=
  { id := "ces_dobry_mpl_dat", lexeme := ces_dobry, cell := dat_pl_m, form := "dobrým",
    analysed := "dobr-ý-m", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_ins : Form :=
  { id := "ces_dobry_mpl_ins", lexeme := ces_dobry, cell := ins_pl_m, form := "dobrými",
    analysed := "dobr-ý-mi", source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_kost_sg_nom : Form :=
  { id := "ces_kost_sg_nom", lexeme := ces_kost, cell := nom_sg, form := "kost",
    analysed := "kost-ø", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_kost_sg_acc : Form :=
  { id := "ces_kost_sg_acc", lexeme := ces_kost, cell := acc_sg, form := "kost",
    analysed := "kost-ø", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_kost_sg_gen : Form :=
  { id := "ces_kost_sg_gen", lexeme := ces_kost, cell := gen_sg, form := "kosti",
    analysed := "kost-i", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_kost_sg_prep : Form :=
  { id := "ces_kost_sg_prep", lexeme := ces_kost, cell := prep_sg, form := "kosti",
    analysed := "kost-i", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_kost_sg_dat : Form :=
  { id := "ces_kost_sg_dat", lexeme := ces_kost, cell := dat_sg, form := "kosti",
    analysed := "kost-i", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_kost_sg_ins : Form :=
  { id := "ces_kost_sg_ins", lexeme := ces_kost, cell := ins_sg, form := "kostí",
    analysed := "kost-í", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_nom : Form :=
  { id := "ces_hrad_sg_nom", lexeme := ces_hrad, cell := nom_sg, form := "hrad",
    analysed := "hrad-ø", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_acc : Form :=
  { id := "ces_hrad_sg_acc", lexeme := ces_hrad, cell := acc_sg, form := "hrad",
    analysed := "hrad-ø", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_gen : Form :=
  { id := "ces_hrad_sg_gen", lexeme := ces_hrad, cell := gen_sg, form := "hradu",
    analysed := "hrad-u", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_prep : Form :=
  { id := "ces_hrad_sg_prep", lexeme := ces_hrad, cell := prep_sg, form := "hradu",
    analysed := "hrad-u", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_dat : Form :=
  { id := "ces_hrad_sg_dat", lexeme := ces_hrad, cell := dat_sg, form := "hradu",
    analysed := "hrad-u", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_ins : Form :=
  { id := "ces_hrad_sg_ins", lexeme := ces_hrad, cell := ins_sg, form := "hradem",
    analysed := "hrad-em", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_nom : Form :=
  { id := "ces_my_nom", lexeme := ces_my, cell := nom_pl, form := "my",
    analysed := "my", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_acc : Form :=
  { id := "ces_my_acc", lexeme := ces_my, cell := acc_pl, form := "nás",
    analysed := "ná-s", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_gen : Form :=
  { id := "ces_my_gen", lexeme := ces_my, cell := gen_pl, form := "nás",
    analysed := "ná-s", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_prep : Form :=
  { id := "ces_my_prep", lexeme := ces_my, cell := prep_pl, form := "nás",
    analysed := "ná-s", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_dat : Form :=
  { id := "ces_my_dat", lexeme := ces_my, cell := dat_pl, form := "nám",
    analysed := "ná-m", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_ins : Form :=
  { id := "ces_my_ins", lexeme := ces_my, cell := ins_pl, form := "námi",
    analysed := "ná-mi", source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_mesto_sg_nom : Form :=
  { id := "ces_mesto_sg_nom", lexeme := ces_mesto, cell := nom_sg, form := "město",
    analysed := "měst-o", source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_mesto_sg_acc : Form :=
  { id := "ces_mesto_sg_acc", lexeme := ces_mesto, cell := acc_sg, form := "město",
    analysed := "měst-o", source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_mesto_sg_gen : Form :=
  { id := "ces_mesto_sg_gen", lexeme := ces_mesto, cell := gen_sg, form := "města",
    analysed := "měst-a", source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_mesto_sg_prep : Form :=
  { id := "ces_mesto_sg_prep", lexeme := ces_mesto, cell := prep_sg, form := "městu",
    analysed := "měst-u", source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_mesto_sg_dat : Form :=
  { id := "ces_mesto_sg_dat", lexeme := ces_mesto, cell := dat_sg, form := "městu",
    analysed := "měst-u", source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_mesto_sg_ins : Form :=
  { id := "ces_mesto_sg_ins", lexeme := ces_mesto, cell := ins_sg, form := "městem",
    analysed := "měst-em", source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_vetsi_nsg_nom : Form :=
  { id := "ces_vetsi_nsg_nom", lexeme := ces_vetsi, cell := nom_sg_n, form := "větší",
    analysed := "větš-í", source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_vetsi_nsg_acc : Form :=
  { id := "ces_vetsi_nsg_acc", lexeme := ces_vetsi, cell := acc_sg_n, form := "větší",
    analysed := "větš-í", source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_vetsi_nsg_gen : Form :=
  { id := "ces_vetsi_nsg_gen", lexeme := ces_vetsi, cell := gen_sg_n, form := "většího",
    analysed := "větš-ího", source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_vetsi_nsg_prep : Form :=
  { id := "ces_vetsi_nsg_prep", lexeme := ces_vetsi, cell := prep_sg_n, form := "větším",
    analysed := "větš-ím", source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_vetsi_nsg_dat : Form :=
  { id := "ces_vetsi_nsg_dat", lexeme := ces_vetsi, cell := dat_sg_n, form := "většímu",
    analysed := "větš-ímu", source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_vetsi_nsg_ins : Form :=
  { id := "ces_vetsi_nsg_ins", lexeme := ces_vetsi, cell := ins_sg_n, form := "větším",
    analysed := "větš-ím", source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_ono_nom : Form :=
  { id := "ces_ono_nom", lexeme := ces_ono, cell := nom_sg, form := "ono",
    analysed := "ono", source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_ono_acc : Form :=
  { id := "ces_ono_acc", lexeme := ces_ono, cell := acc_sg, form := "je",
    analysed := "j-e", source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_ono_gen : Form :=
  { id := "ces_ono_gen", lexeme := ces_ono, cell := gen_sg, form := "jeho",
    analysed := "j-eho", source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_ono_prep : Form :=
  { id := "ces_ono_prep", lexeme := ces_ono, cell := prep_sg, form := "jem",
    analysed := "j-em", source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_ono_dat : Form :=
  { id := "ces_ono_dat", lexeme := ces_ono, cell := dat_sg, form := "jemu",
    analysed := "j-emu", source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_ono_ins : Form :=
  { id := "ces_ono_ins", lexeme := ces_ono, cell := ins_sg, form := "jím",
    analysed := "j-ím", source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_nase_nsg_nom : Form :=
  { id := "ces_nase_nsg_nom", lexeme := ces_nase, cell := nom_sg_n, form := "naše",
    analysed := "naš-e", source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_nase_nsg_acc : Form :=
  { id := "ces_nase_nsg_acc", lexeme := ces_nase, cell := acc_sg_n, form := "naše",
    analysed := "naš-e", source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_nase_nsg_gen : Form :=
  { id := "ces_nase_nsg_gen", lexeme := ces_nase, cell := gen_sg_n, form := "našeho",
    analysed := "naš-eho", source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_nase_nsg_prep : Form :=
  { id := "ces_nase_nsg_prep", lexeme := ces_nase, cell := prep_sg_n, form := "našem",
    analysed := "naš-em", source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_nase_nsg_dat : Form :=
  { id := "ces_nase_nsg_dat", lexeme := ces_nase, cell := dat_sg_n, form := "našemu",
    analysed := "naš-emu", source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_nase_nsg_ins : Form :=
  { id := "ces_nase_nsg_ins", lexeme := ces_nase, cell := ins_sg_n, form := "naším",
    analysed := "naš-ím", source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_vetsi_fsg_nom : Form :=
  { id := "ces_vetsi_fsg_nom", lexeme := ces_vetsi, cell := nom_sg_f, form := "větší",
    analysed := "větš-í", source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_fsg_acc : Form :=
  { id := "ces_vetsi_fsg_acc", lexeme := ces_vetsi, cell := acc_sg_f, form := "větší",
    analysed := "větš-í", source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_fsg_gen : Form :=
  { id := "ces_vetsi_fsg_gen", lexeme := ces_vetsi, cell := gen_sg_f, form := "větší",
    analysed := "větš-í", source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_fsg_prep : Form :=
  { id := "ces_vetsi_fsg_prep", lexeme := ces_vetsi, cell := prep_sg_f, form := "větší",
    analysed := "větš-í", source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_fsg_dat : Form :=
  { id := "ces_vetsi_fsg_dat", lexeme := ces_vetsi, cell := dat_sg_f, form := "větší",
    analysed := "větš-í", source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_fsg_ins : Form :=
  { id := "ces_vetsi_fsg_ins", lexeme := ces_vetsi, cell := ins_sg_f, form := "větší",
    analysed := "větš-í", source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_npl_nom : Form :=
  { id := "ces_vetsi_npl_nom", lexeme := ces_vetsi, cell := nom_pl_n, form := "větší",
    analysed := "větš-í", source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_vetsi_npl_acc : Form :=
  { id := "ces_vetsi_npl_acc", lexeme := ces_vetsi, cell := acc_pl_n, form := "větší",
    analysed := "větš-í", source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_vetsi_npl_gen : Form :=
  { id := "ces_vetsi_npl_gen", lexeme := ces_vetsi, cell := gen_pl_n, form := "větších",
    analysed := "větš-ích", source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_vetsi_npl_prep : Form :=
  { id := "ces_vetsi_npl_prep", lexeme := ces_vetsi, cell := prep_pl_n, form := "větších",
    analysed := "větš-ích", source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_vetsi_npl_dat : Form :=
  { id := "ces_vetsi_npl_dat", lexeme := ces_vetsi, cell := dat_pl_n, form := "větším",
    analysed := "větš-ím", source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_vetsi_npl_ins : Form :=
  { id := "ces_vetsi_npl_ins", lexeme := ces_vetsi, cell := ins_pl_n, form := "většími",
    analysed := "větš-ími", source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_ona_npl_nom : Form :=
  { id := "ces_ona_npl_nom", lexeme := ces_oni, cell := nom_pl, form := "ona",
    analysed := "on-a", source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ona_npl_acc : Form :=
  { id := "ces_ona_npl_acc", lexeme := ces_oni, cell := acc_pl, form := "je",
    analysed := "j-e", source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ona_npl_gen : Form :=
  { id := "ces_ona_npl_gen", lexeme := ces_oni, cell := gen_pl, form := "jich",
    analysed := "j-ich", source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ona_npl_prep : Form :=
  { id := "ces_ona_npl_prep", lexeme := ces_oni, cell := prep_pl, form := "jich",
    analysed := "j-ich", source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ona_npl_dat : Form :=
  { id := "ces_ona_npl_dat", lexeme := ces_oni, cell := dat_pl, form := "jim",
    analysed := "j-im", source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ona_npl_ins : Form :=
  { id := "ces_ona_npl_ins", lexeme := ces_oni, cell := ins_pl, form := "jimi",
    analysed := "j-imi", source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ta_nom : Form :=
  { id := "ces_ta_nom", lexeme := ces_ten, cell := nom_sg_f, form := "ta",
    analysed := "t-a", source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_ta_acc : Form :=
  { id := "ces_ta_acc", lexeme := ces_ten, cell := acc_sg_f, form := "tu",
    analysed := "t-u", source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_ta_gen : Form :=
  { id := "ces_ta_gen", lexeme := ces_ten, cell := gen_sg_f, form := "té",
    analysed := "t-é", source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_ta_prep : Form :=
  { id := "ces_ta_prep", lexeme := ces_ten, cell := prep_sg_f, form := "té",
    analysed := "t-é", source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_ta_dat : Form :=
  { id := "ces_ta_dat", lexeme := ces_ten, cell := dat_sg_f, form := "té",
    analysed := "t-é", source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_ta_ins : Form :=
  { id := "ces_ta_ins", lexeme := ces_ten, cell := ins_sg_f, form := "tou",
    analysed := "t-ou", source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_dva_nom : Form :=
  { id := "ces_dva_nom", lexeme := ces_dva, cell := nom_du_m, form := "dva",
    analysed := "dv-a", source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_dva_acc : Form :=
  { id := "ces_dva_acc", lexeme := ces_dva, cell := acc_du_m, form := "dva",
    analysed := "dv-a", source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_dva_gen : Form :=
  { id := "ces_dva_gen", lexeme := ces_dva, cell := gen_du_m, form := "dvou",
    analysed := "dv-ou", source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_dva_prep : Form :=
  { id := "ces_dva_prep", lexeme := ces_dva, cell := prep_du_m, form := "dvou",
    analysed := "dv-ou", source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_dva_dat : Form :=
  { id := "ces_dva_dat", lexeme := ces_dva, cell := dat_du_m, form := "dvěma",
    analysed := "dv-ěma", source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_dva_ins : Form :=
  { id := "ces_dva_ins", lexeme := ces_dva, cell := ins_du_m, form := "dvěma",
    analysed := "dv-ěma", source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_pet_nom : Form :=
  { id := "ces_pet_nom", lexeme := ces_pet, cell := nom_pl, form := "pět",
    analysed := "pět", source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def ces_pet_acc : Form :=
  { id := "ces_pet_acc", lexeme := ces_pet, cell := acc_pl, form := "pět",
    analysed := "pět", source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def ces_pet_gen : Form :=
  { id := "ces_pet_gen", lexeme := ces_pet, cell := gen_pl, form := "pěti",
    analysed := "pět-i", source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def ces_pet_prep : Form :=
  { id := "ces_pet_prep", lexeme := ces_pet, cell := prep_pl, form := "pěti",
    analysed := "pět-i", source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def ces_pet_dat : Form :=
  { id := "ces_pet_dat", lexeme := ces_pet, cell := dat_pl, form := "pěti",
    analysed := "pět-i", source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def ces_pet_ins : Form :=
  { id := "ces_pet_ins", lexeme := ces_pet, cell := ins_pl, form := "pěti",
    analysed := "pět-i", source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def slk_ona_nom : Form :=
  { id := "slk_ona_nom", lexeme := slk_ona, cell := nom_sg, form := "ona",
    analysed := "ona", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ona_acc : Form :=
  { id := "slk_ona_acc", lexeme := slk_ona, cell := acc_sg, form := "ju",
    analysed := "j-u", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ona_gen : Form :=
  { id := "slk_ona_gen", lexeme := slk_ona, cell := gen_sg, form := "jej",
    analysed := "j-ej", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ona_prep : Form :=
  { id := "slk_ona_prep", lexeme := slk_ona, cell := prep_sg, form := "jej",
    analysed := "j-ej", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ona_dat : Form :=
  { id := "slk_ona_dat", lexeme := slk_ona, cell := dat_sg, form := "njej",
    analysed := "nj-ej", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ona_ins : Form :=
  { id := "slk_ona_ins", lexeme := slk_ona, cell := ins_sg, form := "njou",
    analysed := "nj-ou", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_nom : Form :=
  { id := "slk_nase_fsg_nom", lexeme := slk_nase, cell := nom_sg_f, form := "naša",
    analysed := "naš-a", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_acc : Form :=
  { id := "slk_nase_fsg_acc", lexeme := slk_nase, cell := acc_sg_f, form := "našu",
    analysed := "naš-u", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_gen : Form :=
  { id := "slk_nase_fsg_gen", lexeme := slk_nase, cell := gen_sg_f, form := "našej",
    analysed := "naš-ej", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_prep : Form :=
  { id := "slk_nase_fsg_prep", lexeme := slk_nase, cell := prep_sg_f, form := "našej",
    analysed := "naš-ej", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_dat : Form :=
  { id := "slk_nase_fsg_dat", lexeme := slk_nase, cell := dat_sg_f, form := "našej",
    analysed := "naš-ej", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_ins : Form :=
  { id := "slk_nase_fsg_ins", lexeme := slk_nase, cell := ins_sg_f, form := "našou",
    analysed := "naš-ou", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_nom : Form :=
  { id := "slk_ulica_sg_nom", lexeme := slk_ulica, cell := nom_sg, form := "ulica",
    analysed := "ulic-a", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_acc : Form :=
  { id := "slk_ulica_sg_acc", lexeme := slk_ulica, cell := acc_sg, form := "ulicu",
    analysed := "ulic-u", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_gen : Form :=
  { id := "slk_ulica_sg_gen", lexeme := slk_ulica, cell := gen_sg, form := "ulice",
    analysed := "ulic-e", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_prep : Form :=
  { id := "slk_ulica_sg_prep", lexeme := slk_ulica, cell := prep_sg, form := "ulici",
    analysed := "ulic-i", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_dat : Form :=
  { id := "slk_ulica_sg_dat", lexeme := slk_ulica, cell := dat_sg, form := "ulici",
    analysed := "ulic-i", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_ins : Form :=
  { id := "slk_ulica_sg_ins", lexeme := slk_ulica, cell := ins_sg, form := "ulicou",
    analysed := "ulic-ou", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_nom : Form :=
  { id := "slk_tlac_sg_nom", lexeme := slk_tlac, cell := nom_sg, form := "tlač",
    analysed := "tlač-ø", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_acc : Form :=
  { id := "slk_tlac_sg_acc", lexeme := slk_tlac, cell := acc_sg, form := "tlač",
    analysed := "tlač-ø", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_gen : Form :=
  { id := "slk_tlac_sg_gen", lexeme := slk_tlac, cell := gen_sg, form := "tlače",
    analysed := "tlač-e", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_prep : Form :=
  { id := "slk_tlac_sg_prep", lexeme := slk_tlac, cell := prep_sg, form := "tlači",
    analysed := "tlač-i", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_dat : Form :=
  { id := "slk_tlac_sg_dat", lexeme := slk_tlac, cell := dat_sg, form := "tlači",
    analysed := "tlač-i", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_ins : Form :=
  { id := "slk_tlac_sg_ins", lexeme := slk_tlac, cell := ins_sg, form := "tlačou",
    analysed := "tlač-ou", source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def ukr_kraj_sg_nom : Form :=
  { id := "ukr_kraj_sg_nom", lexeme := ukr_kraj, cell := nom_sg, form := "kraj",
    analysed := "kraj-ø", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kraj_sg_acc : Form :=
  { id := "ukr_kraj_sg_acc", lexeme := ukr_kraj, cell := acc_sg, form := "kraj",
    analysed := "kraj-ø", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kraj_sg_gen : Form :=
  { id := "ukr_kraj_sg_gen", lexeme := ukr_kraj, cell := gen_sg, form := "kráju",
    analysed := "kráj-u", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kraj_sg_prep : Form :=
  { id := "ukr_kraj_sg_prep", lexeme := ukr_kraj, cell := prep_sg, form := "krajú",
    analysed := "kraj-ú", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kraj_sg_dat : Form :=
  { id := "ukr_kraj_sg_dat", lexeme := ukr_kraj, cell := dat_sg, form := "krájevi",
    analysed := "kráj-evi", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kraj_sg_ins : Form :=
  { id := "ukr_kraj_sg_ins", lexeme := ukr_kraj, cell := ins_sg, form := "krájem",
    analysed := "kráj-em", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_nom : Form :=
  { id := "ukr_velykyj_pl_nom", lexeme := ukr_velykyj, cell := nom_pl, form := "velíki",
    analysed := "velík-i", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_acc : Form :=
  { id := "ukr_velykyj_pl_acc", lexeme := ukr_velykyj, cell := acc_pl, form := "velíki",
    analysed := "velík-i", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_gen : Form :=
  { id := "ukr_velykyj_pl_gen", lexeme := ukr_velykyj, cell := gen_pl, form := "velíkıch",
    analysed := "velík-ıch", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_prep : Form :=
  { id := "ukr_velykyj_pl_prep", lexeme := ukr_velykyj, cell := prep_pl, form := "velíkıch",
    analysed := "velík-ıch", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_dat : Form :=
  { id := "ukr_velykyj_pl_dat", lexeme := ukr_velykyj, cell := dat_pl, form := "velíkım",
    analysed := "velík-ım", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_ins : Form :=
  { id := "ukr_velykyj_pl_ins", lexeme := ukr_velykyj, cell := ins_pl, form := "velíkımı",
    analysed := "velík-ımı", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_nom : Form :=
  { id := "ukr_znannja_sg_nom", lexeme := ukr_znannja, cell := nom_sg, form := "znannjá",
    analysed := "znann-já", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_acc : Form :=
  { id := "ukr_znannja_sg_acc", lexeme := ukr_znannja, cell := acc_sg, form := "znannjá",
    analysed := "znann-já", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_gen : Form :=
  { id := "ukr_znannja_sg_gen", lexeme := ukr_znannja, cell := gen_sg, form := "znannjá",
    analysed := "znann-já", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_prep : Form :=
  { id := "ukr_znannja_sg_prep", lexeme := ukr_znannja, cell := prep_sg, form := "znanni̇́",
    analysed := "znann-i̇́", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_dat : Form :=
  { id := "ukr_znannja_sg_dat", lexeme := ukr_znannja, cell := dat_sg, form := "znannjú",
    analysed := "znann-jú", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_ins : Form :=
  { id := "ukr_znannja_sg_ins", lexeme := ukr_znannja, cell := ins_sg, form := "znannjám",
    analysed := "znann-jám", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_nom : Form :=
  { id := "ukr_my_nom", lexeme := ukr_my, cell := nom_pl, form := "mı",
    analysed := "mı", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_acc : Form :=
  { id := "ukr_my_acc", lexeme := ukr_my, cell := acc_pl, form := "nas",
    analysed := "nas", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_gen : Form :=
  { id := "ukr_my_gen", lexeme := ukr_my, cell := gen_pl, form := "nas",
    analysed := "nas", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_prep : Form :=
  { id := "ukr_my_prep", lexeme := ukr_my, cell := prep_pl, form := "nas",
    analysed := "nas", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_dat : Form :=
  { id := "ukr_my_dat", lexeme := ukr_my, cell := dat_pl, form := "nam",
    analysed := "nam", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_ins : Form :=
  { id := "ukr_my_ins", lexeme := ukr_my, cell := ins_pl, form := "námı",
    analysed := "námı", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_nom : Form :=
  { id := "ukr_kasyr_sg_nom", lexeme := ukr_kasyr, cell := nom_sg, form := "kasír",
    analysed := "kasír-ø", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_acc : Form :=
  { id := "ukr_kasyr_sg_acc", lexeme := ukr_kasyr, cell := acc_sg, form := "kasíra",
    analysed := "kasír-a", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_gen : Form :=
  { id := "ukr_kasyr_sg_gen", lexeme := ukr_kasyr, cell := gen_sg, form := "kasíra",
    analysed := "kasír-a", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_prep : Form :=
  { id := "ukr_kasyr_sg_prep", lexeme := ukr_kasyr, cell := prep_sg, form := "kasírovi",
    analysed := "kasír-ovi", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_dat : Form :=
  { id := "ukr_kasyr_sg_dat", lexeme := ukr_kasyr, cell := dat_sg, form := "kasírovi",
    analysed := "kasír-ovi", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_ins : Form :=
  { id := "ukr_kasyr_sg_ins", lexeme := ukr_kasyr, cell := ins_sg, form := "kasírom",
    analysed := "kasír-om", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_nom : Form :=
  { id := "ukr_kasyr_pl_nom", lexeme := ukr_kasyr, cell := nom_pl, form := "kasírı",
    analysed := "kasír-ı", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_acc : Form :=
  { id := "ukr_kasyr_pl_acc", lexeme := ukr_kasyr, cell := acc_pl, form := "kasíriv",
    analysed := "kasír-iv", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_gen : Form :=
  { id := "ukr_kasyr_pl_gen", lexeme := ukr_kasyr, cell := gen_pl, form := "kasíriv",
    analysed := "kasír-iv", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_prep : Form :=
  { id := "ukr_kasyr_pl_prep", lexeme := ukr_kasyr, cell := prep_pl, form := "kasírach",
    analysed := "kasír-ach", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_dat : Form :=
  { id := "ukr_kasyr_pl_dat", lexeme := ukr_kasyr, cell := dat_pl, form := "kasíram",
    analysed := "kasír-am", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_ins : Form :=
  { id := "ukr_kasyr_pl_ins", lexeme := ukr_kasyr, cell := ins_pl, form := "kasíramı",
    analysed := "kasír-amı", source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_maty_sg_nom : Form :=
  { id := "ukr_maty_sg_nom", lexeme := ukr_maty, cell := nom_sg, form := "mátı",
    analysed := "mát-ı", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_maty_sg_acc : Form :=
  { id := "ukr_maty_sg_acc", lexeme := ukr_maty, cell := acc_sg, form := "mátir",
    analysed := "mát-ir", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_maty_sg_gen : Form :=
  { id := "ukr_maty_sg_gen", lexeme := ukr_maty, cell := gen_sg, form := "máteri",
    analysed := "mát-er-i", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_maty_sg_prep : Form :=
  { id := "ukr_maty_sg_prep", lexeme := ukr_maty, cell := prep_sg, form := "máteri",
    analysed := "mát-er-i", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_maty_sg_dat : Form :=
  { id := "ukr_maty_sg_dat", lexeme := ukr_maty, cell := dat_sg, form := "máteri",
    analysed := "mát-er-i", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_maty_sg_ins : Form :=
  { id := "ukr_maty_sg_ins", lexeme := ukr_maty, cell := ins_sg, form := "mátirju",
    analysed := "mát-ir-ju", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_nom : Form :=
  { id := "ukr_ruka_sg_nom", lexeme := ukr_ruka, cell := nom_sg, form := "ruká",
    analysed := "ruk-á", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_acc : Form :=
  { id := "ukr_ruka_sg_acc", lexeme := ukr_ruka, cell := acc_sg, form := "rúku",
    analysed := "rúk-u", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_gen : Form :=
  { id := "ukr_ruka_sg_gen", lexeme := ukr_ruka, cell := gen_sg, form := "rukí",
    analysed := "ruk-í", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_prep : Form :=
  { id := "ukr_ruka_sg_prep", lexeme := ukr_ruka, cell := prep_sg, form := "ruci̇́",
    analysed := "ruc-i̇́", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_dat : Form :=
  { id := "ukr_ruka_sg_dat", lexeme := ukr_ruka, cell := dat_sg, form := "ruci̇́",
    analysed := "ruc-i̇́", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_ins : Form :=
  { id := "ukr_ruka_sg_ins", lexeme := ukr_ruka, cell := ins_sg, form := "rukóju",
    analysed := "ruk-óju", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_nom : Form :=
  { id := "ukr_ja_nom", lexeme := ukr_ja, cell := nom_sg, form := "ja",
    analysed := "ja", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_acc : Form :=
  { id := "ukr_ja_acc", lexeme := ukr_ja, cell := acc_sg, form := "mené",
    analysed := "mené", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_gen : Form :=
  { id := "ukr_ja_gen", lexeme := ukr_ja, cell := gen_sg, form := "mené",
    analysed := "mené", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_prep : Form :=
  { id := "ukr_ja_prep", lexeme := ukr_ja, cell := prep_sg, form := "meni̇́",
    analysed := "meni̇́", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_dat : Form :=
  { id := "ukr_ja_dat", lexeme := ukr_ja, cell := dat_sg, form := "meni̇́",
    analysed := "meni̇́", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_ins : Form :=
  { id := "ukr_ja_ins", lexeme := ukr_ja, cell := ins_sg, form := "mnóju",
    analysed := "mnóju", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_nom : Form :=
  { id := "ukr_velykyj_msg_nom", lexeme := ukr_velykyj, cell := nom_sg_m, form := "velíkıj",
    analysed := "velík-ıj", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_acc : Form :=
  { id := "ukr_velykyj_msg_acc", lexeme := ukr_velykyj, cell := acc_sg_m, form := "velíkıj",
    analysed := "velík-ıj", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_gen : Form :=
  { id := "ukr_velykyj_msg_gen", lexeme := ukr_velykyj, cell := gen_sg_m, form := "velíkogo",
    analysed := "velík-ogo", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_prep : Form :=
  { id := "ukr_velykyj_msg_prep", lexeme := ukr_velykyj, cell := prep_sg_m, form := "velíkomu",
    analysed := "velík-omu", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_dat : Form :=
  { id := "ukr_velykyj_msg_dat", lexeme := ukr_velykyj, cell := dat_sg_m, form := "velíkomu",
    analysed := "velík-omu", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_ins : Form :=
  { id := "ukr_velykyj_msg_ins", lexeme := ukr_velykyj, cell := ins_sg_m, form := "velíkım",
    analysed := "velík-ım", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_nom : Form :=
  { id := "ukr_sto_nom", lexeme := ukr_sto, cell := nom_sg, form := "sto",
    analysed := "st-o", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_acc : Form :=
  { id := "ukr_sto_acc", lexeme := ukr_sto, cell := acc_sg, form := "sto",
    analysed := "st-o", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_gen : Form :=
  { id := "ukr_sto_gen", lexeme := ukr_sto, cell := gen_sg, form := "sta",
    analysed := "st-a", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_prep : Form :=
  { id := "ukr_sto_prep", lexeme := ukr_sto, cell := prep_sg, form := "sta",
    analysed := "st-a", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_dat : Form :=
  { id := "ukr_sto_dat", lexeme := ukr_sto, cell := dat_sg, form := "sta",
    analysed := "st-a", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_ins : Form :=
  { id := "ukr_sto_ins", lexeme := ukr_sto, cell := ins_sg, form := "sta",
    analysed := "st-a", source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_kraj_sg_2_nom : Form :=
  { id := "ukr_kraj_sg_2_nom", lexeme := ukr_kraj, cell := nom_sg, form := "kraj",
    analysed := "kraj-ø", source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_kraj_sg_2_acc : Form :=
  { id := "ukr_kraj_sg_2_acc", lexeme := ukr_kraj, cell := acc_sg, form := "kraj",
    analysed := "kraj-ø", source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_kraj_sg_2_gen : Form :=
  { id := "ukr_kraj_sg_2_gen", lexeme := ukr_kraj, cell := gen_sg, form := "kráju",
    analysed := "kráj-u", source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_kraj_sg_2_prep : Form :=
  { id := "ukr_kraj_sg_2_prep", lexeme := ukr_kraj, cell := prep_sg, form := "kráji",
    analysed := "kráj-i", source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_kraj_sg_2_dat : Form :=
  { id := "ukr_kraj_sg_2_dat", lexeme := ukr_kraj, cell := dat_sg, form := "kráju",
    analysed := "kráj-u", source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_kraj_sg_2_ins : Form :=
  { id := "ukr_kraj_sg_2_ins", lexeme := ukr_kraj, cell := ins_sg, form := "krájem",
    analysed := "kráj-em", source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_bezkrajij_msg_nom : Form :=
  { id := "ukr_bezkrajij_msg_nom", lexeme := ukr_bezkrajij, cell := nom_sg_m, form := "bezkrajij",
    analysed := "bezkraj-ij", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_acc : Form :=
  { id := "ukr_bezkrajij_msg_acc", lexeme := ukr_bezkrajij, cell := acc_sg_m, form := "bezkrajij",
    analysed := "bezkraj-ij", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_gen : Form :=
  { id := "ukr_bezkrajij_msg_gen", lexeme := ukr_bezkrajij, cell := gen_sg_m, form := "bezkrajogo",
    analysed := "bezkraj-ogo", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_prep : Form :=
  { id := "ukr_bezkrajij_msg_prep", lexeme := ukr_bezkrajij, cell := prep_sg_m, form := "bezkrajomu",
    analysed := "bezkraj-omu", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_dat : Form :=
  { id := "ukr_bezkrajij_msg_dat", lexeme := ukr_bezkrajij, cell := dat_sg_m, form := "bezkrajomu",
    analysed := "bezkraj-omu", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_ins : Form :=
  { id := "ukr_bezkrajij_msg_ins", lexeme := ukr_bezkrajij, cell := ins_sg_m, form := "bezkrajim",
    analysed := "bezkraj-im", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_nom : Form :=
  { id := "ukr_bezkrajij_msg_2_nom", lexeme := ukr_bezkrajij, cell := nom_sg_m, form := "bezkrajij",
    analysed := "bezkraj-ij", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_acc : Form :=
  { id := "ukr_bezkrajij_msg_2_acc", lexeme := ukr_bezkrajij, cell := acc_sg_m, form := "bezkrajij",
    analysed := "bezkraj-ij", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_gen : Form :=
  { id := "ukr_bezkrajij_msg_2_gen", lexeme := ukr_bezkrajij, cell := gen_sg_m, form := "bezkrajogo",
    analysed := "bezkraj-ogo", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_prep : Form :=
  { id := "ukr_bezkrajij_msg_2_prep", lexeme := ukr_bezkrajij, cell := prep_sg_m, form := "bezkrajim",
    analysed := "bezkraj-im", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_dat : Form :=
  { id := "ukr_bezkrajij_msg_2_dat", lexeme := ukr_bezkrajij, cell := dat_sg_m, form := "bezkrajomu",
    analysed := "bezkraj-omu", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_ins : Form :=
  { id := "ukr_bezkrajij_msg_2_ins", lexeme := ukr_bezkrajij, cell := ins_sg_m, form := "bezkrajim",
    analysed := "bezkraj-im", source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_velykyj_msg_2_nom : Form :=
  { id := "ukr_velykyj_msg_2_nom", lexeme := ukr_velykyj, cell := nom_sg_m, form := "velíkıj",
    analysed := "velík-ıj", source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def ukr_velykyj_msg_2_acc : Form :=
  { id := "ukr_velykyj_msg_2_acc", lexeme := ukr_velykyj, cell := acc_sg_m, form := "velíkıj",
    analysed := "velík-ıj", source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def ukr_velykyj_msg_2_gen : Form :=
  { id := "ukr_velykyj_msg_2_gen", lexeme := ukr_velykyj, cell := gen_sg_m, form := "velíkogo",
    analysed := "velík-ogo", source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def ukr_velykyj_msg_2_prep : Form :=
  { id := "ukr_velykyj_msg_2_prep", lexeme := ukr_velykyj, cell := prep_sg_m, form := "velíkim",
    analysed := "velík-im", source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def ukr_velykyj_msg_2_dat : Form :=
  { id := "ukr_velykyj_msg_2_dat", lexeme := ukr_velykyj, cell := dat_sg_m, form := "velíkomu",
    analysed := "velík-omu", source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def ukr_velykyj_msg_2_ins : Form :=
  { id := "ukr_velykyj_msg_2_ins", lexeme := ukr_velykyj, cell := ins_sg_m, form := "velíkım",
    analysed := "velík-ım", source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def srp_sin_sg.paradigm : Paradigm :=
  { id := "srp_sin_sg", lexeme := srp_sin, forms := [srp_sin_sg_nom, srp_sin_sg_acc, srp_sin_sg_gen, srp_sin_sg_prep, srp_sin_sg_dat, srp_sin_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg.paradigm : Paradigm :=
  { id := "srp_grad_sg", lexeme := srp_grad, forms := [srp_grad_sg_nom, srp_grad_sg_acc, srp_grad_sg_gen, srp_grad_sg_prep, srp_grad_sg_dat, srp_grad_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg.paradigm : Paradigm :=
  { id := "srp_muz_sg", lexeme := srp_muz, forms := [srp_muz_sg_nom, srp_muz_sg_acc, srp_muz_sg_gen, srp_muz_sg_prep, srp_muz_sg_dat, srp_muz_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg.paradigm : Paradigm :=
  { id := "srp_selo_sg", lexeme := srp_selo, forms := [srp_selo_sg_nom, srp_selo_sg_acc, srp_selo_sg_gen, srp_selo_sg_prep, srp_selo_sg_dat, srp_selo_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg.paradigm : Paradigm :=
  { id := "srp_srce_sg", lexeme := srp_srce, forms := [srp_srce_sg_nom, srp_srce_sg_acc, srp_srce_sg_gen, srp_srce_sg_prep, srp_srce_sg_dat, srp_srce_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg.paradigm : Paradigm :=
  { id := "srp_ovca_sg", lexeme := srp_ovca, forms := [srp_ovca_sg_nom, srp_ovca_sg_acc, srp_ovca_sg_gen, srp_ovca_sg_prep, srp_ovca_sg_dat, srp_ovca_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg.paradigm : Paradigm :=
  { id := "srp_smrt_sg", lexeme := srp_smrt, forms := [srp_smrt_sg_nom, srp_smrt_sg_acc, srp_smrt_sg_gen, srp_smrt_sg_prep, srp_smrt_sg_dat, srp_smrt_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_pl.paradigm : Paradigm :=
  { id := "srp_sin_pl", lexeme := srp_sin, forms := [srp_sin_pl_nom, srp_sin_pl_acc, srp_sin_pl_gen, srp_sin_pl_prep, srp_sin_pl_dat, srp_sin_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl.paradigm : Paradigm :=
  { id := "srp_grad_pl", lexeme := srp_grad, forms := [srp_grad_pl_nom, srp_grad_pl_acc, srp_grad_pl_gen, srp_grad_pl_prep, srp_grad_pl_dat, srp_grad_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl.paradigm : Paradigm :=
  { id := "srp_muz_pl", lexeme := srp_muz, forms := [srp_muz_pl_nom, srp_muz_pl_acc, srp_muz_pl_gen, srp_muz_pl_prep, srp_muz_pl_dat, srp_muz_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl.paradigm : Paradigm :=
  { id := "srp_selo_pl", lexeme := srp_selo, forms := [srp_selo_pl_nom, srp_selo_pl_acc, srp_selo_pl_gen, srp_selo_pl_prep, srp_selo_pl_dat, srp_selo_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl.paradigm : Paradigm :=
  { id := "srp_srce_pl", lexeme := srp_srce, forms := [srp_srce_pl_nom, srp_srce_pl_acc, srp_srce_pl_gen, srp_srce_pl_prep, srp_srce_pl_dat, srp_srce_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl.paradigm : Paradigm :=
  { id := "srp_ovca_pl", lexeme := srp_ovca, forms := [srp_ovca_pl_nom, srp_ovca_pl_acc, srp_ovca_pl_gen, srp_ovca_pl_prep, srp_ovca_pl_dat, srp_ovca_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl.paradigm : Paradigm :=
  { id := "srp_smrt_pl", lexeme := srp_smrt, forms := [srp_smrt_pl_nom, srp_smrt_pl_acc, srp_smrt_pl_gen, srp_smrt_pl_prep, srp_smrt_pl_dat, srp_smrt_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ja.paradigm : Paradigm :=
  { id := "srp_ja", lexeme := srp_ja, forms := [srp_ja_nom, srp_ja_acc, srp_ja_gen, srp_ja_prep, srp_ja_dat, srp_ja_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti.paradigm : Paradigm :=
  { id := "srp_ti", lexeme := srp_ti, forms := [srp_ti_nom, srp_ti_acc, srp_ti_gen, srp_ti_prep, srp_ti_dat, srp_ti_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on.paradigm : Paradigm :=
  { id := "srp_on", lexeme := srp_on, forms := [srp_on_nom, srp_on_acc, srp_on_gen, srp_on_prep, srp_on_dat, srp_on_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona.paradigm : Paradigm :=
  { id := "srp_ona", lexeme := srp_ona, forms := [srp_ona_nom, srp_ona_acc, srp_ona_gen, srp_ona_prep, srp_ona_dat, srp_ona_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi.paradigm : Paradigm :=
  { id := "srp_mi", lexeme := srp_mi, forms := [srp_mi_nom, srp_mi_acc, srp_mi_gen, srp_mi_prep, srp_mi_dat, srp_mi_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi.paradigm : Paradigm :=
  { id := "srp_vi", lexeme := srp_vi, forms := [srp_vi_nom, srp_vi_acc, srp_vi_gen, srp_vi_prep, srp_vi_dat, srp_vi_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni.paradigm : Paradigm :=
  { id := "srp_oni", lexeme := srp_oni, forms := [srp_oni_nom, srp_oni_acc, srp_oni_gen, srp_oni_prep, srp_oni_dat, srp_oni_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def slv_miza_du.paradigm : Paradigm :=
  { id := "slv_miza_du", lexeme := slv_miza, forms := [slv_miza_du_nom, slv_miza_du_acc, slv_miza_du_gen, slv_miza_du_prep, slv_miza_du_dat, slv_miza_du_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg.paradigm : Paradigm :=
  { id := "slv_breskev_sg", lexeme := slv_breskev, forms := [slv_breskev_sg_nom, slv_breskev_sg_acc, slv_breskev_sg_gen, slv_breskev_sg_prep, slv_breskev_sg_dat, slv_breskev_sg_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl.paradigm : Paradigm :=
  { id := "slv_breskev_pl", lexeme := slv_breskev, forms := [slv_breskev_pl_nom, slv_breskev_pl_acc, slv_breskev_pl_gen, slv_breskev_pl_prep, slv_breskev_pl_dat, slv_breskev_pl_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg.paradigm : Paradigm :=
  { id := "slv_jabolko_sg", lexeme := slv_jabolko, forms := [slv_jabolko_sg_nom, slv_jabolko_sg_acc, slv_jabolko_sg_gen, slv_jabolko_sg_prep, slv_jabolko_sg_dat, slv_jabolko_sg_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du.paradigm : Paradigm :=
  { id := "slv_kmet_du", lexeme := slv_kmet, forms := [slv_kmet_du_nom, slv_kmet_du_acc, slv_kmet_du_gen, slv_kmet_du_prep, slv_kmet_du_dat, slv_kmet_du_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg.paradigm : Paradigm :=
  { id := "slv_kmet_sg", lexeme := slv_kmet, forms := [slv_kmet_sg_nom, slv_kmet_sg_acc, slv_kmet_sg_gen, slv_kmet_sg_prep, slv_kmet_sg_dat, slv_kmet_sg_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz.paradigm : Paradigm :=
  { id := "slv_jaz", lexeme := slv_jaz, forms := [slv_jaz_nom, slv_jaz_acc, slv_jaz_gen, slv_jaz_prep, slv_jaz_dat, slv_jaz_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_moj_mpl.paradigm : Paradigm :=
  { id := "slv_moj_mpl", lexeme := slv_moj, forms := [slv_moj_mpl_nom, slv_moj_mpl_acc, slv_moj_mpl_gen, slv_moj_mpl_prep, slv_moj_mpl_dat, slv_moj_mpl_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva.paradigm : Paradigm :=
  { id := "slv_dva", lexeme := slv_dva, forms := [slv_dva_nom, slv_dva_acc, slv_dva_gen, slv_dva_prep, slv_dva_dat, slv_dva_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi.paradigm : Paradigm :=
  { id := "slv_mi", lexeme := slv_mi, forms := [slv_mi_nom, slv_mi_acc, slv_mi_gen, slv_mi_prep, slv_mi_dat, slv_mi_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva.paradigm : Paradigm :=
  { id := "slv_midva", lexeme := slv_midva, forms := [slv_midva_nom, slv_midva_acc, slv_midva_gen, slv_midva_prep, slv_midva_dat, slv_midva_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg.paradigm : Paradigm :=
  { id := "slv_nit_sg", lexeme := slv_nit, forms := [slv_nit_sg_nom, slv_nit_sg_acc, slv_nit_sg_gen, slv_nit_sg_prep, slv_nit_sg_dat, slv_nit_sg_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg.paradigm : Paradigm :=
  { id := "slv_gospa_sg", lexeme := slv_gospa, forms := [slv_gospa_sg_nom, slv_gospa_sg_acc, slv_gospa_sg_gen, slv_gospa_sg_prep, slv_gospa_sg_dat, slv_gospa_sg_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dan_du.paradigm : Paradigm :=
  { id := "slv_dan_du", lexeme := slv_dan, forms := [slv_dan_du_nom, slv_dan_du_acc, slv_dan_du_gen, slv_dan_du_prep, slv_dan_du_dat, slv_dan_du_ins],
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg.paradigm : Paradigm :=
  { id := "slv_racunovodja_sg", lexeme := slv_racunovodja, forms := [slv_racunovodja_sg_nom, slv_racunovodja_sg_acc, slv_racunovodja_sg_gen, slv_racunovodja_sg_prep, slv_racunovodja_sg_dat, slv_racunovodja_sg_ins],
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_ta_n.paradigm : Paradigm :=
  { id := "slv_ta_n", lexeme := slv_ta, forms := [slv_ta_n_nom, slv_ta_n_acc, slv_ta_n_gen, slv_ta_n_prep, slv_ta_n_dat, slv_ta_n_ins],
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl.paradigm : Paradigm :=
  { id := "slv_potnik_pl", lexeme := slv_potnik, forms := [slv_potnik_pl_nom, slv_potnik_pl_acc, slv_potnik_pl_gen, slv_potnik_pl_prep, slv_potnik_pl_dat, slv_potnik_pl_ins],
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f.paradigm : Paradigm :=
  { id := "slv_ta_f", lexeme := slv_ta, forms := [slv_ta_f_nom, slv_ta_f_acc, slv_ta_f_gen, slv_ta_f_prep, slv_ta_f_dat, slv_ta_f_ins],
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_tisti_n.paradigm : Paradigm :=
  { id := "slv_tisti_n", lexeme := slv_tisti, forms := [slv_tisti_n_nom, slv_tisti_n_acc, slv_tisti_n_gen, slv_tisti_n_prep, slv_tisti_n_dat, slv_tisti_n_ins],
    source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_vas_n.paradigm : Paradigm :=
  { id := "slv_vas_n", lexeme := slv_vas, forms := [slv_vas_n_nom, slv_vas_n_acc, slv_vas_n_gen, slv_vas_n_prep, slv_vas_n_dat, slv_vas_n_ins],
    source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def ces_okno_sg.paradigm : Paradigm :=
  { id := "ces_okno_sg", lexeme := ces_okno, forms := [ces_okno_sg_nom, ces_okno_sg_acc, ces_okno_sg_gen, ces_okno_sg_prep, ces_okno_sg_dat, ces_okno_sg_ins],
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg.paradigm : Paradigm :=
  { id := "ces_ulice_sg", lexeme := ces_ulice, forms := [ces_ulice_sg_nom, ces_ulice_sg_acc, ces_ulice_sg_gen, ces_ulice_sg_prep, ces_ulice_sg_dat, ces_ulice_sg_ins],
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl.paradigm : Paradigm :=
  { id := "ces_muz_pl", lexeme := ces_muz, forms := [ces_muz_pl_nom, ces_muz_pl_acc, ces_muz_pl_gen, ces_muz_pl_prep, ces_muz_pl_dat, ces_muz_pl_ins],
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_sg.paradigm : Paradigm :=
  { id := "ces_muz_sg", lexeme := ces_muz, forms := [ces_muz_sg_nom, ces_muz_sg_acc, ces_muz_sg_gen, ces_muz_sg_prep, ces_muz_sg_dat, ces_muz_sg_ins],
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg.paradigm : Paradigm :=
  { id := "ces_dobry_fsg", lexeme := ces_dobry, forms := [ces_dobry_fsg_nom, ces_dobry_fsg_acc, ces_dobry_fsg_gen, ces_dobry_fsg_prep, ces_dobry_fsg_dat, ces_dobry_fsg_ins],
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_mpl_2.paradigm : Paradigm :=
  { id := "ces_dobry_mpl_2", lexeme := ces_dobry, forms := [ces_dobry_mpl_2_nom, ces_dobry_mpl_2_acc, ces_dobry_mpl_2_gen, ces_dobry_mpl_2_prep, ces_dobry_mpl_2_dat, ces_dobry_mpl_2_ins],
    source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_vetsi_msg.paradigm : Paradigm :=
  { id := "ces_vetsi_msg", lexeme := ces_vetsi, forms := [ces_vetsi_msg_nom, ces_vetsi_msg_acc, ces_vetsi_msg_gen, ces_vetsi_msg_prep, ces_vetsi_msg_dat, ces_vetsi_msg_ins],
    source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_oba.paradigm : Paradigm :=
  { id := "ces_oba", lexeme := ces_oba, forms := [ces_oba_nom, ces_oba_acc, ces_oba_gen, ces_oba_prep, ces_oba_dat, ces_oba_ins],
    source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_stroj_sg.paradigm : Paradigm :=
  { id := "ces_stroj_sg", lexeme := ces_stroj, forms := [ces_stroj_sg_nom, ces_stroj_sg_acc, ces_stroj_sg_gen, ces_stroj_sg_prep, ces_stroj_sg_dat, ces_stroj_sg_ins],
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl.paradigm : Paradigm :=
  { id := "ces_stroj_pl", lexeme := ces_stroj, forms := [ces_stroj_pl_nom, ces_stroj_pl_acc, ces_stroj_pl_gen, ces_stroj_pl_prep, ces_stroj_pl_dat, ces_stroj_pl_ins],
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl.paradigm : Paradigm :=
  { id := "ces_kost_pl", lexeme := ces_kost, forms := [ces_kost_pl_nom, ces_kost_pl_acc, ces_kost_pl_gen, ces_kost_pl_prep, ces_kost_pl_dat, ces_kost_pl_ins],
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty.paradigm : Paradigm :=
  { id := "ces_ty", lexeme := ces_ten, forms := [ces_ty_nom, ces_ty_acc, ces_ty_gen, ces_ty_prep, ces_ty_dat, ces_ty_ins],
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_vila_sg.paradigm : Paradigm :=
  { id := "ces_vila_sg", lexeme := ces_vila, forms := [ces_vila_sg_nom, ces_vila_sg_acc, ces_vila_sg_gen, ces_vila_sg_prep, ces_vila_sg_dat, ces_vila_sg_ins],
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg.paradigm : Paradigm :=
  { id := "ces_misa_sg", lexeme := ces_misa, forms := [ces_misa_sg_nom, ces_misa_sg_acc, ces_misa_sg_gen, ces_misa_sg_prep, ces_misa_sg_dat, ces_misa_sg_ins],
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vul_pl.paradigm : Paradigm :=
  { id := "ces_vul_pl", lexeme := ces_vul, forms := [ces_vul_pl_nom, ces_vul_pl_acc, ces_vul_pl_gen, ces_vul_pl_prep, ces_vul_pl_dat, ces_vul_pl_ins],
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl.paradigm : Paradigm :=
  { id := "ces_hoch_pl", lexeme := ces_hoch, forms := [ces_hoch_pl_nom, ces_hoch_pl_acc, ces_hoch_pl_gen, ces_hoch_pl_prep, ces_hoch_pl_dat, ces_hoch_pl_ins],
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_pan_sg.paradigm : Paradigm :=
  { id := "ces_pan_sg", lexeme := ces_pan, forms := [ces_pan_sg_nom, ces_pan_sg_acc, ces_pan_sg_gen, ces_pan_sg_prep, ces_pan_sg_dat, ces_pan_sg_ins],
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten.paradigm : Paradigm :=
  { id := "ces_ten", lexeme := ces_ten, forms := [ces_ten_nom, ces_ten_acc, ces_ten_gen, ces_ten_prep, ces_ten_dat, ces_ten_ins],
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2.paradigm : Paradigm :=
  { id := "ces_my_2", lexeme := ces_my, forms := [ces_my_2_nom, ces_my_2_acc, ces_my_2_gen, ces_my_2_prep, ces_my_2_dat, ces_my_2_ins],
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ona.paradigm : Paradigm :=
  { id := "ces_ona", lexeme := ces_ona, forms := [ces_ona_nom, ces_ona_acc, ces_ona_gen, ces_ona_prep, ces_ona_dat, ces_ona_ins],
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg.paradigm : Paradigm :=
  { id := "ces_nase_fsg", lexeme := ces_nase, forms := [ces_nase_fsg_nom, ces_nase_fsg_acc, ces_nase_fsg_gen, ces_nase_fsg_prep, ces_nase_fsg_dat, ces_nase_fsg_ins],
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg.paradigm : Paradigm :=
  { id := "ces_zatez_sg", lexeme := ces_zatez, forms := [ces_zatez_sg_nom, ces_zatez_sg_acc, ces_zatez_sg_gen, ces_zatez_sg_prep, ces_zatez_sg_dat, ces_zatez_sg_ins],
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zena_sg.paradigm : Paradigm :=
  { id := "ces_zena_sg", lexeme := ces_zena, forms := [ces_zena_sg_nom, ces_zena_sg_acc, ces_zena_sg_gen, ces_zena_sg_prep, ces_zena_sg_dat, ces_zena_sg_ins],
    source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_kluk_pl.paradigm : Paradigm :=
  { id := "ces_kluk_pl", lexeme := ces_kluk, forms := [ces_kluk_pl_nom, ces_kluk_pl_acc, ces_kluk_pl_gen, ces_kluk_pl_prep, ces_kluk_pl_dat, ces_kluk_pl_ins],
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial.paradigm : Paradigm :=
  { id := "ces_kluk_pl_colloquial", lexeme := ces_kluk, forms := [ces_kluk_pl_colloquial_nom, ces_kluk_pl_colloquial_acc, ces_kluk_pl_colloquial_gen, ces_kluk_pl_colloquial_prep, ces_kluk_pl_colloquial_dat, ces_kluk_pl_colloquial_ins],
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial.paradigm : Paradigm :=
  { id := "ces_muz_pl_colloquial", lexeme := ces_muz, forms := [ces_muz_pl_colloquial_nom, ces_muz_pl_colloquial_acc, ces_muz_pl_colloquial_gen, ces_muz_pl_colloquial_prep, ces_muz_pl_colloquial_dat, ces_muz_pl_colloquial_ins],
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_zena_pl.paradigm : Paradigm :=
  { id := "ces_zena_pl", lexeme := ces_zena, forms := [ces_zena_pl_nom, ces_zena_pl_acc, ces_zena_pl_gen, ces_zena_pl_prep, ces_zena_pl_dat, ces_zena_pl_ins],
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl.paradigm : Paradigm :=
  { id := "ces_pisen_pl", lexeme := ces_pisen, forms := [ces_pisen_pl_nom, ces_pisen_pl_acc, ces_pisen_pl_gen, ces_pisen_pl_prep, ces_pisen_pl_dat, ces_pisen_pl_ins],
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl.paradigm : Paradigm :=
  { id := "ces_dobry_mpl", lexeme := ces_dobry, forms := [ces_dobry_mpl_nom, ces_dobry_mpl_acc, ces_dobry_mpl_gen, ces_dobry_mpl_prep, ces_dobry_mpl_dat, ces_dobry_mpl_ins],
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_kost_sg.paradigm : Paradigm :=
  { id := "ces_kost_sg", lexeme := ces_kost, forms := [ces_kost_sg_nom, ces_kost_sg_acc, ces_kost_sg_gen, ces_kost_sg_prep, ces_kost_sg_dat, ces_kost_sg_ins],
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg.paradigm : Paradigm :=
  { id := "ces_hrad_sg", lexeme := ces_hrad, forms := [ces_hrad_sg_nom, ces_hrad_sg_acc, ces_hrad_sg_gen, ces_hrad_sg_prep, ces_hrad_sg_dat, ces_hrad_sg_ins],
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my.paradigm : Paradigm :=
  { id := "ces_my", lexeme := ces_my, forms := [ces_my_nom, ces_my_acc, ces_my_gen, ces_my_prep, ces_my_dat, ces_my_ins],
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_mesto_sg.paradigm : Paradigm :=
  { id := "ces_mesto_sg", lexeme := ces_mesto, forms := [ces_mesto_sg_nom, ces_mesto_sg_acc, ces_mesto_sg_gen, ces_mesto_sg_prep, ces_mesto_sg_dat, ces_mesto_sg_ins],
    source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_vetsi_nsg.paradigm : Paradigm :=
  { id := "ces_vetsi_nsg", lexeme := ces_vetsi, forms := [ces_vetsi_nsg_nom, ces_vetsi_nsg_acc, ces_vetsi_nsg_gen, ces_vetsi_nsg_prep, ces_vetsi_nsg_dat, ces_vetsi_nsg_ins],
    source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_ono.paradigm : Paradigm :=
  { id := "ces_ono", lexeme := ces_ono, forms := [ces_ono_nom, ces_ono_acc, ces_ono_gen, ces_ono_prep, ces_ono_dat, ces_ono_ins],
    source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_nase_nsg.paradigm : Paradigm :=
  { id := "ces_nase_nsg", lexeme := ces_nase, forms := [ces_nase_nsg_nom, ces_nase_nsg_acc, ces_nase_nsg_gen, ces_nase_nsg_prep, ces_nase_nsg_dat, ces_nase_nsg_ins],
    source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_vetsi_fsg.paradigm : Paradigm :=
  { id := "ces_vetsi_fsg", lexeme := ces_vetsi, forms := [ces_vetsi_fsg_nom, ces_vetsi_fsg_acc, ces_vetsi_fsg_gen, ces_vetsi_fsg_prep, ces_vetsi_fsg_dat, ces_vetsi_fsg_ins],
    source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_npl.paradigm : Paradigm :=
  { id := "ces_vetsi_npl", lexeme := ces_vetsi, forms := [ces_vetsi_npl_nom, ces_vetsi_npl_acc, ces_vetsi_npl_gen, ces_vetsi_npl_prep, ces_vetsi_npl_dat, ces_vetsi_npl_ins],
    source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_ona_npl.paradigm : Paradigm :=
  { id := "ces_ona_npl", lexeme := ces_oni, forms := [ces_ona_npl_nom, ces_ona_npl_acc, ces_ona_npl_gen, ces_ona_npl_prep, ces_ona_npl_dat, ces_ona_npl_ins],
    source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ta.paradigm : Paradigm :=
  { id := "ces_ta", lexeme := ces_ten, forms := [ces_ta_nom, ces_ta_acc, ces_ta_gen, ces_ta_prep, ces_ta_dat, ces_ta_ins],
    source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_dva.paradigm : Paradigm :=
  { id := "ces_dva", lexeme := ces_dva, forms := [ces_dva_nom, ces_dva_acc, ces_dva_gen, ces_dva_prep, ces_dva_dat, ces_dva_ins],
    source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_pet.paradigm : Paradigm :=
  { id := "ces_pet", lexeme := ces_pet, forms := [ces_pet_nom, ces_pet_acc, ces_pet_gen, ces_pet_prep, ces_pet_dat, ces_pet_ins],
    source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def slk_ona.paradigm : Paradigm :=
  { id := "slk_ona", lexeme := slk_ona, forms := [slk_ona_nom, slk_ona_acc, slk_ona_gen, slk_ona_prep, slk_ona_dat, slk_ona_ins],
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg.paradigm : Paradigm :=
  { id := "slk_nase_fsg", lexeme := slk_nase, forms := [slk_nase_fsg_nom, slk_nase_fsg_acc, slk_nase_fsg_gen, slk_nase_fsg_prep, slk_nase_fsg_dat, slk_nase_fsg_ins],
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg.paradigm : Paradigm :=
  { id := "slk_ulica_sg", lexeme := slk_ulica, forms := [slk_ulica_sg_nom, slk_ulica_sg_acc, slk_ulica_sg_gen, slk_ulica_sg_prep, slk_ulica_sg_dat, slk_ulica_sg_ins],
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg.paradigm : Paradigm :=
  { id := "slk_tlac_sg", lexeme := slk_tlac, forms := [slk_tlac_sg_nom, slk_tlac_sg_acc, slk_tlac_sg_gen, slk_tlac_sg_prep, slk_tlac_sg_dat, slk_tlac_sg_ins],
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def ukr_kraj_sg.paradigm : Paradigm :=
  { id := "ukr_kraj_sg", lexeme := ukr_kraj, forms := [ukr_kraj_sg_nom, ukr_kraj_sg_acc, ukr_kraj_sg_gen, ukr_kraj_sg_prep, ukr_kraj_sg_dat, ukr_kraj_sg_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl.paradigm : Paradigm :=
  { id := "ukr_velykyj_pl", lexeme := ukr_velykyj, forms := [ukr_velykyj_pl_nom, ukr_velykyj_pl_acc, ukr_velykyj_pl_gen, ukr_velykyj_pl_prep, ukr_velykyj_pl_dat, ukr_velykyj_pl_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg.paradigm : Paradigm :=
  { id := "ukr_znannja_sg", lexeme := ukr_znannja, forms := [ukr_znannja_sg_nom, ukr_znannja_sg_acc, ukr_znannja_sg_gen, ukr_znannja_sg_prep, ukr_znannja_sg_dat, ukr_znannja_sg_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my.paradigm : Paradigm :=
  { id := "ukr_my", lexeme := ukr_my, forms := [ukr_my_nom, ukr_my_acc, ukr_my_gen, ukr_my_prep, ukr_my_dat, ukr_my_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg.paradigm : Paradigm :=
  { id := "ukr_kasyr_sg", lexeme := ukr_kasyr, forms := [ukr_kasyr_sg_nom, ukr_kasyr_sg_acc, ukr_kasyr_sg_gen, ukr_kasyr_sg_prep, ukr_kasyr_sg_dat, ukr_kasyr_sg_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl.paradigm : Paradigm :=
  { id := "ukr_kasyr_pl", lexeme := ukr_kasyr, forms := [ukr_kasyr_pl_nom, ukr_kasyr_pl_acc, ukr_kasyr_pl_gen, ukr_kasyr_pl_prep, ukr_kasyr_pl_dat, ukr_kasyr_pl_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_maty_sg.paradigm : Paradigm :=
  { id := "ukr_maty_sg", lexeme := ukr_maty, forms := [ukr_maty_sg_nom, ukr_maty_sg_acc, ukr_maty_sg_gen, ukr_maty_sg_prep, ukr_maty_sg_dat, ukr_maty_sg_ins],
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg.paradigm : Paradigm :=
  { id := "ukr_ruka_sg", lexeme := ukr_ruka, forms := [ukr_ruka_sg_nom, ukr_ruka_sg_acc, ukr_ruka_sg_gen, ukr_ruka_sg_prep, ukr_ruka_sg_dat, ukr_ruka_sg_ins],
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja.paradigm : Paradigm :=
  { id := "ukr_ja", lexeme := ukr_ja, forms := [ukr_ja_nom, ukr_ja_acc, ukr_ja_gen, ukr_ja_prep, ukr_ja_dat, ukr_ja_ins],
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg.paradigm : Paradigm :=
  { id := "ukr_velykyj_msg", lexeme := ukr_velykyj, forms := [ukr_velykyj_msg_nom, ukr_velykyj_msg_acc, ukr_velykyj_msg_gen, ukr_velykyj_msg_prep, ukr_velykyj_msg_dat, ukr_velykyj_msg_ins],
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto.paradigm : Paradigm :=
  { id := "ukr_sto", lexeme := ukr_sto, forms := [ukr_sto_nom, ukr_sto_acc, ukr_sto_gen, ukr_sto_prep, ukr_sto_dat, ukr_sto_ins],
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_kraj_sg_2.paradigm : Paradigm :=
  { id := "ukr_kraj_sg_2", lexeme := ukr_kraj, forms := [ukr_kraj_sg_2_nom, ukr_kraj_sg_2_acc, ukr_kraj_sg_2_gen, ukr_kraj_sg_2_prep, ukr_kraj_sg_2_dat, ukr_kraj_sg_2_ins],
    source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_bezkrajij_msg.paradigm : Paradigm :=
  { id := "ukr_bezkrajij_msg", lexeme := ukr_bezkrajij, forms := [ukr_bezkrajij_msg_nom, ukr_bezkrajij_msg_acc, ukr_bezkrajij_msg_gen, ukr_bezkrajij_msg_prep, ukr_bezkrajij_msg_dat, ukr_bezkrajij_msg_ins],
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2.paradigm : Paradigm :=
  { id := "ukr_bezkrajij_msg_2", lexeme := ukr_bezkrajij, forms := [ukr_bezkrajij_msg_2_nom, ukr_bezkrajij_msg_2_acc, ukr_bezkrajij_msg_2_gen, ukr_bezkrajij_msg_2_prep, ukr_bezkrajij_msg_2_dat, ukr_bezkrajij_msg_2_ins],
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_velykyj_msg_2.paradigm : Paradigm :=
  { id := "ukr_velykyj_msg_2", lexeme := ukr_velykyj, forms := [ukr_velykyj_msg_2_nom, ukr_velykyj_msg_2_acc, ukr_velykyj_msg_2_gen, ukr_velykyj_msg_2_prep, ukr_velykyj_msg_2_dat, ukr_velykyj_msg_2_ins],
    source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [srp_sin, srp_grad, srp_muz, srp_selo, srp_srce, srp_ovca, srp_smrt, srp_ja, srp_ti, srp_on, srp_ona, srp_mi, srp_vi, srp_oni, slv_miza, slv_breskev, slv_jabolko, slv_kmet, slv_jaz, slv_moj, slv_dva, slv_mi, slv_midva, slv_nit, slv_gospa, slv_dan, slv_racunovodja, slv_ta, slv_potnik, slv_tisti, slv_vas, ces_okno, ces_ulice, ces_muz, ces_dobry, ces_vetsi, ces_oba, ces_stroj, ces_kost, ces_ten, ces_vila, ces_misa, ces_vul, ces_hoch, ces_pan, ces_my, ces_ona, ces_nase, ces_zatez, ces_zena, ces_kluk, ces_pisen, ces_hrad, ces_mesto, ces_ono, ces_oni, ces_dva, ces_pet, slk_ona, slk_nase, slk_ulica, slk_tlac, ukr_kraj, ukr_velykyj, ukr_znannja, ukr_my, ukr_kasyr, ukr_maty, ukr_ruka, ukr_ja, ukr_sto, ukr_bezkrajij]

/-- Every form of the data. -/
def forms : List Form := [srp_sin_sg_nom, srp_sin_sg_acc, srp_sin_sg_gen, srp_sin_sg_prep, srp_sin_sg_dat, srp_sin_sg_ins, srp_grad_sg_nom, srp_grad_sg_acc, srp_grad_sg_gen, srp_grad_sg_prep, srp_grad_sg_dat, srp_grad_sg_ins, srp_muz_sg_nom, srp_muz_sg_acc, srp_muz_sg_gen, srp_muz_sg_prep, srp_muz_sg_dat, srp_muz_sg_ins, srp_selo_sg_nom, srp_selo_sg_acc, srp_selo_sg_gen, srp_selo_sg_prep, srp_selo_sg_dat, srp_selo_sg_ins, srp_srce_sg_nom, srp_srce_sg_acc, srp_srce_sg_gen, srp_srce_sg_prep, srp_srce_sg_dat, srp_srce_sg_ins, srp_ovca_sg_nom, srp_ovca_sg_acc, srp_ovca_sg_gen, srp_ovca_sg_prep, srp_ovca_sg_dat, srp_ovca_sg_ins, srp_smrt_sg_nom, srp_smrt_sg_acc, srp_smrt_sg_gen, srp_smrt_sg_prep, srp_smrt_sg_dat, srp_smrt_sg_ins, srp_sin_pl_nom, srp_sin_pl_acc, srp_sin_pl_gen, srp_sin_pl_prep, srp_sin_pl_dat, srp_sin_pl_ins, srp_grad_pl_nom, srp_grad_pl_acc, srp_grad_pl_gen, srp_grad_pl_prep, srp_grad_pl_dat, srp_grad_pl_ins, srp_muz_pl_nom, srp_muz_pl_acc, srp_muz_pl_gen, srp_muz_pl_prep, srp_muz_pl_dat, srp_muz_pl_ins, srp_selo_pl_nom, srp_selo_pl_acc, srp_selo_pl_gen, srp_selo_pl_prep, srp_selo_pl_dat, srp_selo_pl_ins, srp_srce_pl_nom, srp_srce_pl_acc, srp_srce_pl_gen, srp_srce_pl_prep, srp_srce_pl_dat, srp_srce_pl_ins, srp_ovca_pl_nom, srp_ovca_pl_acc, srp_ovca_pl_gen, srp_ovca_pl_prep, srp_ovca_pl_dat, srp_ovca_pl_ins, srp_smrt_pl_nom, srp_smrt_pl_acc, srp_smrt_pl_gen, srp_smrt_pl_prep, srp_smrt_pl_dat, srp_smrt_pl_ins, srp_ja_nom, srp_ja_acc, srp_ja_gen, srp_ja_prep, srp_ja_dat, srp_ja_ins, srp_ti_nom, srp_ti_acc, srp_ti_gen, srp_ti_prep, srp_ti_dat, srp_ti_ins, srp_on_nom, srp_on_acc, srp_on_gen, srp_on_prep, srp_on_dat, srp_on_ins, srp_ona_nom, srp_ona_acc, srp_ona_gen, srp_ona_prep, srp_ona_dat, srp_ona_ins, srp_mi_nom, srp_mi_acc, srp_mi_gen, srp_mi_prep, srp_mi_dat, srp_mi_ins, srp_vi_nom, srp_vi_acc, srp_vi_gen, srp_vi_prep, srp_vi_dat, srp_vi_ins, srp_oni_nom, srp_oni_acc, srp_oni_gen, srp_oni_prep, srp_oni_dat, srp_oni_ins, slv_miza_du_nom, slv_miza_du_acc, slv_miza_du_gen, slv_miza_du_prep, slv_miza_du_dat, slv_miza_du_ins, slv_breskev_sg_nom, slv_breskev_sg_acc, slv_breskev_sg_gen, slv_breskev_sg_prep, slv_breskev_sg_dat, slv_breskev_sg_ins, slv_breskev_pl_nom, slv_breskev_pl_acc, slv_breskev_pl_gen, slv_breskev_pl_prep, slv_breskev_pl_dat, slv_breskev_pl_ins, slv_jabolko_sg_nom, slv_jabolko_sg_acc, slv_jabolko_sg_gen, slv_jabolko_sg_prep, slv_jabolko_sg_dat, slv_jabolko_sg_ins, slv_kmet_du_nom, slv_kmet_du_acc, slv_kmet_du_gen, slv_kmet_du_prep, slv_kmet_du_dat, slv_kmet_du_ins, slv_kmet_sg_nom, slv_kmet_sg_acc, slv_kmet_sg_gen, slv_kmet_sg_prep, slv_kmet_sg_dat, slv_kmet_sg_ins, slv_jaz_nom, slv_jaz_acc, slv_jaz_gen, slv_jaz_prep, slv_jaz_dat, slv_jaz_ins, slv_moj_mpl_nom, slv_moj_mpl_acc, slv_moj_mpl_gen, slv_moj_mpl_prep, slv_moj_mpl_dat, slv_moj_mpl_ins, slv_dva_nom, slv_dva_acc, slv_dva_gen, slv_dva_prep, slv_dva_dat, slv_dva_ins, slv_mi_nom, slv_mi_acc, slv_mi_gen, slv_mi_prep, slv_mi_dat, slv_mi_ins, slv_midva_nom, slv_midva_acc, slv_midva_gen, slv_midva_prep, slv_midva_dat, slv_midva_ins, slv_nit_sg_nom, slv_nit_sg_acc, slv_nit_sg_gen, slv_nit_sg_prep, slv_nit_sg_dat, slv_nit_sg_ins, slv_gospa_sg_nom, slv_gospa_sg_acc, slv_gospa_sg_gen, slv_gospa_sg_prep, slv_gospa_sg_dat, slv_gospa_sg_ins, slv_dan_du_nom, slv_dan_du_acc, slv_dan_du_gen, slv_dan_du_prep, slv_dan_du_dat, slv_dan_du_ins, slv_racunovodja_sg_nom, slv_racunovodja_sg_acc, slv_racunovodja_sg_gen, slv_racunovodja_sg_prep, slv_racunovodja_sg_dat, slv_racunovodja_sg_ins, slv_ta_n_nom, slv_ta_n_acc, slv_ta_n_gen, slv_ta_n_prep, slv_ta_n_dat, slv_ta_n_ins, slv_potnik_pl_nom, slv_potnik_pl_acc, slv_potnik_pl_gen, slv_potnik_pl_prep, slv_potnik_pl_dat, slv_potnik_pl_ins, slv_ta_f_nom, slv_ta_f_acc, slv_ta_f_gen, slv_ta_f_prep, slv_ta_f_dat, slv_ta_f_ins, slv_tisti_n_nom, slv_tisti_n_acc, slv_tisti_n_gen, slv_tisti_n_prep, slv_tisti_n_dat, slv_tisti_n_ins, slv_vas_n_nom, slv_vas_n_acc, slv_vas_n_gen, slv_vas_n_prep, slv_vas_n_dat, slv_vas_n_ins, ces_okno_sg_nom, ces_okno_sg_acc, ces_okno_sg_gen, ces_okno_sg_prep, ces_okno_sg_dat, ces_okno_sg_ins, ces_ulice_sg_nom, ces_ulice_sg_acc, ces_ulice_sg_gen, ces_ulice_sg_prep, ces_ulice_sg_dat, ces_ulice_sg_ins, ces_muz_pl_nom, ces_muz_pl_acc, ces_muz_pl_gen, ces_muz_pl_prep, ces_muz_pl_dat, ces_muz_pl_ins, ces_muz_sg_nom, ces_muz_sg_acc, ces_muz_sg_gen, ces_muz_sg_prep, ces_muz_sg_dat, ces_muz_sg_ins, ces_dobry_fsg_nom, ces_dobry_fsg_acc, ces_dobry_fsg_gen, ces_dobry_fsg_prep, ces_dobry_fsg_dat, ces_dobry_fsg_ins, ces_dobry_mpl_2_nom, ces_dobry_mpl_2_acc, ces_dobry_mpl_2_gen, ces_dobry_mpl_2_prep, ces_dobry_mpl_2_dat, ces_dobry_mpl_2_ins, ces_vetsi_msg_nom, ces_vetsi_msg_acc, ces_vetsi_msg_gen, ces_vetsi_msg_prep, ces_vetsi_msg_dat, ces_vetsi_msg_ins, ces_oba_nom, ces_oba_acc, ces_oba_gen, ces_oba_prep, ces_oba_dat, ces_oba_ins, ces_stroj_sg_nom, ces_stroj_sg_acc, ces_stroj_sg_gen, ces_stroj_sg_prep, ces_stroj_sg_dat, ces_stroj_sg_ins, ces_stroj_pl_nom, ces_stroj_pl_acc, ces_stroj_pl_gen, ces_stroj_pl_prep, ces_stroj_pl_dat, ces_stroj_pl_ins, ces_kost_pl_nom, ces_kost_pl_acc, ces_kost_pl_gen, ces_kost_pl_prep, ces_kost_pl_dat, ces_kost_pl_ins, ces_ty_nom, ces_ty_acc, ces_ty_gen, ces_ty_prep, ces_ty_dat, ces_ty_ins, ces_vila_sg_nom, ces_vila_sg_acc, ces_vila_sg_gen, ces_vila_sg_prep, ces_vila_sg_dat, ces_vila_sg_ins, ces_misa_sg_nom, ces_misa_sg_acc, ces_misa_sg_gen, ces_misa_sg_prep, ces_misa_sg_dat, ces_misa_sg_ins, ces_vul_pl_nom, ces_vul_pl_acc, ces_vul_pl_gen, ces_vul_pl_prep, ces_vul_pl_dat, ces_vul_pl_ins, ces_hoch_pl_nom, ces_hoch_pl_acc, ces_hoch_pl_gen, ces_hoch_pl_prep, ces_hoch_pl_dat, ces_hoch_pl_ins, ces_pan_sg_nom, ces_pan_sg_acc, ces_pan_sg_gen, ces_pan_sg_prep, ces_pan_sg_dat, ces_pan_sg_ins, ces_ten_nom, ces_ten_acc, ces_ten_gen, ces_ten_prep, ces_ten_dat, ces_ten_ins, ces_my_2_nom, ces_my_2_acc, ces_my_2_gen, ces_my_2_prep, ces_my_2_dat, ces_my_2_ins, ces_ona_nom, ces_ona_acc, ces_ona_gen, ces_ona_prep, ces_ona_dat, ces_ona_ins, ces_nase_fsg_nom, ces_nase_fsg_acc, ces_nase_fsg_gen, ces_nase_fsg_prep, ces_nase_fsg_dat, ces_nase_fsg_ins, ces_zatez_sg_nom, ces_zatez_sg_acc, ces_zatez_sg_gen, ces_zatez_sg_prep, ces_zatez_sg_dat, ces_zatez_sg_ins, ces_zena_sg_nom, ces_zena_sg_acc, ces_zena_sg_gen, ces_zena_sg_prep, ces_zena_sg_dat, ces_zena_sg_ins, ces_kluk_pl_nom, ces_kluk_pl_acc, ces_kluk_pl_gen, ces_kluk_pl_prep, ces_kluk_pl_dat, ces_kluk_pl_ins, ces_kluk_pl_colloquial_nom, ces_kluk_pl_colloquial_acc, ces_kluk_pl_colloquial_gen, ces_kluk_pl_colloquial_prep, ces_kluk_pl_colloquial_dat, ces_kluk_pl_colloquial_ins, ces_muz_pl_colloquial_nom, ces_muz_pl_colloquial_acc, ces_muz_pl_colloquial_gen, ces_muz_pl_colloquial_prep, ces_muz_pl_colloquial_dat, ces_muz_pl_colloquial_ins, ces_zena_pl_nom, ces_zena_pl_acc, ces_zena_pl_gen, ces_zena_pl_prep, ces_zena_pl_dat, ces_zena_pl_ins, ces_pisen_pl_nom, ces_pisen_pl_acc, ces_pisen_pl_gen, ces_pisen_pl_prep, ces_pisen_pl_dat, ces_pisen_pl_ins, ces_dobry_mpl_nom, ces_dobry_mpl_acc, ces_dobry_mpl_gen, ces_dobry_mpl_prep, ces_dobry_mpl_dat, ces_dobry_mpl_ins, ces_kost_sg_nom, ces_kost_sg_acc, ces_kost_sg_gen, ces_kost_sg_prep, ces_kost_sg_dat, ces_kost_sg_ins, ces_hrad_sg_nom, ces_hrad_sg_acc, ces_hrad_sg_gen, ces_hrad_sg_prep, ces_hrad_sg_dat, ces_hrad_sg_ins, ces_my_nom, ces_my_acc, ces_my_gen, ces_my_prep, ces_my_dat, ces_my_ins, ces_mesto_sg_nom, ces_mesto_sg_acc, ces_mesto_sg_gen, ces_mesto_sg_prep, ces_mesto_sg_dat, ces_mesto_sg_ins, ces_vetsi_nsg_nom, ces_vetsi_nsg_acc, ces_vetsi_nsg_gen, ces_vetsi_nsg_prep, ces_vetsi_nsg_dat, ces_vetsi_nsg_ins, ces_ono_nom, ces_ono_acc, ces_ono_gen, ces_ono_prep, ces_ono_dat, ces_ono_ins, ces_nase_nsg_nom, ces_nase_nsg_acc, ces_nase_nsg_gen, ces_nase_nsg_prep, ces_nase_nsg_dat, ces_nase_nsg_ins, ces_vetsi_fsg_nom, ces_vetsi_fsg_acc, ces_vetsi_fsg_gen, ces_vetsi_fsg_prep, ces_vetsi_fsg_dat, ces_vetsi_fsg_ins, ces_vetsi_npl_nom, ces_vetsi_npl_acc, ces_vetsi_npl_gen, ces_vetsi_npl_prep, ces_vetsi_npl_dat, ces_vetsi_npl_ins, ces_ona_npl_nom, ces_ona_npl_acc, ces_ona_npl_gen, ces_ona_npl_prep, ces_ona_npl_dat, ces_ona_npl_ins, ces_ta_nom, ces_ta_acc, ces_ta_gen, ces_ta_prep, ces_ta_dat, ces_ta_ins, ces_dva_nom, ces_dva_acc, ces_dva_gen, ces_dva_prep, ces_dva_dat, ces_dva_ins, ces_pet_nom, ces_pet_acc, ces_pet_gen, ces_pet_prep, ces_pet_dat, ces_pet_ins, slk_ona_nom, slk_ona_acc, slk_ona_gen, slk_ona_prep, slk_ona_dat, slk_ona_ins, slk_nase_fsg_nom, slk_nase_fsg_acc, slk_nase_fsg_gen, slk_nase_fsg_prep, slk_nase_fsg_dat, slk_nase_fsg_ins, slk_ulica_sg_nom, slk_ulica_sg_acc, slk_ulica_sg_gen, slk_ulica_sg_prep, slk_ulica_sg_dat, slk_ulica_sg_ins, slk_tlac_sg_nom, slk_tlac_sg_acc, slk_tlac_sg_gen, slk_tlac_sg_prep, slk_tlac_sg_dat, slk_tlac_sg_ins, ukr_kraj_sg_nom, ukr_kraj_sg_acc, ukr_kraj_sg_gen, ukr_kraj_sg_prep, ukr_kraj_sg_dat, ukr_kraj_sg_ins, ukr_velykyj_pl_nom, ukr_velykyj_pl_acc, ukr_velykyj_pl_gen, ukr_velykyj_pl_prep, ukr_velykyj_pl_dat, ukr_velykyj_pl_ins, ukr_znannja_sg_nom, ukr_znannja_sg_acc, ukr_znannja_sg_gen, ukr_znannja_sg_prep, ukr_znannja_sg_dat, ukr_znannja_sg_ins, ukr_my_nom, ukr_my_acc, ukr_my_gen, ukr_my_prep, ukr_my_dat, ukr_my_ins, ukr_kasyr_sg_nom, ukr_kasyr_sg_acc, ukr_kasyr_sg_gen, ukr_kasyr_sg_prep, ukr_kasyr_sg_dat, ukr_kasyr_sg_ins, ukr_kasyr_pl_nom, ukr_kasyr_pl_acc, ukr_kasyr_pl_gen, ukr_kasyr_pl_prep, ukr_kasyr_pl_dat, ukr_kasyr_pl_ins, ukr_maty_sg_nom, ukr_maty_sg_acc, ukr_maty_sg_gen, ukr_maty_sg_prep, ukr_maty_sg_dat, ukr_maty_sg_ins, ukr_ruka_sg_nom, ukr_ruka_sg_acc, ukr_ruka_sg_gen, ukr_ruka_sg_prep, ukr_ruka_sg_dat, ukr_ruka_sg_ins, ukr_ja_nom, ukr_ja_acc, ukr_ja_gen, ukr_ja_prep, ukr_ja_dat, ukr_ja_ins, ukr_velykyj_msg_nom, ukr_velykyj_msg_acc, ukr_velykyj_msg_gen, ukr_velykyj_msg_prep, ukr_velykyj_msg_dat, ukr_velykyj_msg_ins, ukr_sto_nom, ukr_sto_acc, ukr_sto_gen, ukr_sto_prep, ukr_sto_dat, ukr_sto_ins, ukr_kraj_sg_2_nom, ukr_kraj_sg_2_acc, ukr_kraj_sg_2_gen, ukr_kraj_sg_2_prep, ukr_kraj_sg_2_dat, ukr_kraj_sg_2_ins, ukr_bezkrajij_msg_nom, ukr_bezkrajij_msg_acc, ukr_bezkrajij_msg_gen, ukr_bezkrajij_msg_prep, ukr_bezkrajij_msg_dat, ukr_bezkrajij_msg_ins, ukr_bezkrajij_msg_2_nom, ukr_bezkrajij_msg_2_acc, ukr_bezkrajij_msg_2_gen, ukr_bezkrajij_msg_2_prep, ukr_bezkrajij_msg_2_dat, ukr_bezkrajij_msg_2_ins, ukr_velykyj_msg_2_nom, ukr_velykyj_msg_2_acc, ukr_velykyj_msg_2_gen, ukr_velykyj_msg_2_prep, ukr_velykyj_msg_2_dat, ukr_velykyj_msg_2_ins]

/-- Every paradigm of the data. -/
def paradigms : List Paradigm := [srp_sin_sg.paradigm, srp_grad_sg.paradigm, srp_muz_sg.paradigm, srp_selo_sg.paradigm, srp_srce_sg.paradigm, srp_ovca_sg.paradigm, srp_smrt_sg.paradigm, srp_sin_pl.paradigm, srp_grad_pl.paradigm, srp_muz_pl.paradigm, srp_selo_pl.paradigm, srp_srce_pl.paradigm, srp_ovca_pl.paradigm, srp_smrt_pl.paradigm, srp_ja.paradigm, srp_ti.paradigm, srp_on.paradigm, srp_ona.paradigm, srp_mi.paradigm, srp_vi.paradigm, srp_oni.paradigm, slv_miza_du.paradigm, slv_breskev_sg.paradigm, slv_breskev_pl.paradigm, slv_jabolko_sg.paradigm, slv_kmet_du.paradigm, slv_kmet_sg.paradigm, slv_jaz.paradigm, slv_moj_mpl.paradigm, slv_dva.paradigm, slv_mi.paradigm, slv_midva.paradigm, slv_nit_sg.paradigm, slv_gospa_sg.paradigm, slv_dan_du.paradigm, slv_racunovodja_sg.paradigm, slv_ta_n.paradigm, slv_potnik_pl.paradigm, slv_ta_f.paradigm, slv_tisti_n.paradigm, slv_vas_n.paradigm, ces_okno_sg.paradigm, ces_ulice_sg.paradigm, ces_muz_pl.paradigm, ces_muz_sg.paradigm, ces_dobry_fsg.paradigm, ces_dobry_mpl_2.paradigm, ces_vetsi_msg.paradigm, ces_oba.paradigm, ces_stroj_sg.paradigm, ces_stroj_pl.paradigm, ces_kost_pl.paradigm, ces_ty.paradigm, ces_vila_sg.paradigm, ces_misa_sg.paradigm, ces_vul_pl.paradigm, ces_hoch_pl.paradigm, ces_pan_sg.paradigm, ces_ten.paradigm, ces_my_2.paradigm, ces_ona.paradigm, ces_nase_fsg.paradigm, ces_zatez_sg.paradigm, ces_zena_sg.paradigm, ces_kluk_pl.paradigm, ces_kluk_pl_colloquial.paradigm, ces_muz_pl_colloquial.paradigm, ces_zena_pl.paradigm, ces_pisen_pl.paradigm, ces_dobry_mpl.paradigm, ces_kost_sg.paradigm, ces_hrad_sg.paradigm, ces_my.paradigm, ces_mesto_sg.paradigm, ces_vetsi_nsg.paradigm, ces_ono.paradigm, ces_nase_nsg.paradigm, ces_vetsi_fsg.paradigm, ces_vetsi_npl.paradigm, ces_ona_npl.paradigm, ces_ta.paradigm, ces_dva.paradigm, ces_pet.paradigm, slk_ona.paradigm, slk_nase_fsg.paradigm, slk_ulica_sg.paradigm, slk_tlac_sg.paradigm, ukr_kraj_sg.paradigm, ukr_velykyj_pl.paradigm, ukr_znannja_sg.paradigm, ukr_my.paradigm, ukr_kasyr_sg.paradigm, ukr_kasyr_pl.paradigm, ukr_maty_sg.paradigm, ukr_ruka_sg.paradigm, ukr_ja.paradigm, ukr_velykyj_msg.paradigm, ukr_sto.paradigm, ukr_kraj_sg_2.paradigm, ukr_bezkrajij_msg.paradigm, ukr_bezkrajij_msg_2.paradigm, ukr_velykyj_msg_2.paradigm]

end Caha2009.Paradigms
