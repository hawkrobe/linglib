module

public import Linglib.Data.Forms.Schema

/-!
# `JackendoffAudring2020` — CLDF form data

Auto-generated from `Linglib/Data/Forms/JackendoffAudring2020.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace JackendoffAudring2020.Forms`.
-/

@[expose] public section

namespace JackendoffAudring2020.Forms

open Data.Forms

def sing : Form :=
  { id := "jackendoffaudring2020_sing"
    languageId := "stan1293"
    parameterId := "sing"
    form := "sing"
    segments := ["s", "ɪ", "ŋ"]
    source := [
      ⟨"jackendoff-audring-2020", "(24)"⟩
    ] }

def sang : Form :=
  { id := "jackendoffaudring2020_sang"
    languageId := "stan1293"
    parameterId := "sing_past"
    form := "sang"
    segments := ["s", "æ", "ŋ"]
    source := [
      ⟨"jackendoff-audring-2020", "(24)"⟩
    ] }

def string : Form :=
  { id := "jackendoffaudring2020_string"
    languageId := "stan1293"
    parameterId := "string"
    form := "string"
    segments := ["str", "ɪ", "ŋ"]
    source := [
      ⟨"jackendoff-audring-2020", "(26)"⟩
    ] }

def strung : Form :=
  { id := "jackendoffaudring2020_strung"
    languageId := "stan1293"
    parameterId := "string_past"
    form := "strung"
    segments := ["str", "ʌ", "ŋ"]
    source := [
      ⟨"jackendoff-audring-2020", "(26)"⟩
    ] }

def sprech : Form :=
  { id := "jackendoffaudring2020_sprech"
    languageId := "stan1295"
    parameterId := "speak_stem"
    form := "sprech-"
    segments := ["ʃpr", "ɛ", "x"]
    source := [
      ⟨"jackendoff-audring-2020", "(43)"⟩
    ] }

def sprich : Form :=
  { id := "jackendoffaudring2020_sprich"
    languageId := "stan1295"
    parameterId := "speak_stem_present_2_3_sg"
    form := "sprich-"
    segments := ["ʃpr", "ɪ", "x"]
    source := [
      ⟨"jackendoff-audring-2020", "(43)"⟩
    ] }

def piggish : Form :=
  { id := "jackendoffaudring2020_piggish"
    languageId := "stan1293"
    parameterId := "like_a_pig"
    form := "piggish"
    segments := ["pig", "ish"]
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1 (5)"⟩
    ] }

def childish : Form :=
  { id := "jackendoffaudring2020_childish"
    languageId := "stan1293"
    parameterId := "like_a_child"
    form := "childish"
    segments := ["child", "ish"]
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1 (5)"⟩
    ] }

def sluggish : Form :=
  { id := "jackendoffaudring2020_sluggish"
    languageId := "stan1293"
    parameterId := "like_a_slug"
    form := "sluggish"
    segments := ["slug", "ish"]
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1 (5)"⟩
    ] }

def foolish : Form :=
  { id := "jackendoffaudring2020_foolish"
    languageId := "stan1293"
    parameterId := "like_a_fool"
    form := "foolish"
    segments := ["fool", "ish"]
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1"⟩
    ] }

def arrowheadLake : Form :=
  { id := "jackendoffaudring2020_arrowheadLake"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Arrowhead Lake"
    segments := ["Arrowhead", "Lake"]
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def loonMountain : Form :=
  { id := "jackendoffaudring2020_loonMountain"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Loon Mountain"
    segments := ["Loon", "Mountain"]
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def wissahickonCreek : Form :=
  { id := "jackendoffaudring2020_wissahickonCreek"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Wissahickon Creek"
    segments := ["Wissahickon", "Creek"]
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def laurelHill : Form :=
  { id := "jackendoffaudring2020_laurelHill"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Laurel Hill"
    segments := ["Laurel", "Hill"]
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def sugarIsland : Form :=
  { id := "jackendoffaudring2020_sugarIsland"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Sugar Island"
    segments := ["Sugar", "Island"]
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def mountEverest : Form :=
  { id := "jackendoffaudring2020_mountEverest"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Mount Everest"
    segments := ["Mount", "Everest"]
    source := [
      ⟨"jackendoff-audring-2020", "(17b)"⟩
    ] }

def lakeMichigan : Form :=
  { id := "jackendoffaudring2020_lakeMichigan"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Lake Michigan"
    segments := ["Lake", "Michigan"]
    source := [
      ⟨"jackendoff-audring-2020", "(17b)"⟩
    ] }

def capeCod : Form :=
  { id := "jackendoffaudring2020_capeCod"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Cape Cod"
    segments := ["Cape", "Cod"]
    source := [
      ⟨"jackendoff-audring-2020", "(17b)"⟩
    ] }

def bayOfFundy : Form :=
  { id := "jackendoffaudring2020_bayOfFundy"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "the Bay of Fundy"
    segments := ["the", "Bay", "of", "Fundy"]
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def gulfOfStLawrence : Form :=
  { id := "jackendoffaudring2020_gulfOfStLawrence"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "the Gulf of St. Lawrence"
    segments := ["the", "Gulf", "of", "St. Lawrence"]
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def capeOfGoodHope : Form :=
  { id := "jackendoffaudring2020_capeOfGoodHope"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "the Cape of Good Hope"
    segments := ["the", "Cape", "of", "Good Hope"]
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def isleOfWight : Form :=
  { id := "jackendoffaudring2020_isleOfWight"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "the Isle of Wight"
    segments := ["the", "Isle", "of", "Wight"]
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def morrisMountain : Form :=
  { id := "jackendoffaudring2020_morrisMountain"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Morris Mountain"
    segments := ["Morris", "Mountain"]
    source := [
      ⟨"jackendoff-audring-2020", "2.7"⟩
    ] }

def mountMorris : Form :=
  { id := "jackendoffaudring2020_mountMorris"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Mount Morris"
    segments := ["Mount", "Morris"]
    source := [
      ⟨"jackendoff-audring-2020", "2.7"⟩
    ] }

def all : List Form := [sing, sang, string, strung, sprech, sprich, piggish, childish, sluggish, foolish, arrowheadLake, loonMountain, wissahickonCreek, laurelHill, sugarIsland, mountEverest, lakeMichigan, capeCod, bayOfFundy, gulfOfStLawrence, capeOfGoodHope, isleOfWight, morrisMountain, mountMorris]

def relations : List FormRelation := [
  { id := "jackendoffaudring2020_sing_sang", form := sing, target := sang, relation := "past", source := [
      ⟨"jackendoff-audring-2020", "(24)"⟩
    ] },
  { id := "jackendoffaudring2020_string_strung", form := string, target := strung, relation := "past", source := [
      ⟨"jackendoff-audring-2020", "(26)"⟩
    ] },
  { id := "jackendoffaudring2020_sprech_sprich", form := sprech, target := sprich, relation := "present_2_3_sg_stem", source := [
      ⟨"jackendoff-audring-2020", "(45)"⟩
    ] }
]

end JackendoffAudring2020.Forms
