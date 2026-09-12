import Linglib.Data.Forms.Schema

/-!
# `JackendoffAudring2020` — CLDF form data

Auto-generated from `Linglib/Data/Forms/JackendoffAudring2020.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace JackendoffAudring2020.Forms`.
-/

namespace JackendoffAudring2020.Forms

open Data.Forms

def sing : Form :=
  { id := "jackendoffaudring2020_sing"
    languageId := "stan1293"
    parameterId := "sing"
    form := "sing"
    segments := ["s", "ɪ", "ŋ"]
    comment := "stem; onset, nucleus, coda"
    source := [
      ⟨"jackendoff-audring-2020", "(24)"⟩
    ] }

def sang : Form :=
  { id := "jackendoffaudring2020_sang"
    languageId := "stan1293"
    parameterId := "sing_past"
    form := "sang"
    segments := ["s", "æ", "ŋ"]
    comment := "past tense; onset, nucleus, coda"
    source := [
      ⟨"jackendoff-audring-2020", "(24)"⟩
    ] }

def string : Form :=
  { id := "jackendoffaudring2020_string"
    languageId := "stan1293"
    parameterId := "string"
    form := "string"
    segments := ["str", "ɪ", "ŋ"]
    comment := "stem; the onset cluster is one segment"
    source := [
      ⟨"jackendoff-audring-2020", "(26)"⟩
    ] }

def strung : Form :=
  { id := "jackendoffaudring2020_strung"
    languageId := "stan1293"
    parameterId := "string_past"
    form := "strung"
    segments := ["str", "ʌ", "ŋ"]
    comment := "past tense"
    source := [
      ⟨"jackendoff-audring-2020", "(26)"⟩
    ] }

def sprech : Form :=
  { id := "jackendoffaudring2020_sprech"
    languageId := "stan1295"
    parameterId := "speak_stem"
    form := "sprech-"
    segments := ["ʃpr", "ɛ", "x"]
    comment := "default stem of sprechen"
    source := [
      ⟨"jackendoff-audring-2020", "(43)"⟩
    ] }

def sprich : Form :=
  { id := "jackendoffaudring2020_sprich"
    languageId := "stan1295"
    parameterId := "speak_stem_present_2_3_sg"
    form := "sprich-"
    segments := ["ʃpr", "ɪ", "x"]
    comment := "special stem of the present 2nd and 3rd singular"
    source := [
      ⟨"jackendoff-audring-2020", "(43)"⟩
    ] }

def piggish : Form :=
  { id := "jackendoffaudring2020_piggish"
    languageId := "stan1293"
    parameterId := "like_a_pig"
    form := "piggish"
    segments := ["pig", "ish"]
    comment := "the -ish sisters of Section 7.8.1"
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1 (5)"⟩
    ] }

def childish : Form :=
  { id := "jackendoffaudring2020_childish"
    languageId := "stan1293"
    parameterId := "like_a_child"
    form := "childish"
    segments := ["child", "ish"]
    comment := "the -ish sisters of Section 7.8.1"
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1 (5)"⟩
    ] }

def sluggish : Form :=
  { id := "jackendoffaudring2020_sluggish"
    languageId := "stan1293"
    parameterId := "like_a_slug"
    form := "sluggish"
    segments := ["slug", "ish"]
    comment := "the -ish sisters of Section 7.8.1"
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1 (5)"⟩
    ] }

def foolish : Form :=
  { id := "jackendoffaudring2020_foolish"
    languageId := "stan1293"
    parameterId := "like_a_fool"
    form := "foolish"
    segments := ["fool", "ish"]
    comment := "the newly encountered sister of Section 7.8.1"
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1"⟩
    ] }

def arrowheadLake : Form :=
  { id := "jackendoffaudring2020_arrowheadLake"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Arrowhead Lake"
    segments := ["Arrowhead", "Lake"]
    comment := "(17a): name then feature"
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def loonMountain : Form :=
  { id := "jackendoffaudring2020_loonMountain"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Loon Mountain"
    segments := ["Loon", "Mountain"]
    comment := "(17a): name then feature"
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def wissahickonCreek : Form :=
  { id := "jackendoffaudring2020_wissahickonCreek"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Wissahickon Creek"
    segments := ["Wissahickon", "Creek"]
    comment := "(17a): name then feature"
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def laurelHill : Form :=
  { id := "jackendoffaudring2020_laurelHill"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Laurel Hill"
    segments := ["Laurel", "Hill"]
    comment := "(17a): name then feature"
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def sugarIsland : Form :=
  { id := "jackendoffaudring2020_sugarIsland"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Sugar Island"
    segments := ["Sugar", "Island"]
    comment := "(17a): name then feature"
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def mountEverest : Form :=
  { id := "jackendoffaudring2020_mountEverest"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Mount Everest"
    segments := ["Mount", "Everest"]
    comment := "(17b): feature then name"
    source := [
      ⟨"jackendoff-audring-2020", "(17b)"⟩
    ] }

def lakeMichigan : Form :=
  { id := "jackendoffaudring2020_lakeMichigan"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Lake Michigan"
    segments := ["Lake", "Michigan"]
    comment := "(17b): feature then name"
    source := [
      ⟨"jackendoff-audring-2020", "(17b)"⟩
    ] }

def capeCod : Form :=
  { id := "jackendoffaudring2020_capeCod"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Cape Cod"
    segments := ["Cape", "Cod"]
    comment := "(17b): feature then name"
    source := [
      ⟨"jackendoff-audring-2020", "(17b)"⟩
    ] }

def bayOfFundy : Form :=
  { id := "jackendoffaudring2020_bayOfFundy"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "the Bay of Fundy"
    segments := ["the", "Bay", "of", "Fundy"]
    comment := "(17d): the feature of name"
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def gulfOfStLawrence : Form :=
  { id := "jackendoffaudring2020_gulfOfStLawrence"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "the Gulf of St. Lawrence"
    segments := ["the", "Gulf", "of", "St. Lawrence"]
    comment := "(17d)"
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def capeOfGoodHope : Form :=
  { id := "jackendoffaudring2020_capeOfGoodHope"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "the Cape of Good Hope"
    segments := ["the", "Cape", "of", "Good Hope"]
    comment := "(17d)"
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def isleOfWight : Form :=
  { id := "jackendoffaudring2020_isleOfWight"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "the Isle of Wight"
    segments := ["the", "Isle", "of", "Wight"]
    comment := "(17d)"
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def morrisMountain : Form :=
  { id := "jackendoffaudring2020_morrisMountain"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Morris Mountain"
    segments := ["Morris", "Mountain"]
    comment := "a coinage the pattern (17a) licenses"
    source := [
      ⟨"jackendoff-audring-2020", "2.7"⟩
    ] }

def mountMorris : Form :=
  { id := "jackendoffaudring2020_mountMorris"
    languageId := "stan1293"
    parameterId := "toponym"
    form := "Mount Morris"
    segments := ["Mount", "Morris"]
    comment := "a coinage the pattern (17b) licenses"
    source := [
      ⟨"jackendoff-audring-2020", "2.7"⟩
    ] }

def all : List Form := [sing, sang, string, strung, sprech, sprich, piggish, childish, sluggish, foolish, arrowheadLake, loonMountain, wissahickonCreek, laurelHill, sugarIsland, mountEverest, lakeMichigan, capeCod, bayOfFundy, gulfOfStLawrence, capeOfGoodHope, isleOfWight, morrisMountain, mountMorris]

def parameters : List Parameter := [
  { id := "sing", name := "sing", description := "" },
  { id := "sing_past", name := "sing (past)", description := "" },
  { id := "string", name := "string", description := "" },
  { id := "string_past", name := "string (past)", description := "" },
  { id := "speak_stem", name := "speak (stem)", description := "" },
  { id := "speak_stem_present_2_3_sg", name := "speak (present 2nd and 3rd singular stem)", description := "" },
  { id := "like_a_pig", name := "like a pig", description := "" },
  { id := "like_a_child", name := "like a child", description := "" },
  { id := "like_a_slug", name := "like a slug", description := "" },
  { id := "like_a_fool", name := "like a fool", description := "" },
  { id := "toponym", name := "name of a geographical feature", description := "" }
]

def relations : List FormRelation := [
  { id := "jackendoffaudring2020_sing_sang", formId := "jackendoffaudring2020_sing", targetId := "jackendoffaudring2020_sang", relation := "past", source := [
      ⟨"jackendoff-audring-2020", "(24)"⟩
    ] },
  { id := "jackendoffaudring2020_string_strung", formId := "jackendoffaudring2020_string", targetId := "jackendoffaudring2020_strung", relation := "past", source := [
      ⟨"jackendoff-audring-2020", "(26)"⟩
    ] },
  { id := "jackendoffaudring2020_sprech_sprich", formId := "jackendoffaudring2020_sprech", targetId := "jackendoffaudring2020_sprich", relation := "present_2_3_sg_stem", source := [
      ⟨"jackendoff-audring-2020", "(45)"⟩
    ] }
]

end JackendoffAudring2020.Forms
