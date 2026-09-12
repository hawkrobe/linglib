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

def all : List Form := [sing, sang, string, strung, sprech, sprich, piggish, childish, sluggish, foolish]

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
  { id := "like_a_fool", name := "like a fool", description := "" }
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
