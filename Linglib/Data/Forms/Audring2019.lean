import Linglib.Data.Forms.Schema

/-!
# `Audring2019` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Audring2019.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Audring2019.Forms`.
-/

namespace Audring2019.Forms

open Data.Forms

def boyish : Form :=
  { id := "audring2019_boyish"
    languageId := "stan1293"
    parameterId := "like_a_boy"
    form := "boyish"
    segments := ["boy", "ish"]
    comment := "the [N -ish]A family (8)"
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def foolish : Form :=
  { id := "audring2019_foolish"
    languageId := "stan1293"
    parameterId := "like_a_fool"
    form := "foolish"
    segments := ["fool", "ish"]
    comment := "the [N -ish]A family (8)"
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def childish : Form :=
  { id := "audring2019_childish"
    languageId := "stan1293"
    parameterId := "like_a_child"
    form := "childish"
    segments := ["child", "ish"]
    comment := "the [N -ish]A family (8)"
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def trumpish : Form :=
  { id := "audring2019_trumpish"
    languageId := "stan1293"
    parameterId := "like_trump"
    form := "Trumpish"
    segments := ["Trump", "ish"]
    comment := "novel formation showing the base variable is open"
    source := [
      ⟨"audring-2019", "4.1"⟩
    ] }

def careful : Form :=
  { id := "audring2019_careful"
    languageId := "stan1293"
    parameterId := "careful"
    form := "careful"
    segments := ["care", "ful"]
    comment := "the [N -ful]A schema of the second-order schema (14)"
    source := [
      ⟨"audring-2019", "5"⟩
    ] }

def careless : Form :=
  { id := "audring2019_careless"
    languageId := "stan1293"
    parameterId := "careless"
    form := "careless"
    segments := ["care", "less"]
    comment := "the [N -less]A schema of the second-order schema (14)"
    source := [
      ⟨"audring-2019", "5"⟩
    ] }

def clueless : Form :=
  { id := "audring2019_clueless"
    languageId := "stan1293"
    parameterId := "clueless"
    form := "clueless"
    segments := ["clue", "less"]
    comment := "an [N -less]A word with no [N -ful]A sister"
    source := [
      ⟨"audring-2019", "4.2.2"⟩
    ] }

def all : List Form := [boyish, foolish, childish, trumpish, careful, careless, clueless]

def parameters : List Parameter := [
  { id := "like_a_boy", name := "like a boy", description := "" },
  { id := "like_a_fool", name := "like a fool", description := "" },
  { id := "like_a_child", name := "like a child", description := "" },
  { id := "like_trump", name := "like Trump", description := "" },
  { id := "careful", name := "careful", description := "" },
  { id := "careless", name := "careless", description := "" },
  { id := "clueless", name := "clueless", description := "" }
]

def relations : List FormRelation := [
  { id := "audring2019_boyish_foolish", formId := "audring2019_boyish", targetId := "audring2019_foolish", relation := "same_affix", source := [
      ⟨"audring-2019", "(8)"⟩
    ] },
  { id := "audring2019_boyish_childish", formId := "audring2019_boyish", targetId := "audring2019_childish", relation := "same_affix", source := [
      ⟨"audring-2019", "(8)"⟩
    ] },
  { id := "audring2019_foolish_childish", formId := "audring2019_foolish", targetId := "audring2019_childish", relation := "same_affix", source := [
      ⟨"audring-2019", "(8)"⟩
    ] },
  { id := "audring2019_careful_careless", formId := "audring2019_careful", targetId := "audring2019_careless", relation := "second_order_schema", source := [
      ⟨"audring-2019", "(14)"⟩
    ] }
]

end Audring2019.Forms
