module

public import Linglib.Data.Forms.Schema

/-!
# `Audring2019` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Audring2019.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Audring2019.Forms`.
-/

@[expose] public section

namespace Audring2019.Forms

open Data.Forms

def boyish : Form :=
  { id := "audring2019_boyish"
    languageId := "stan1293"
    parameterId := "like_a_boy"
    form := "boyish"
    segments := ["boy", "ish"]
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def foolish : Form :=
  { id := "audring2019_foolish"
    languageId := "stan1293"
    parameterId := "like_a_fool"
    form := "foolish"
    segments := ["fool", "ish"]
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def childish : Form :=
  { id := "audring2019_childish"
    languageId := "stan1293"
    parameterId := "like_a_child"
    form := "childish"
    segments := ["child", "ish"]
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def trumpish : Form :=
  { id := "audring2019_trumpish"
    languageId := "stan1293"
    parameterId := "like_trump"
    form := "Trumpish"
    segments := ["Trump", "ish"]
    source := [
      ⟨"audring-2019", "4.1"⟩
    ] }

def careful : Form :=
  { id := "audring2019_careful"
    languageId := "stan1293"
    parameterId := "careful"
    form := "careful"
    segments := ["care", "ful"]
    source := [
      ⟨"audring-2019", "5"⟩
    ] }

def careless : Form :=
  { id := "audring2019_careless"
    languageId := "stan1293"
    parameterId := "careless"
    form := "careless"
    segments := ["care", "less"]
    source := [
      ⟨"audring-2019", "5"⟩
    ] }

def clueless : Form :=
  { id := "audring2019_clueless"
    languageId := "stan1293"
    parameterId := "clueless"
    form := "clueless"
    segments := ["clue", "less"]
    source := [
      ⟨"audring-2019", "4.2.2"⟩
    ] }

def all : List Form := [boyish, foolish, childish, trumpish, careful, careless, clueless]

def relations : List FormRelation := [
  { id := "audring2019_boyish_foolish", form := boyish, target := foolish, relation := "same_affix", source := [
      ⟨"audring-2019", "(8)"⟩
    ] },
  { id := "audring2019_boyish_childish", form := boyish, target := childish, relation := "same_affix", source := [
      ⟨"audring-2019", "(8)"⟩
    ] },
  { id := "audring2019_foolish_childish", form := foolish, target := childish, relation := "same_affix", source := [
      ⟨"audring-2019", "(8)"⟩
    ] },
  { id := "audring2019_careful_careless", form := careful, target := careless, relation := "second_order_schema", source := [
      ⟨"audring-2019", "(14)"⟩
    ] }
]

end Audring2019.Forms
