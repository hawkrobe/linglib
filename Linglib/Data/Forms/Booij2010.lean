module

public import Linglib.Data.Forms.Schema

/-!
# `Booij2010` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Booij2010.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Booij2010.Forms`.
-/

@[expose] public section

namespace Booij2010.Forms

open Data.Forms

def carlessness : Form :=
  { id := "booij2010_carlessness"
    languageId := "stan1293"
    parameterId := "carlessness"
    form := "carlessness"
    segments := ["carless", "ness"]
    source := [
      ⟨"booij-2010-compass", ""⟩
    ] }

def baldness : Form :=
  { id := "booij2010_baldness"
    languageId := "stan1293"
    parameterId := "baldness"
    form := "baldness"
    segments := ["bald", "ness"]
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def bigness : Form :=
  { id := "booij2010_bigness"
    languageId := "stan1293"
    parameterId := "bigness"
    form := "bigness"
    segments := ["big", "ness"]
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def blackness : Form :=
  { id := "booij2010_blackness"
    languageId := "stan1293"
    parameterId := "blackness"
    form := "blackness"
    segments := ["black", "ness"]
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def britishness : Form :=
  { id := "booij2010_britishness"
    languageId := "stan1293"
    parameterId := "britishness"
    form := "Britishness"
    segments := ["British", "ness"]
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def awareness : Form :=
  { id := "booij2010_awareness"
    languageId := "stan1293"
    parameterId := "awareness"
    form := "awareness"
    segments := ["aware", "ness"]
    source := [
      ⟨"booij-2010-compass", "(2)"⟩
    ] }

def leesbaar : Form :=
  { id := "booij2010_leesbaar"
    languageId := "dutc1256"
    parameterId := "readable"
    form := "leesbaar"
    segments := ["lees", "baar"]
    source := [
      ⟨"booij-2010-compass", ""⟩
    ] }

def werkbaar : Form :=
  { id := "booij2010_werkbaar"
    languageId := "dutc1256"
    parameterId := "workable"
    form := "werkbaar"
    segments := ["werk", "baar"]
    source := [
      ⟨"booij-2010-compass", ""⟩
    ] }

def onbedwingbaar : Form :=
  { id := "booij2010_onbedwingbaar"
    languageId := "dutc1256"
    parameterId := "unsuppressable"
    form := "onbedwingbaar"
    segments := ["on", "bedwing", "baar"]
    source := [
      ⟨"booij-2010-compass", "(15)"⟩
    ] }

def all : List Form := [carlessness, baldness, bigness, blackness, britishness, awareness, leesbaar, werkbaar, onbedwingbaar]

def relations : List FormRelation := []

end Booij2010.Forms
