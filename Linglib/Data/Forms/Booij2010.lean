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
    comment := "the paper's novel coin (Time, October 5, 2009)"
    source := [
      ⟨"booij-2010-compass", ""⟩
    ] }

def baldness : Form :=
  { id := "booij2010_baldness"
    languageId := "stan1293"
    parameterId := "baldness"
    form := "baldness"
    segments := ["bald", "ness"]
    comment := "a stored deadjectival noun of the opening word set (1b)"
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def bigness : Form :=
  { id := "booij2010_bigness"
    languageId := "stan1293"
    parameterId := "bigness"
    form := "bigness"
    segments := ["big", "ness"]
    comment := "a stored deadjectival noun of the opening word set (1b)"
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def blackness : Form :=
  { id := "booij2010_blackness"
    languageId := "stan1293"
    parameterId := "blackness"
    form := "blackness"
    segments := ["black", "ness"]
    comment := "a stored deadjectival noun of the opening word set (1b)"
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def britishness : Form :=
  { id := "booij2010_britishness"
    languageId := "stan1293"
    parameterId := "britishness"
    form := "Britishness"
    segments := ["British", "ness"]
    comment := "a stored deadjectival noun of the opening word set (1b)"
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def awareness : Form :=
  { id := "booij2010_awareness"
    languageId := "stan1293"
    parameterId := "awareness"
    form := "awareness"
    segments := ["aware", "ness"]
    comment := "the paper's example of an existing deadjectival noun (2)"
    source := [
      ⟨"booij-2010-compass", "(2)"⟩
    ] }

def leesbaar : Form :=
  { id := "booij2010_leesbaar"
    languageId := "dutc1256"
    parameterId := "readable"
    form := "leesbaar"
    segments := ["lees", "baar"]
    comment := "a regular -baar adjective on the transitive verb lezen"
    source := [
      ⟨"booij-2010-compass", ""⟩
    ] }

def werkbaar : Form :=
  { id := "booij2010_werkbaar"
    languageId := "dutc1256"
    parameterId := "workable"
    form := "werkbaar"
    segments := ["werk", "baar"]
    comment := "a -baar adjective on the intransitive verb werken, overriding the schema's transitive base"
    source := [
      ⟨"booij-2010-compass", ""⟩
    ] }

def onbedwingbaar : Form :=
  { id := "booij2010_onbedwingbaar"
    languageId := "dutc1256"
    parameterId := "unsuppressable"
    form := "onbedwingbaar"
    segments := ["on", "bedwing", "baar"]
    comment := "coined directly from the verb bedwingen by the unified schema (16), with no listed bedwingbaar"
    source := [
      ⟨"booij-2010-compass", "(15)"⟩
    ] }

def all : List Form := [carlessness, baldness, bigness, blackness, britishness, awareness, leesbaar, werkbaar, onbedwingbaar]

def parameters : List Parameter := [
  { id := "carlessness", name := "the state of being without a car", description := "" },
  { id := "baldness", name := "baldness", description := "" },
  { id := "bigness", name := "bigness", description := "" },
  { id := "blackness", name := "blackness", description := "" },
  { id := "britishness", name := "Britishness", description := "" },
  { id := "awareness", name := "awareness", description := "" },
  { id := "readable", name := "readable", description := "" },
  { id := "workable", name := "workable", description := "" },
  { id := "unsuppressable", name := "unsuppressable", description := "" }
]

def relations : List FormRelation := []

end Booij2010.Forms
