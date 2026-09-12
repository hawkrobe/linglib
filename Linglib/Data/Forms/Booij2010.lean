import Linglib.Data.Forms.Schema

/-!
# `Booij2010` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Booij2010.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Booij2010.Forms`.
-/

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
    comment := "a stored deadjectival noun of the opening word set"
    source := [
      ⟨"booij-2010-compass", ""⟩
    ] }

def awareness : Form :=
  { id := "booij2010_awareness"
    languageId := "stan1293"
    parameterId := "awareness"
    form := "awareness"
    segments := ["aware", "ness"]
    comment := "the paper's example of an existing deadjectival noun"
    source := [
      ⟨"booij-2010-compass", ""⟩
    ] }

def all : List Form := [carlessness, baldness, awareness]

def parameters : List Parameter := [
  { id := "carlessness", name := "the state of being without a car", description := "" },
  { id := "baldness", name := "baldness", description := "" },
  { id := "awareness", name := "awareness", description := "" }
]

def relations : List FormRelation := []

end Booij2010.Forms
