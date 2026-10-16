module

public import Linglib.Data.Forms.Schema

/-!
# `ArregiPietraszko2021` — CLDF form data

Auto-generated from `Linglib/Data/Forms/ArregiPietraszko2021.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace ArregiPietraszko2021.Forms`.
-/

@[expose] public section

namespace ArregiPietraszko2021.Forms

open Data.Forms

def f_19_cl1 : Form :=
  { id := "arregipietraszko2021_19_cl1"
    languageId := "nort2795"
    parameterId := "rel_cl1"
    form := "o"
    segments := ["o"]
    source := [
      ⟨"arregi-pietraszko-2021", "(19)"⟩
    ]
    columns := [("Lnk", "a"), ("D", "u"), ("T", "u")] }

def f_19_cl9 : Form :=
  { id := "arregipietraszko2021_19_cl9"
    languageId := "nort2795"
    parameterId := "rel_cl9"
    form := "e"
    segments := ["e"]
    source := [
      ⟨"arregi-pietraszko-2021", "(19)"⟩
    ]
    columns := [("Lnk", "a"), ("D", "i"), ("T", "i")] }

def f_19_cl7 : Form :=
  { id := "arregipietraszko2021_19_cl7"
    languageId := "nort2795"
    parameterId := "rel_cl7"
    form := "esi"
    segments := ["e", "s", "i"]
    source := [
      ⟨"arregi-pietraszko-2021", "(19)"⟩
    ]
    columns := [("Lnk", "a"), ("D", "i"), ("T", "si")] }

def f_19_cl11 : Form :=
  { id := "arregipietraszko2021_19_cl11"
    languageId := "nort2795"
    parameterId := "rel_cl11"
    form := "olu"
    segments := ["o", "l", "u"]
    source := [
      ⟨"arregi-pietraszko-2021", "(19)"⟩
    ]
    columns := [("Lnk", "a"), ("D", "u"), ("T", "lu")] }

def doesnt : Form :=
  { id := "arregipietraszko2021_doesnt"
    languageId := "stan1293"
    parameterId := "do_3sg_neg"
    form := "doesn't"
    segments := ["doe", "s", "n't"]
    source := [
      ⟨"arregi-pietraszko-2021", "p. 264"⟩
    ]
    columns := [("Verb", "dummy")] }

def hadnt : Form :=
  { id := "arregipietraszko2021_hadnt"
    languageId := "stan1293"
    parameterId := "have_pst_neg"
    form := "hadn't"
    segments := ["ha", "d", "n't"]
    source := [
      ⟨"arregi-pietraszko-2021", "p. 264"⟩
    ]
    columns := [("Verb", "auxiliary")] }

def all : List Form := [f_19_cl1, f_19_cl9, f_19_cl7, f_19_cl11, doesnt, hadnt]

def relations : List FormRelation := []

end ArregiPietraszko2021.Forms
