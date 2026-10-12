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
    comment := ""
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
    comment := ""
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
    comment := ""
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
    comment := ""
    source := [
      ⟨"arregi-pietraszko-2021", "(19)"⟩
    ]
    columns := [("Lnk", "a"), ("D", "u"), ("T", "lu")] }

def all : List Form := [f_19_cl1, f_19_cl9, f_19_cl7, f_19_cl11]

def parameters : List Parameter := [
  { id := "rel_cl1", name := "1REL", description := "relative agreement prefix of class 1" },
  { id := "rel_cl9", name := "9REL", description := "relative agreement prefix of class 9" },
  { id := "rel_cl7", name := "7REL", description := "relative agreement prefix of class 7" },
  { id := "rel_cl11", name := "11REL", description := "relative agreement prefix of class 11" }
]

def relations : List FormRelation := []

end ArregiPietraszko2021.Forms
