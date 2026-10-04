module

public import Linglib.Data.Forms.Schema

/-!
# `Yolyan2025` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Yolyan2025.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Yolyan2025.Forms`.
-/

@[expose] public section

namespace Yolyan2025.Forms

open Data.Forms

def f_2_11a_1 : Form :=
  { id := "yolyan2025_2_11a_1"
    languageId := "bemb1257"
    parameterId := "they_will_arrive"
    form := "bá-ká-fík-á"
    segments := ["b", "á", "+", "k", "á", "+", "f", "í", "k", "+", "á"]
    comment := "Copperbelt Bemba data cited from Bickmore and Kula (2013) and Kula and Bickmore (2015)."
    source := [
      ⟨"yolyan-2025", "Example 2.11 (a)"⟩
    ]
    columns := [("Underlying", "/bá-ka-fik-a/")] }

def f_2_11a_2 : Form :=
  { id := "yolyan2025_2_11a_2"
    languageId := "bemb1257"
    parameterId := "they_will_introduce_him_her"
    form := "bá-ká-mú-lóndólól-á"
    segments := ["b", "á", "+", "k", "á", "+", "m", "ú", "+", "l", "ó", "n", "d", "ó", "l", "ó", "l", "+", "á"]
    comment := ""
    source := [
      ⟨"yolyan-2025", "Example 2.11 (a)"⟩
    ]
    columns := [("Underlying", "/bá-ka-mu-londolol-a/")] }

def f_2_11b_1 : Form :=
  { id := "yolyan2025_2_11b_1"
    languageId := "bemb1257"
    parameterId := "they_will_hate"
    form := "bá-ká-pát-à kó"
    segments := ["b", "á", "+", "k", "á", "+", "p", "á", "t", "+", "à", "_", "k", "ó"]
    comment := "The following high tone of kó blocks unbounded spreading; only the next two vowels surface high."
    source := [
      ⟨"yolyan-2025", "Example 2.11 (b)"⟩
    ]
    columns := [("Underlying", "/bá-ka-pat-a kó/")] }

def f_2_11b_2 : Form :=
  { id := "yolyan2025_2_11b_2"
    languageId := "bemb1257"
    parameterId := "they_will_introduce_them"
    form := "bá-ká-ló-òndòlòl-à kó"
    segments := ["b", "á", "+", "k", "á", "+", "l", "ó", "+", "ò", "n", "d", "ò", "l", "ò", "l", "+", "à", "_", "k", "ó"]
    comment := "Form as printed in the paper; the root londolol is split across the second spread vowel."
    source := [
      ⟨"yolyan-2025", "Example 2.11 (b)"⟩
    ]
    columns := [("Underlying", "/bá-ka-londolol-a kó/")] }

def f_2_11c : Form :=
  { id := "yolyan2025_2_11c"
    languageId := "bemb1257"
    parameterId := "to_pierce"
    form := "ù-kù-tùl-à"
    segments := ["ù", "+", "k", "ù", "+", "t", "ù", "l", "+", "à"]
    comment := "No underlying high tone; every vowel surfaces low by default."
    source := [
      ⟨"yolyan-2025", "Example 2.11 (c)"⟩
    ]
    columns := [("Underlying", "/u-ku-tul-a/")] }

def all : List Form := [f_2_11a_1, f_2_11a_2, f_2_11b_1, f_2_11b_2, f_2_11c]

def parameters : List Parameter := [
  { id := "they_will_arrive", name := "they will arrive", description := "" },
  { id := "they_will_introduce_him_her", name := "they will introduce him/her", description := "" },
  { id := "they_will_hate", name := "they will hate", description := "" },
  { id := "they_will_introduce_them", name := "they will introduce them", description := "" },
  { id := "to_pierce", name := "to pierce", description := "" }
]

def relations : List FormRelation := []

end Yolyan2025.Forms
