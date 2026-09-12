import Linglib.Data.Forms.Schema

/-!
# `Booij2019` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Booij2019.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Booij2019.Forms`.
-/

namespace Booij2019.Forms

open Data.Forms

def xabbaaz : Form :=
  { id := "booij2019_xabbaaz"
    languageId := "nort3139"
    parameterId := "baker"
    form := "xabbaaz"
    segments := ["x", "a", "b", "b", "aa", "z"]
    comment := "occupation noun of the template C₁aC₂C₂aaC₃ (2); a long vowel is one segment"
    source := [
      ⟨"booij-2019", "(1)"⟩
    ] }

def xaddaam : Form :=
  { id := "booij2019_xaddaam"
    languageId := "nort3139"
    parameterId := "servant"
    form := "xaddaam"
    segments := ["x", "a", "d", "d", "aa", "m"]
    comment := "occupation noun of the template C₁aC₂C₂aaC₃ (2); a long vowel is one segment"
    source := [
      ⟨"booij-2019", "(1)"⟩
    ] }

def bawwaab : Form :=
  { id := "booij2019_bawwaab"
    languageId := "nort3139"
    parameterId := "doorkeeper"
    form := "bawwaab"
    segments := ["b", "a", "w", "w", "aa", "b"]
    comment := "occupation noun of the template C₁aC₂C₂aaC₃ (2); a long vowel is one segment"
    source := [
      ⟨"booij-2019", "(1)"⟩
    ] }

def sammaak : Form :=
  { id := "booij2019_sammaak"
    languageId := "nort3139"
    parameterId := "fish_seller"
    form := "sammaak"
    segments := ["s", "a", "m", "m", "aa", "k"]
    comment := "occupation noun of the template C₁aC₂C₂aaC₃ (2); a long vowel is one segment"
    source := [
      ⟨"booij-2019", "(1)"⟩
    ] }

def tamu : Form :=
  { id := "booij2019_tamu"
    languageId := "java1254"
    parameterId := "guest"
    form := "tamu"
    segments := ["t", "amu"]
    comment := "base of the reduplication (13); the residue after the initial consonant is one segment, the paper's variable y"
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def tetamu : Form :=
  { id := "booij2019_tetamu"
    languageId := "java1254"
    parameterId := "to_visit"
    form := "tətamu"
    segments := ["t", "ə", "t", "amu"]
    comment := "partial reduplication (13): the initial consonant copied, then the schwa"
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def jawah : Form :=
  { id := "booij2019_jawah"
    languageId := "java1254"
    parameterId := "rain"
    form := "jawah"
    segments := ["j", "awah"]
    comment := "base of the reduplication (13)"
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def jejawah : Form :=
  { id := "booij2019_jejawah"
    languageId := "java1254"
    parameterId := "to_play_in_the_rain"
    form := "jəjawah"
    segments := ["j", "ə", "j", "awah"]
    comment := "partial reduplication (13)"
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def geni : Form :=
  { id := "booij2019_geni"
    languageId := "java1254"
    parameterId := "fire"
    form := "gəni"
    segments := ["g", "əni"]
    comment := "base of the reduplication (13)"
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def gegeni : Form :=
  { id := "booij2019_gegeni"
    languageId := "java1254"
    parameterId := "to_warm_oneself_by_the_fire"
    form := "gəgəni"
    segments := ["g", "ə", "g", "əni"]
    comment := "partial reduplication (13)"
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def kibiir : Form :=
  { id := "booij2019_kibiir"
    languageId := "egyp1253"
    parameterId := "big"
    form := "kibiir"
    segments := ["k", "i", "b", "ii", "r"]
    comment := "adjective of the template C₁VC₂VC₃ (16)"
    source := [
      ⟨"booij-2019", "(15)"⟩
    ] }

def akbar : Form :=
  { id := "booij2019_akbar"
    languageId := "egyp1253"
    parameterId := "bigger"
    form := "akbar"
    segments := ["a", "k", "b", "a", "r"]
    comment := "comparative of the template aC₁C₂aC₃ (16)"
    source := [
      ⟨"booij-2019", "(15)"⟩
    ] }

def tixiin : Form :=
  { id := "booij2019_tixiin"
    languageId := "egyp1253"
    parameterId := "fat"
    form := "tixiin"
    segments := ["t", "i", "x", "ii", "n"]
    comment := "adjective of the template C₁VC₂VC₃ (16)"
    source := [
      ⟨"booij-2019", "(15)"⟩
    ] }

def atxan : Form :=
  { id := "booij2019_atxan"
    languageId := "egyp1253"
    parameterId := "fatter"
    form := "atxan"
    segments := ["a", "t", "x", "a", "n"]
    comment := "comparative of the template aC₁C₂aC₃ (16)"
    source := [
      ⟨"booij-2019", "(15)"⟩
    ] }

def all : List Form := [xabbaaz, xaddaam, bawwaab, sammaak, tamu, tetamu, jawah, jejawah, geni, gegeni, kibiir, akbar, tixiin, atxan]

def parameters : List Parameter := [
  { id := "baker", name := "baker", description := "" },
  { id := "servant", name := "servant", description := "" },
  { id := "doorkeeper", name := "doorkeeper", description := "" },
  { id := "fish_seller", name := "fish seller", description := "" },
  { id := "guest", name := "guest", description := "" },
  { id := "to_visit", name := "to visit", description := "" },
  { id := "rain", name := "rain", description := "" },
  { id := "to_play_in_the_rain", name := "to play in the rain", description := "" },
  { id := "fire", name := "fire", description := "" },
  { id := "to_warm_oneself_by_the_fire", name := "to warm oneself by the fire", description := "" },
  { id := "big", name := "big", description := "" },
  { id := "bigger", name := "bigger", description := "" },
  { id := "fat", name := "fat", description := "" },
  { id := "fatter", name := "fatter", description := "" }
]

def relations : List FormRelation := [
  { id := "booij2019_tamu_tetamu", formId := "booij2019_tamu", targetId := "booij2019_tetamu", relation := "reduplication", source := [
      ⟨"booij-2019", "(12)"⟩
    ] },
  { id := "booij2019_jawah_jejawah", formId := "booij2019_jawah", targetId := "booij2019_jejawah", relation := "reduplication", source := [
      ⟨"booij-2019", "(12)"⟩
    ] },
  { id := "booij2019_geni_gegeni", formId := "booij2019_geni", targetId := "booij2019_gegeni", relation := "reduplication", source := [
      ⟨"booij-2019", "(12)"⟩
    ] },
  { id := "booij2019_kibiir_akbar", formId := "booij2019_kibiir", targetId := "booij2019_akbar", relation := "comparative", source := [
      ⟨"booij-2019", "(15)"⟩
    ] },
  { id := "booij2019_tixiin_atxan", formId := "booij2019_tixiin", targetId := "booij2019_atxan", relation := "comparative", source := [
      ⟨"booij-2019", "(15)"⟩
    ] }
]

end Booij2019.Forms
