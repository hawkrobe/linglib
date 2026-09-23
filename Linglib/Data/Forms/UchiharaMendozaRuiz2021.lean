module

public import Linglib.Data.Forms.Schema

/-!
# `UchiharaMendozaRuiz2021` — CLDF form data

Auto-generated from `Linglib/Data/Forms/UchiharaMendozaRuiz2021.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace UchiharaMendozaRuiz2021.Forms`.
-/

@[expose] public section

namespace UchiharaMendozaRuiz2021.Forms

open Data.Forms

def ja3a3 : Form :=
  { id := "uchiharamendozaruiz2021_ja3a3"
    languageId := "alco1235"
    parameterId := "white"
    form := "ja3a3"
    segments := ["j", "a3", "a3"]
    comment := "monosyllabic stem lengthened to a bimoraic foot; the input /ja/ is monomoraic"
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(15)"⟩
    ] }

def ki3ti4 : Form :=
  { id := "uchiharamendozaruiz2021_ki3ti4"
    languageId := "alco1235"
    parameterId := "animal"
    form := "ki3ti4"
    segments := ["k", "i3", "t", "i4"]
    comment := "disyllabic stem, no lengthening: a bimoraic foot already"
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(16)"⟩
    ] }

def ti1kwi14i2 : Form :=
  { id := "uchiharamendozaruiz2021_ti1kwi14i2"
    languageId := "alco1235"
    parameterId := "water"
    form := "ti1kwi14i2"
    segments := ["t", "i1", "kw", "i14", "i2"]
    comment := "lexical accent on the final mora lengthens the final syllable; the initial syllable is unfooted"
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(17)"⟩
    ] }

def ma4ka2 : Form :=
  { id := "uchiharamendozaruiz2021_ma4ka2"
    languageId := "alco1235"
    parameterId := "hammock"
    form := "ma4ka2"
    segments := ["m", "a4", "k", "a2"]
    comment := "Spanish hamaca truncated to the bimoraic foot; the tonic syllables coincide"
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(42a)"⟩
    ] }

def skwe4la2 : Form :=
  { id := "uchiharamendozaruiz2021_skwe4la2"
    languageId := "alco1235"
    parameterId := "school"
    form := "skwe4la2"
    segments := ["s", "kw", "e4", "l", "a2"]
    comment := "Spanish escuela truncated to the bimoraic foot"
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(42d)"⟩
    ] }

def pe3lo3 : Form :=
  { id := "uchiharamendozaruiz2021_pe3lo3"
    languageId := "alco1235"
    parameterId := "buzzard"
    form := "pe3lo3"
    segments := ["p", "e3", "l", "o3"]
    comment := "Spanish zopilote truncated to the bimoraic foot although the tonic syllables differ: maximality, not foot alignment"
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(43a)"⟩
    ] }

def po3li3si4a2 : Form :=
  { id := "uchiharamendozaruiz2021_po3li3si4a2"
    languageId := "alco1235"
    parameterId := "police"
    form := "po3li3si4a2"
    segments := ["p", "o3", "l", "i3", "s", "i4", "a2"]
    comment := "a more recent loan from Spanish policía, not truncated: two unfooted syllables before the foot"
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(44a)"⟩
    ] }

def nu3mi3 : Form :=
  { id := "uchiharamendozaruiz2021_nu3mi3"
    languageId := "alco1235"
    parameterId := "hug"
    form := "nu3mi3"
    segments := ["n", "u3", "m", "i3"]
    comment := "the stem, tone 3 initial"
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(64)"⟩
    ] }

def nu2mi3 : Form :=
  { id := "uchiharamendozaruiz2021_nu2mi3"
    languageId := "alco1235"
    parameterId := "hugged"
    form := "nu2mi3"
    segments := ["n", "u2", "m", "i3"]
    comment := "perfective realized by tone alone, tone 1 of the prefix coalescing with stem tone 3 into tone 2, rather than by the prefix ni1- that would leave a mora unfooted"
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(64)"⟩
    ] }

def ni1shi14ko3 : Form :=
  { id := "uchiharamendozaruiz2021_ni1shi14ko3"
    languageId := "alco1235"
    parameterId := "sold"
    form := "ni1shi14ko3"
    segments := ["n", "i1", "sh", "i14", "k", "o3"]
    comment := "the segmental perfective prefix with a tone 14 stem; the prefix mora is unfooted, PARSE(µ) being dominated by REALIZE-MORPHEME"
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(5)"⟩
    ] }

def all : List Form := [ja3a3, ki3ti4, ti1kwi14i2, ma4ka2, skwe4la2, pe3lo3, po3li3si4a2, nu3mi3, nu2mi3, ni1shi14ko3]

def parameters : List Parameter := [
  { id := "white", name := "white", description := "" },
  { id := "animal", name := "animal", description := "" },
  { id := "water", name := "water", description := "" },
  { id := "hammock", name := "hammock", description := "loan from Spanish hamaca" },
  { id := "school", name := "school", description := "loan from Spanish escuela" },
  { id := "buzzard", name := "buzzard", description := "loan from Spanish zopilote" },
  { id := "police", name := "police", description := "loan from Spanish policía" },
  { id := "hug", name := "hug", description := "verb stem" },
  { id := "hugged", name := "hugged", description := "perfective" },
  { id := "sold", name := "sold", description := "perfective" }
]

def relations : List FormRelation := [
  { id := "uchiharamendozaruiz2021_nu3mi3_nu2mi3", formId := "uchiharamendozaruiz2021_nu3mi3", targetId := "uchiharamendozaruiz2021_nu2mi3", relation := "perfective", source := [
      ⟨"uchihara-mendozaruiz-2021", "(64)"⟩
    ] }
]

end UchiharaMendozaRuiz2021.Forms
