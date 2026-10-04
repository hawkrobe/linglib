module

public import Linglib.Data.Forms.Schema

/-!
# `McCollumEtAl2020` — CLDF form data

Auto-generated from `Linglib/Data/Forms/McCollumEtAl2020.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace McCollumEtAl2020.Forms`.
-/

@[expose] public section

namespace McCollumEtAl2020.Forms

open Data.Forms

def f_1a : Form :=
  { id := "mccollumetal2020_1a"
    languageId := "nyan1302"
    parameterId := "3sg_neg_fut_come"
    form := "atɪ́babá"
    segments := ["a", "t", "ɪ́", "b", "a", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(1a)"⟩,
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(5a)"⟩,
      ⟨"yolyan-2025", "Example 2.12 (b)"⟩
    ]
    columns := [("Underlying", "/a-tɪ́-ba-bá/")] }

def f_1b : Form :=
  { id := "mccollumetal2020_1b"
    languageId := "nyan1302"
    parameterId := "3sg_neg_fut_grow"
    form := "etíbeʃē"
    segments := ["e", "t", "í", "b", "e", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(1b)"⟩,
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(5d)"⟩,
      ⟨"yolyan-2025", "Example 2.12 (a)"⟩
    ]
    columns := [("Underlying", "/a-tɪ́-ba-ʃē/")] }

def f_1c : Form :=
  { id := "mccollumetal2020_1c"
    languageId := "nyan1302"
    parameterId := "1sg_neg_fut_come"
    form := "ɪtɪ́babá"
    segments := ["ɪ", "t", "ɪ́", "b", "a", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(1c)"⟩
    ]
    columns := [("Underlying", "/ɪ-tɪ́-ba-bá/")] }

def f_1d : Form :=
  { id := "mccollumetal2020_1d"
    languageId := "nyan1302"
    parameterId := "1sg_neg_fut_grow"
    form := "ɪtɪ́baʃē"
    segments := ["ɪ", "t", "ɪ́", "b", "a", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(1d)"⟩
    ]
    columns := [("Underlying", "/ɪ-tɪ́-ba-ʃē/")] }

def f_2a_man : Form :=
  { id := "mccollumetal2020_2a_man"
    languageId := "nyan1302"
    parameterId := "cl1_man"
    form := "aɲɪ"
    segments := ["a", "ɲ", "ɪ"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(2a)"⟩
    ]
    columns := [("Underlying", "/a-ɲɪ/")] }

def f_2a_dog : Form :=
  { id := "mccollumetal2020_2a_dog"
    languageId := "nyan1302"
    parameterId := "cl1_dog"
    form := "ebú"
    segments := ["e", "b", "ú"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(2a)"⟩
    ]
    columns := [("Underlying", "/a-bú/")] }

def f_2b_copper : Form :=
  { id := "mccollumetal2020_2b_copper"
    languageId := "nyan1302"
    parameterId := "cl3_copper"
    form := "ɔda"
    segments := ["ɔ", "d", "a"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(2b)"⟩
    ]
    columns := [("Underlying", "/ɔ-da/")] }

def f_2b_vulture : Form :=
  { id := "mccollumetal2020_2b_vulture"
    languageId := "nyan1302"
    parameterId := "cl3_vulture"
    form := "opétē"
    segments := ["o", "p", "é", "t", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(2b)"⟩
    ]
    columns := [("Underlying", "/ɔ-pétē/")] }

def f_2c_copper : Form :=
  { id := "mccollumetal2020_2c_copper"
    languageId := "nyan1302"
    parameterId := "cl4_copper"
    form := "ɪda"
    segments := ["ɪ", "d", "a"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(2c)"⟩
    ]
    columns := [("Underlying", "/ɪ-da/")] }

def f_2c_vulture : Form :=
  { id := "mccollumetal2020_2c_vulture"
    languageId := "nyan1302"
    parameterId := "cl4_vulture"
    form := "ipétē"
    segments := ["i", "p", "é", "t", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(2c)"⟩
    ]
    columns := [("Underlying", "/ɪ-pétē/")] }

def f_2d_axe : Form :=
  { id := "mccollumetal2020_2d_axe"
    languageId := "nyan1302"
    parameterId := "cl8_axe"
    form := "bʊwɪ"
    segments := ["b", "ʊ", "w", "ɪ"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(2d)"⟩
    ]
    columns := [("Underlying", "/bʊ-wɪ/")] }

def f_2d_war : Form :=
  { id := "mccollumetal2020_2d_war"
    languageId := "nyan1302"
    parameterId := "cl8_war"
    form := "buju"
    segments := ["b", "u", "j", "u"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(2d)"⟩
    ]
    columns := [("Underlying", "/bʊ-ju/")] }

def f_3a : Form :=
  { id := "mccollumetal2020_3a"
    languageId := "nyan1302"
    parameterId := "1sg_neg_come"
    form := "ɪtɪ́bá"
    segments := ["ɪ", "t", "ɪ́", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(3a)"⟩
    ]
    columns := [("Underlying", "/ɪ-tɪ́-bá/")] }

def f_3b : Form :=
  { id := "mccollumetal2020_3b"
    languageId := "nyan1302"
    parameterId := "1pl_neg_come"
    form := "bʊtɪ́bá"
    segments := ["b", "ʊ", "t", "ɪ́", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(3b)"⟩,
      ⟨"yolyan-2025", "Example 2.12 (b)"⟩
    ]
    columns := [("Underlying", "/bʊ-tɪ́-bá/")] }

def f_3c : Form :=
  { id := "mccollumetal2020_3c"
    languageId := "nyan1302"
    parameterId := "cl5_neg_come"
    form := "kɪtɪ́bá"
    segments := ["k", "ɪ", "t", "ɪ́", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(3c)"⟩
    ]
    columns := [("Underlying", "/kɪ-tɪ́-bá/")] }

def f_3d : Form :=
  { id := "mccollumetal2020_3d"
    languageId := "nyan1302"
    parameterId := "1sg_neg_grow"
    form := "itíʃē"
    segments := ["i", "t", "í", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(3d)"⟩
    ]
    columns := [("Underlying", "/ɪ-tɪ́-ʃē/")] }

def f_3e : Form :=
  { id := "mccollumetal2020_3e"
    languageId := "nyan1302"
    parameterId := "1pl_neg_grow"
    form := "butíʃē"
    segments := ["b", "u", "t", "í", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(3e)"⟩,
      ⟨"yolyan-2025", "Example 2.12 (a)"⟩
    ]
    columns := [("Underlying", "/bʊ-tɪ́-ʃē/")] }

def f_3f : Form :=
  { id := "mccollumetal2020_3f"
    languageId := "nyan1302"
    parameterId := "cl5_neg_grow"
    form := "kitíʃē"
    segments := ["k", "i", "t", "í", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(3f)"⟩
    ]
    columns := [("Underlying", "/kɪ-tɪ́-ʃē/")] }

def f_4a : Form :=
  { id := "mccollumetal2020_4a"
    languageId := "nyan1302"
    parameterId := "3sg_fut_come"
    form := "ababá"
    segments := ["a", "b", "a", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(4a)"⟩
    ]
    columns := [("Underlying", "/a-ba-bá/")] }

def f_4b : Form :=
  { id := "mccollumetal2020_4b"
    languageId := "nyan1302"
    parameterId := "cl7_fut_come"
    form := "kababá"
    segments := ["k", "a", "b", "a", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(4b)"⟩
    ]
    columns := [("Underlying", "/ka-ba-bá/")] }

def f_4c : Form :=
  { id := "mccollumetal2020_4c"
    languageId := "nyan1302"
    parameterId := "2sg_fut_come"
    form := "ɔbɔbá"
    segments := ["ɔ", "b", "ɔ", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(4c)"⟩
    ]
    columns := [("Underlying", "/ɔ-ba-bá/")] }

def f_4d : Form :=
  { id := "mccollumetal2020_4d"
    languageId := "nyan1302"
    parameterId := "3sg_fut_grow"
    form := "ebeʃē"
    segments := ["e", "b", "e", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(4d)"⟩
    ]
    columns := [("Underlying", "/a-ba-ʃē/")] }

def f_4e : Form :=
  { id := "mccollumetal2020_4e"
    languageId := "nyan1302"
    parameterId := "cl7_fut_grow"
    form := "kebeʃē"
    segments := ["k", "e", "b", "e", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(4e)"⟩
    ]
    columns := [("Underlying", "/ka-ba-ʃē/")] }

def f_4f : Form :=
  { id := "mccollumetal2020_4f"
    languageId := "nyan1302"
    parameterId := "2sg_fut_grow"
    form := "oboʃē"
    segments := ["o", "b", "o", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(4f)"⟩
    ]
    columns := [("Underlying", "/ɔ-ba-ʃē/")] }

def f_5b : Form :=
  { id := "mccollumetal2020_5b"
    languageId := "nyan1302"
    parameterId := "cl7_neg_fut_come"
    form := "katɪ́babá"
    segments := ["k", "a", "t", "ɪ́", "b", "a", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(5b)"⟩
    ]
    columns := [("Underlying", "/ka-tɪ́-ba-bá/")] }

def f_5c : Form :=
  { id := "mccollumetal2020_5c"
    languageId := "nyan1302"
    parameterId := "2sg_neg_fut_come"
    form := "ɔtɪ́bɔbá"
    segments := ["ɔ", "t", "ɪ́", "b", "ɔ", "b", "á"]
    comment := "The gloss is printed 2SG-Z-NEG-FUT-come."
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(5c)"⟩
    ]
    columns := [("Underlying", "/ɔ-tɪ́-ba-bá/")] }

def f_5e : Form :=
  { id := "mccollumetal2020_5e"
    languageId := "nyan1302"
    parameterId := "cl7_neg_fut_grow"
    form := "ketíbeʃē"
    segments := ["k", "e", "t", "í", "b", "e", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(5e)"⟩
    ]
    columns := [("Underlying", "/ka-tɪ́-ba-ʃē/")] }

def f_5f : Form :=
  { id := "mccollumetal2020_5f"
    languageId := "nyan1302"
    parameterId := "2sg_neg_fut_grow"
    form := "otíboʃē"
    segments := ["o", "t", "í", "b", "o", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(5f)"⟩
    ]
    columns := [("Underlying", "/ɔ-tɪ́-ba-ʃē/")] }

def f_6a : Form :=
  { id := "mccollumetal2020_6a"
    languageId := "nyan1302"
    parameterId := "1sg_fut_come"
    form := "ɪbabá"
    segments := ["ɪ", "b", "a", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(6a)"⟩
    ]
    columns := [("Underlying", "/ɪ-ba-bá/")] }

def f_6b : Form :=
  { id := "mccollumetal2020_6b"
    languageId := "nyan1302"
    parameterId := "1pl_fut_come"
    form := "bʊbabá"
    segments := ["b", "ʊ", "b", "a", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(6b)"⟩
    ]
    columns := [("Underlying", "/bʊ-ba-bá/")] }

def f_6c : Form :=
  { id := "mccollumetal2020_6c"
    languageId := "nyan1302"
    parameterId := "cl5_fut_come"
    form := "kɪbabá"
    segments := ["k", "ɪ", "b", "a", "b", "á"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(6c)"⟩
    ]
    columns := [("Underlying", "/kɪ-ba-bá/")] }

def f_6d : Form :=
  { id := "mccollumetal2020_6d"
    languageId := "nyan1302"
    parameterId := "1sg_fut_grow"
    form := "ɪbaʃē"
    segments := ["ɪ", "b", "a", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(6d)"⟩
    ]
    columns := [("Underlying", "/ɪ-ba-ʃē/")] }

def f_6e : Form :=
  { id := "mccollumetal2020_6e"
    languageId := "nyan1302"
    parameterId := "1pl_fut_grow"
    form := "bʊbaʃē"
    segments := ["b", "ʊ", "b", "a", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(6e)"⟩
    ]
    columns := [("Underlying", "/bʊ-ba-ʃē/")] }

def f_6f : Form :=
  { id := "mccollumetal2020_6f"
    languageId := "nyan1302"
    parameterId := "cl5_fut_grow"
    form := "kɪbaʃē"
    segments := ["k", "ɪ", "b", "a", "ʃ", "ē"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(6f)"⟩
    ]
    columns := [("Underlying", "/kɪ-ba-ʃē/")] }

def f_7a : Form :=
  { id := "mccollumetal2020_7a"
    languageId := "nyan1302"
    parameterId := "1sg_itv_cook"
    form := "ɪdɪtɔ́"
    segments := ["ɪ", "d", "ɪ", "t", "ɔ́"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(7a)"⟩
    ]
    columns := [("Underlying", "/ɪ-dɪ-tɔ́/")] }

def f_7b : Form :=
  { id := "mccollumetal2020_7b"
    languageId := "nyan1302"
    parameterId := "1sg_itv_climb"
    form := "idiwu"
    segments := ["i", "d", "i", "w", "u"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(7b)"⟩
    ]
    columns := [("Underlying", "/ɪ-dɪ-wu/")] }

def f_7c : Form :=
  { id := "mccollumetal2020_7c"
    languageId := "nyan1302"
    parameterId := "1sg_fut_itv_climb"
    form := "ɪbadiwu"
    segments := ["ɪ", "b", "a", "d", "i", "w", "u"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(7c)"⟩
    ]
    columns := [("Underlying", "/ɪ-ba-dɪ-wu/")] }

def f_7d : Form :=
  { id := "mccollumetal2020_7d"
    languageId := "nyan1302"
    parameterId := "1pl_fut_itv_climb"
    form := "bʊbadiwu"
    segments := ["b", "ʊ", "b", "a", "d", "i", "w", "u"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(7d)"⟩
    ]
    columns := [("Underlying", "/bʊ-ba-dɪ-wu/")] }

def f_8a : Form :=
  { id := "mccollumetal2020_8a"
    languageId := "nyan1302"
    parameterId := "3sg_neg_climb"
    form := "etíwu"
    segments := ["e", "t", "í", "w", "u"]
    comment := "The underlying form is printed /a-atɪ́-wu/."
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(8a)"⟩
    ]
    columns := [("Underlying", "/a-tɪ́-wu/")] }

def f_8b : Form :=
  { id := "mccollumetal2020_8b"
    languageId := "nyan1302"
    parameterId := "1sg_neg_climb"
    form := "itíwu"
    segments := ["i", "t", "í", "w", "u"]
    comment := "The underlying form is printed /i-tɪ́-wu/; the tape (26) runs the word as /ɪ-tɪ́-wu/."
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(8b)"⟩,
      ⟨"yolyan-2025", "Example 2.12 (c)"⟩
    ]
    columns := [("Underlying", "/ɪ-tɪ́-wu/")] }

def f_8c : Form :=
  { id := "mccollumetal2020_8c"
    languageId := "nyan1302"
    parameterId := "1sg_fut_climb"
    form := "ɪbawu"
    segments := ["ɪ", "b", "a", "w", "u"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(8c)"⟩,
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(27b)"⟩,
      ⟨"yolyan-2025", "Example 2.12 (c)"⟩
    ]
    columns := [("Underlying", "/ɪ-ba-wu/")] }

def f_8d : Form :=
  { id := "mccollumetal2020_8d"
    languageId := "nyan1302"
    parameterId := "1sg_neg_pfv_climb"
    form := "ɪtɪ́kawu"
    segments := ["ɪ", "t", "ɪ́", "k", "a", "w", "u"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(8d)"⟩
    ]
    columns := [("Underlying", "/ɪ-tɪ́-ka-wu/")] }

def f_8e : Form :=
  { id := "mccollumetal2020_8e"
    languageId := "nyan1302"
    parameterId := "1sg_neg_pfv_prog_climb"
    form := "ɪtɪ́kaáwū"
    segments := ["ɪ", "t", "ɪ́", "k", "a", "á", "w", "ū"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(8e)"⟩
    ]
    columns := [("Underlying", "/ɪ-tɪ́-ka-á-wu/")] }

def f_8f : Form :=
  { id := "mccollumetal2020_8f"
    languageId := "nyan1302"
    parameterId := "1sg_neg_pfv_prog_vent_climb"
    form := "ɪtɪ́kaábāwū"
    segments := ["ɪ", "t", "ɪ́", "k", "a", "á", "b", "ā", "w", "ū"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(8f)"⟩
    ]
    columns := [("Underlying", "/ɪ-tɪ́-ka-á-ba-wu/")] }

def f_8g : Form :=
  { id := "mccollumetal2020_8g"
    languageId := "nyan1302"
    parameterId := "1sg_neg_pfv_prog_vent_vent_climb"
    form := "ɪtɪ́kaábābāwū"
    segments := ["ɪ", "t", "ɪ́", "k", "a", "á", "b", "ā", "b", "ā", "w", "ū"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(8g)"⟩,
      ⟨"yolyan-2025", "Example 2.12 (c)"⟩
    ]
    columns := [("Underlying", "/ɪ-tɪ́-ka-á-ba-ba-wu/")] }

def f_8h : Form :=
  { id := "mccollumetal2020_8h"
    languageId := "nyan1302"
    parameterId := "3sg_neg_pfv_prog_vent_vent_climb"
    form := "etíkeébēbēwū"
    segments := ["e", "t", "í", "k", "e", "é", "b", "ē", "b", "ē", "w", "ū"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(8h)"⟩,
      ⟨"yolyan-2025", "Example 2.12 (c)"⟩
    ]
    columns := [("Underlying", "/a-tɪ́-ka-á-ba-ba-wu/")] }

def f_27a : Form :=
  { id := "mccollumetal2020_27a"
    languageId := "nyan1302"
    parameterId := "3sg_fut_climb"
    form := "ebewu"
    segments := ["e", "b", "e", "w", "u"]
    comment := ""
    source := [
      ⟨"mccollum-bakovic-mai-meinhardt-2020", "(27a)"⟩
    ]
    columns := [("Underlying", "/a-ba-wu/")] }

def all : List Form := [f_1a, f_1b, f_1c, f_1d, f_2a_man, f_2a_dog, f_2b_copper, f_2b_vulture, f_2c_copper, f_2c_vulture, f_2d_axe, f_2d_war, f_3a, f_3b, f_3c, f_3d, f_3e, f_3f, f_4a, f_4b, f_4c, f_4d, f_4e, f_4f, f_5b, f_5c, f_5e, f_5f, f_6a, f_6b, f_6c, f_6d, f_6e, f_6f, f_7a, f_7b, f_7c, f_7d, f_8a, f_8b, f_8c, f_8d, f_8e, f_8f, f_8g, f_8h, f_27a]

def parameters : List Parameter := [
  { id := "3sg_neg_fut_come", name := "3SG-NEG-FUT-come", description := "" },
  { id := "3sg_neg_fut_grow", name := "3SG-NEG-FUT-grow", description := "" },
  { id := "1sg_neg_fut_come", name := "1SG-NEG-FUT-come", description := "" },
  { id := "1sg_neg_fut_grow", name := "1SG-NEG-FUT-grow", description := "" },
  { id := "cl1_man", name := "CL1-man", description := "" },
  { id := "cl1_dog", name := "CL1-dog", description := "" },
  { id := "cl3_copper", name := "CL3-copper", description := "" },
  { id := "cl3_vulture", name := "CL3-vulture", description := "" },
  { id := "cl4_copper", name := "CL4-copper", description := "" },
  { id := "cl4_vulture", name := "CL4-vulture", description := "" },
  { id := "cl8_axe", name := "CL8-axe", description := "" },
  { id := "cl8_war", name := "CL8-war", description := "" },
  { id := "1sg_neg_come", name := "1SG-NEG-come", description := "" },
  { id := "1pl_neg_come", name := "1PL-NEG-come", description := "" },
  { id := "cl5_neg_come", name := "CL5-NEG-come", description := "" },
  { id := "1sg_neg_grow", name := "1SG-NEG-grow", description := "" },
  { id := "1pl_neg_grow", name := "1PL-NEG-grow", description := "" },
  { id := "cl5_neg_grow", name := "CL5-NEG-grow", description := "" },
  { id := "3sg_fut_come", name := "3SG-FUT-come", description := "" },
  { id := "cl7_fut_come", name := "CL7-FUT-come", description := "" },
  { id := "2sg_fut_come", name := "2SG-FUT-come", description := "" },
  { id := "3sg_fut_grow", name := "3SG-FUT-grow", description := "" },
  { id := "cl7_fut_grow", name := "CL7-FUT-grow", description := "" },
  { id := "2sg_fut_grow", name := "2SG-FUT-grow", description := "" },
  { id := "cl7_neg_fut_come", name := "CL7-NEG-FUT-come", description := "" },
  { id := "2sg_neg_fut_come", name := "2SG-NEG-FUT-come", description := "" },
  { id := "cl7_neg_fut_grow", name := "CL7-NEG-FUT-grow", description := "" },
  { id := "2sg_neg_fut_grow", name := "2SG-NEG-FUT-grow", description := "" },
  { id := "1sg_fut_come", name := "1SG-FUT-come", description := "" },
  { id := "1pl_fut_come", name := "1PL-FUT-come", description := "" },
  { id := "cl5_fut_come", name := "CL5-FUT-come", description := "" },
  { id := "1sg_fut_grow", name := "1SG-FUT-grow", description := "" },
  { id := "1pl_fut_grow", name := "1PL-FUT-grow", description := "" },
  { id := "cl5_fut_grow", name := "CL5-FUT-grow", description := "" },
  { id := "1sg_itv_cook", name := "1SG-ITV-cook", description := "" },
  { id := "1sg_itv_climb", name := "1SG-ITV-climb", description := "" },
  { id := "1sg_fut_itv_climb", name := "1SG-FUT-ITV-climb", description := "" },
  { id := "1pl_fut_itv_climb", name := "1PL-FUT-ITV-climb", description := "" },
  { id := "3sg_neg_climb", name := "3SG-NEG-climb", description := "" },
  { id := "1sg_neg_climb", name := "1SG-NEG-climb", description := "" },
  { id := "1sg_fut_climb", name := "1SG-FUT-climb", description := "" },
  { id := "1sg_neg_pfv_climb", name := "1SG-NEG-PFV-climb", description := "" },
  { id := "1sg_neg_pfv_prog_climb", name := "1SG-NEG-PFV-PROG-climb", description := "" },
  { id := "1sg_neg_pfv_prog_vent_climb", name := "1SG-NEG-PFV-PROG-VENT-climb", description := "" },
  { id := "1sg_neg_pfv_prog_vent_vent_climb", name := "1SG-NEG-PFV-PROG-VENT-VENT-climb", description := "" },
  { id := "3sg_neg_pfv_prog_vent_vent_climb", name := "3SG-NEG-PFV-PROG-VENT-VENT-climb", description := "" },
  { id := "3sg_fut_climb", name := "3SG-FUT-climb", description := "" }
]

def relations : List FormRelation := []

end McCollumEtAl2020.Forms
