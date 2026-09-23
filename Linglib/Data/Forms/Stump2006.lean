module

public import Linglib.Data.Forms.Schema

/-!
# `Stump2006` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Stump2006.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Stump2006.Forms`.
-/

@[expose] public section

namespace Stump2006.Forms

open Data.Forms

def room_nom_sg : Form :=
  { id := "stump2006_room_nom_sg"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokoj"
    segments := ["p", "o", "k", "o", "j"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "nom"), ("Number", "sg")] }

def room_gen_sg : Form :=
  { id := "stump2006_room_gen_sg"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokoje"
    segments := ["p", "o", "k", "o", "j", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "gen"), ("Number", "sg")] }

def room_dat_sg : Form :=
  { id := "stump2006_room_dat_sg"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokoji"
    segments := ["p", "o", "k", "o", "j", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "dat"), ("Number", "sg")] }

def room_acc_sg : Form :=
  { id := "stump2006_room_acc_sg"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokoj"
    segments := ["p", "o", "k", "o", "j"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "acc"), ("Number", "sg")] }

def room_voc_sg : Form :=
  { id := "stump2006_room_voc_sg"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokoji"
    segments := ["p", "o", "k", "o", "j", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "voc"), ("Number", "sg")] }

def room_loc_sg : Form :=
  { id := "stump2006_room_loc_sg"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokoji"
    segments := ["p", "o", "k", "o", "j", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "loc"), ("Number", "sg")] }

def room_ins_sg : Form :=
  { id := "stump2006_room_ins_sg"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokojem"
    segments := ["p", "o", "k", "o", "j", "e", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "ins"), ("Number", "sg")] }

def room_nom_pl : Form :=
  { id := "stump2006_room_nom_pl"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokoje"
    segments := ["p", "o", "k", "o", "j", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "nom"), ("Number", "pl")] }

def room_gen_pl : Form :=
  { id := "stump2006_room_gen_pl"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokojů"
    segments := ["p", "o", "k", "o", "j", "ů"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "gen"), ("Number", "pl")] }

def room_dat_pl : Form :=
  { id := "stump2006_room_dat_pl"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokojům"
    segments := ["p", "o", "k", "o", "j", "ů", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "dat"), ("Number", "pl")] }

def room_acc_pl : Form :=
  { id := "stump2006_room_acc_pl"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokoje"
    segments := ["p", "o", "k", "o", "j", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "acc"), ("Number", "pl")] }

def room_voc_pl : Form :=
  { id := "stump2006_room_voc_pl"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokoje"
    segments := ["p", "o", "k", "o", "j", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "voc"), ("Number", "pl")] }

def room_loc_pl : Form :=
  { id := "stump2006_room_loc_pl"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokojích"
    segments := ["p", "o", "k", "o", "j", "í", "ch"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "loc"), ("Number", "pl")] }

def room_ins_pl : Form :=
  { id := "stump2006_room_ins_pl"
    languageId := "czec1258"
    parameterId := "room"
    form := "pokoji"
    segments := ["p", "o", "k", "o", "j", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "POKOJ"), ("Case", "ins"), ("Number", "pl")] }

def spring_nom_sg : Form :=
  { id := "stump2006_spring_nom_sg"
    languageId := "czec1258"
    parameterId := "spring"
    form := "pramen"
    segments := ["p", "r", "a", "m", "e", "n"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "nom"), ("Number", "sg")] }

def spring_gen_sg : Form :=
  { id := "stump2006_spring_gen_sg"
    languageId := "czec1258"
    parameterId := "spring"
    form := "pramene"
    segments := ["p", "r", "a", "m", "e", "n", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "gen"), ("Number", "sg")] }

def spring_dat_sg : Form :=
  { id := "stump2006_spring_dat_sg"
    languageId := "czec1258"
    parameterId := "spring"
    form := "prameni"
    segments := ["p", "r", "a", "m", "e", "n", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "dat"), ("Number", "sg")] }

def spring_acc_sg : Form :=
  { id := "stump2006_spring_acc_sg"
    languageId := "czec1258"
    parameterId := "spring"
    form := "pramen"
    segments := ["p", "r", "a", "m", "e", "n"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "acc"), ("Number", "sg")] }

def spring_voc_sg : Form :=
  { id := "stump2006_spring_voc_sg"
    languageId := "czec1258"
    parameterId := "spring"
    form := "prameni"
    segments := ["p", "r", "a", "m", "e", "n", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "voc"), ("Number", "sg")] }

def spring_loc_sg : Form :=
  { id := "stump2006_spring_loc_sg"
    languageId := "czec1258"
    parameterId := "spring"
    form := "prameni"
    segments := ["p", "r", "a", "m", "e", "n", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "loc"), ("Number", "sg")] }

def spring_ins_sg : Form :=
  { id := "stump2006_spring_ins_sg"
    languageId := "czec1258"
    parameterId := "spring"
    form := "pramenem"
    segments := ["p", "r", "a", "m", "e", "n", "e", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "ins"), ("Number", "sg")] }

def spring_nom_pl : Form :=
  { id := "stump2006_spring_nom_pl"
    languageId := "czec1258"
    parameterId := "spring"
    form := "prameny"
    segments := ["p", "r", "a", "m", "e", "n", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "nom"), ("Number", "pl")] }

def spring_gen_pl : Form :=
  { id := "stump2006_spring_gen_pl"
    languageId := "czec1258"
    parameterId := "spring"
    form := "pramenů"
    segments := ["p", "r", "a", "m", "e", "n", "ů"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "gen"), ("Number", "pl")] }

def spring_dat_pl : Form :=
  { id := "stump2006_spring_dat_pl"
    languageId := "czec1258"
    parameterId := "spring"
    form := "pramenům"
    segments := ["p", "r", "a", "m", "e", "n", "ů", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "dat"), ("Number", "pl")] }

def spring_acc_pl : Form :=
  { id := "stump2006_spring_acc_pl"
    languageId := "czec1258"
    parameterId := "spring"
    form := "prameny"
    segments := ["p", "r", "a", "m", "e", "n", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "acc"), ("Number", "pl")] }

def spring_voc_pl : Form :=
  { id := "stump2006_spring_voc_pl"
    languageId := "czec1258"
    parameterId := "spring"
    form := "prameny"
    segments := ["p", "r", "a", "m", "e", "n", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "voc"), ("Number", "pl")] }

def spring_loc_pl : Form :=
  { id := "stump2006_spring_loc_pl"
    languageId := "czec1258"
    parameterId := "spring"
    form := "pramenech"
    segments := ["p", "r", "a", "m", "e", "n", "e", "ch"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "loc"), ("Number", "pl")] }

def spring_ins_pl : Form :=
  { id := "stump2006_spring_ins_pl"
    languageId := "czec1258"
    parameterId := "spring"
    form := "prameny"
    segments := ["p", "r", "a", "m", "e", "n", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "PRAMEN"), ("Case", "ins"), ("Number", "pl")] }

def bridge_nom_sg : Form :=
  { id := "stump2006_bridge_nom_sg"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "most"
    segments := ["m", "o", "s", "t"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "nom"), ("Number", "sg")] }

def bridge_gen_sg : Form :=
  { id := "stump2006_bridge_gen_sg"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "mostu"
    segments := ["m", "o", "s", "t", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "gen"), ("Number", "sg")] }

def bridge_dat_sg : Form :=
  { id := "stump2006_bridge_dat_sg"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "mostu"
    segments := ["m", "o", "s", "t", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "dat"), ("Number", "sg")] }

def bridge_acc_sg : Form :=
  { id := "stump2006_bridge_acc_sg"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "most"
    segments := ["m", "o", "s", "t"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "acc"), ("Number", "sg")] }

def bridge_voc_sg : Form :=
  { id := "stump2006_bridge_voc_sg"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "moste"
    segments := ["m", "o", "s", "t", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "voc"), ("Number", "sg")] }

def bridge_loc_sg : Form :=
  { id := "stump2006_bridge_loc_sg"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "mostě"
    segments := ["m", "o", "s", "t", "ě"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "loc"), ("Number", "sg")] }

def bridge_ins_sg : Form :=
  { id := "stump2006_bridge_ins_sg"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "mostem"
    segments := ["m", "o", "s", "t", "e", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "ins"), ("Number", "sg")] }

def bridge_nom_pl : Form :=
  { id := "stump2006_bridge_nom_pl"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "mosty"
    segments := ["m", "o", "s", "t", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "nom"), ("Number", "pl")] }

def bridge_gen_pl : Form :=
  { id := "stump2006_bridge_gen_pl"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "mostů"
    segments := ["m", "o", "s", "t", "ů"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "gen"), ("Number", "pl")] }

def bridge_dat_pl : Form :=
  { id := "stump2006_bridge_dat_pl"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "mostům"
    segments := ["m", "o", "s", "t", "ů", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "dat"), ("Number", "pl")] }

def bridge_acc_pl : Form :=
  { id := "stump2006_bridge_acc_pl"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "mosty"
    segments := ["m", "o", "s", "t", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "acc"), ("Number", "pl")] }

def bridge_voc_pl : Form :=
  { id := "stump2006_bridge_voc_pl"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "mosty"
    segments := ["m", "o", "s", "t", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "voc"), ("Number", "pl")] }

def bridge_loc_pl : Form :=
  { id := "stump2006_bridge_loc_pl"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "mostech"
    segments := ["m", "o", "s", "t", "e", "ch"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "loc"), ("Number", "pl")] }

def bridge_ins_pl : Form :=
  { id := "stump2006_bridge_ins_pl"
    languageId := "czec1258"
    parameterId := "bridge"
    form := "mosty"
    segments := ["m", "o", "s", "t", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ]
    columns := [("Lexeme", "MOST"), ("Case", "ins"), ("Number", "pl")] }

def woman_nom_sg : Form :=
  { id := "stump2006_woman_nom_sg"
    languageId := "czec1258"
    parameterId := "woman"
    form := "žena"
    segments := ["ž", "e", "n", "a"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "nom"), ("Number", "sg")] }

def woman_gen_sg : Form :=
  { id := "stump2006_woman_gen_sg"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženy"
    segments := ["ž", "e", "n", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "gen"), ("Number", "sg")] }

def woman_dat_sg : Form :=
  { id := "stump2006_woman_dat_sg"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženě"
    segments := ["ž", "e", "n", "ě"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "dat"), ("Number", "sg")] }

def woman_acc_sg : Form :=
  { id := "stump2006_woman_acc_sg"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženu"
    segments := ["ž", "e", "n", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "acc"), ("Number", "sg")] }

def woman_voc_sg : Form :=
  { id := "stump2006_woman_voc_sg"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženo"
    segments := ["ž", "e", "n", "o"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "voc"), ("Number", "sg")] }

def woman_loc_sg : Form :=
  { id := "stump2006_woman_loc_sg"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženě"
    segments := ["ž", "e", "n", "ě"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "loc"), ("Number", "sg")] }

def woman_ins_sg : Form :=
  { id := "stump2006_woman_ins_sg"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženou"
    segments := ["ž", "e", "n", "o", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "ins"), ("Number", "sg")] }

def woman_nom_pl : Form :=
  { id := "stump2006_woman_nom_pl"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženy"
    segments := ["ž", "e", "n", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "nom"), ("Number", "pl")] }

def woman_gen_pl : Form :=
  { id := "stump2006_woman_gen_pl"
    languageId := "czec1258"
    parameterId := "woman"
    form := "žen"
    segments := ["ž", "e", "n"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "gen"), ("Number", "pl")] }

def woman_dat_pl : Form :=
  { id := "stump2006_woman_dat_pl"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženám"
    segments := ["ž", "e", "n", "á", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "dat"), ("Number", "pl")] }

def woman_acc_pl : Form :=
  { id := "stump2006_woman_acc_pl"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženy"
    segments := ["ž", "e", "n", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "acc"), ("Number", "pl")] }

def woman_voc_pl : Form :=
  { id := "stump2006_woman_voc_pl"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženy"
    segments := ["ž", "e", "n", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "voc"), ("Number", "pl")] }

def woman_loc_pl : Form :=
  { id := "stump2006_woman_loc_pl"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženách"
    segments := ["ž", "e", "n", "á", "ch"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "loc"), ("Number", "pl")] }

def woman_ins_pl : Form :=
  { id := "stump2006_woman_ins_pl"
    languageId := "czec1258"
    parameterId := "woman"
    form := "ženami"
    segments := ["ž", "e", "n", "a", "m", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "ŽENA"), ("Case", "ins"), ("Number", "pl")] }

def president_nom_sg : Form :=
  { id := "stump2006_president_nom_sg"
    languageId := "czec1258"
    parameterId := "president"
    form := "předseda"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "a"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "nom"), ("Number", "sg")] }

def president_gen_sg : Form :=
  { id := "stump2006_president_gen_sg"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedy"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "gen"), ("Number", "sg")] }

def president_dat_sg : Form :=
  { id := "stump2006_president_dat_sg"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedovi"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o", "v", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "dat"), ("Number", "sg")] }

def president_acc_sg : Form :=
  { id := "stump2006_president_acc_sg"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedu"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "acc"), ("Number", "sg")] }

def president_voc_sg : Form :=
  { id := "stump2006_president_voc_sg"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedo"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "voc"), ("Number", "sg")] }

def president_loc_sg : Form :=
  { id := "stump2006_president_loc_sg"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedovi"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o", "v", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "loc"), ("Number", "sg")] }

def president_ins_sg : Form :=
  { id := "stump2006_president_ins_sg"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedou"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "ins"), ("Number", "sg")] }

def president_nom_pl : Form :=
  { id := "stump2006_president_nom_pl"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedové"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o", "v", "é"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "nom"), ("Number", "pl")] }

def president_gen_pl : Form :=
  { id := "stump2006_president_gen_pl"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedů"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "ů"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "gen"), ("Number", "pl")] }

def president_dat_pl : Form :=
  { id := "stump2006_president_dat_pl"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedům"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "ů", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "dat"), ("Number", "pl")] }

def president_acc_pl : Form :=
  { id := "stump2006_president_acc_pl"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedy"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "acc"), ("Number", "pl")] }

def president_voc_pl : Form :=
  { id := "stump2006_president_voc_pl"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedové"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o", "v", "é"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "voc"), ("Number", "pl")] }

def president_loc_pl : Form :=
  { id := "stump2006_president_loc_pl"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedech"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "e", "ch"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "loc"), ("Number", "pl")] }

def president_ins_pl : Form :=
  { id := "stump2006_president_ins_pl"
    languageId := "czec1258"
    parameterId := "president"
    form := "předsedy"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "PŘEDSEDA"), ("Case", "ins"), ("Number", "pl")] }

def philosopher_nom_sg : Form :=
  { id := "stump2006_philosopher_nom_sg"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosof"
    segments := ["f", "i", "l", "o", "s", "o", "f"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "nom"), ("Number", "sg")] }

def philosopher_gen_sg : Form :=
  { id := "stump2006_philosopher_gen_sg"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofa"
    segments := ["f", "i", "l", "o", "s", "o", "f", "a"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "gen"), ("Number", "sg")] }

def philosopher_dat_sg : Form :=
  { id := "stump2006_philosopher_dat_sg"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofovi"
    segments := ["f", "i", "l", "o", "s", "o", "f", "o", "v", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "dat"), ("Number", "sg")] }

def philosopher_acc_sg : Form :=
  { id := "stump2006_philosopher_acc_sg"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofa"
    segments := ["f", "i", "l", "o", "s", "o", "f", "a"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "acc"), ("Number", "sg")] }

def philosopher_voc_sg : Form :=
  { id := "stump2006_philosopher_voc_sg"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofe"
    segments := ["f", "i", "l", "o", "s", "o", "f", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "voc"), ("Number", "sg")] }

def philosopher_loc_sg : Form :=
  { id := "stump2006_philosopher_loc_sg"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofovi"
    segments := ["f", "i", "l", "o", "s", "o", "f", "o", "v", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "loc"), ("Number", "sg")] }

def philosopher_ins_sg : Form :=
  { id := "stump2006_philosopher_ins_sg"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofem"
    segments := ["f", "i", "l", "o", "s", "o", "f", "e", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "ins"), ("Number", "sg")] }

def philosopher_nom_pl : Form :=
  { id := "stump2006_philosopher_nom_pl"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofové"
    segments := ["f", "i", "l", "o", "s", "o", "f", "o", "v", "é"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "nom"), ("Number", "pl")] }

def philosopher_gen_pl : Form :=
  { id := "stump2006_philosopher_gen_pl"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofů"
    segments := ["f", "i", "l", "o", "s", "o", "f", "ů"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "gen"), ("Number", "pl")] }

def philosopher_dat_pl : Form :=
  { id := "stump2006_philosopher_dat_pl"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofům"
    segments := ["f", "i", "l", "o", "s", "o", "f", "ů", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "dat"), ("Number", "pl")] }

def philosopher_acc_pl : Form :=
  { id := "stump2006_philosopher_acc_pl"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofy"
    segments := ["f", "i", "l", "o", "s", "o", "f", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "acc"), ("Number", "pl")] }

def philosopher_voc_pl : Form :=
  { id := "stump2006_philosopher_voc_pl"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofové"
    segments := ["f", "i", "l", "o", "s", "o", "f", "o", "v", "é"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "voc"), ("Number", "pl")] }

def philosopher_loc_pl : Form :=
  { id := "stump2006_philosopher_loc_pl"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofech"
    segments := ["f", "i", "l", "o", "s", "o", "f", "e", "ch"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "loc"), ("Number", "pl")] }

def philosopher_ins_pl : Form :=
  { id := "stump2006_philosopher_ins_pl"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofy"
    segments := ["f", "i", "l", "o", "s", "o", "f", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Lexeme", "FILOSOF"), ("Case", "ins"), ("Number", "pl")] }

def servant_nom_sg : Form :=
  { id := "stump2006_servant_nom_sg"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluha"
    segments := ["s", "l", "u", "h", "a"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "nom"), ("Number", "sg")] }

def servant_gen_sg : Form :=
  { id := "stump2006_servant_gen_sg"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluhy"
    segments := ["s", "l", "u", "h", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "gen"), ("Number", "sg")] }

def servant_dat_sg : Form :=
  { id := "stump2006_servant_dat_sg"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluhovi"
    segments := ["s", "l", "u", "h", "o", "v", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "dat"), ("Number", "sg")] }

def servant_acc_sg : Form :=
  { id := "stump2006_servant_acc_sg"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluhu"
    segments := ["s", "l", "u", "h", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "acc"), ("Number", "sg")] }

def servant_voc_sg : Form :=
  { id := "stump2006_servant_voc_sg"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluho"
    segments := ["s", "l", "u", "h", "o"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "voc"), ("Number", "sg")] }

def servant_loc_sg : Form :=
  { id := "stump2006_servant_loc_sg"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluhovi"
    segments := ["s", "l", "u", "h", "o", "v", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "loc"), ("Number", "sg")] }

def servant_ins_sg : Form :=
  { id := "stump2006_servant_ins_sg"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluhou"
    segments := ["s", "l", "u", "h", "o", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "ins"), ("Number", "sg")] }

def servant_nom_pl : Form :=
  { id := "stump2006_servant_nom_pl"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluhové"
    segments := ["s", "l", "u", "h", "o", "v", "é"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "nom"), ("Number", "pl")] }

def servant_gen_pl : Form :=
  { id := "stump2006_servant_gen_pl"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluhů"
    segments := ["s", "l", "u", "h", "ů"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "gen"), ("Number", "pl")] }

def servant_dat_pl : Form :=
  { id := "stump2006_servant_dat_pl"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluhům"
    segments := ["s", "l", "u", "h", "ů", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "dat"), ("Number", "pl")] }

def servant_acc_pl : Form :=
  { id := "stump2006_servant_acc_pl"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluhy"
    segments := ["s", "l", "u", "h", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "acc"), ("Number", "pl")] }

def servant_voc_pl : Form :=
  { id := "stump2006_servant_voc_pl"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluhové"
    segments := ["s", "l", "u", "h", "o", "v", "é"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "voc"), ("Number", "pl")] }

def servant_loc_pl : Form :=
  { id := "stump2006_servant_loc_pl"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluzích"
    segments := ["s", "l", "u", "z", "í", "ch"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "loc"), ("Number", "pl")] }

def servant_ins_pl : Form :=
  { id := "stump2006_servant_ins_pl"
    languageId := "czec1258"
    parameterId := "servant"
    form := "sluhy"
    segments := ["s", "l", "u", "h", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Lexeme", "SLUHA"), ("Case", "ins"), ("Number", "pl")] }

def all : List Form := [room_nom_sg, room_gen_sg, room_dat_sg, room_acc_sg, room_voc_sg, room_loc_sg, room_ins_sg, room_nom_pl, room_gen_pl, room_dat_pl, room_acc_pl, room_voc_pl, room_loc_pl, room_ins_pl, spring_nom_sg, spring_gen_sg, spring_dat_sg, spring_acc_sg, spring_voc_sg, spring_loc_sg, spring_ins_sg, spring_nom_pl, spring_gen_pl, spring_dat_pl, spring_acc_pl, spring_voc_pl, spring_loc_pl, spring_ins_pl, bridge_nom_sg, bridge_gen_sg, bridge_dat_sg, bridge_acc_sg, bridge_voc_sg, bridge_loc_sg, bridge_ins_sg, bridge_nom_pl, bridge_gen_pl, bridge_dat_pl, bridge_acc_pl, bridge_voc_pl, bridge_loc_pl, bridge_ins_pl, woman_nom_sg, woman_gen_sg, woman_dat_sg, woman_acc_sg, woman_voc_sg, woman_loc_sg, woman_ins_sg, woman_nom_pl, woman_gen_pl, woman_dat_pl, woman_acc_pl, woman_voc_pl, woman_loc_pl, woman_ins_pl, president_nom_sg, president_gen_sg, president_dat_sg, president_acc_sg, president_voc_sg, president_loc_sg, president_ins_sg, president_nom_pl, president_gen_pl, president_dat_pl, president_acc_pl, president_voc_pl, president_loc_pl, president_ins_pl, philosopher_nom_sg, philosopher_gen_sg, philosopher_dat_sg, philosopher_acc_sg, philosopher_voc_sg, philosopher_loc_sg, philosopher_ins_sg, philosopher_nom_pl, philosopher_gen_pl, philosopher_dat_pl, philosopher_acc_pl, philosopher_voc_pl, philosopher_loc_pl, philosopher_ins_pl, servant_nom_sg, servant_gen_sg, servant_dat_sg, servant_acc_sg, servant_voc_sg, servant_loc_sg, servant_ins_sg, servant_nom_pl, servant_gen_pl, servant_dat_pl, servant_acc_pl, servant_voc_pl, servant_loc_pl, servant_ins_pl]

def parameters : List Parameter := [
  { id := "room", name := "room", description := "POKOJ" },
  { id := "spring", name := "spring", description := "PRAMEN" },
  { id := "bridge", name := "bridge", description := "MOST" },
  { id := "woman", name := "woman", description := "ŽENA" },
  { id := "president", name := "president", description := "PŘEDSEDA" },
  { id := "philosopher", name := "philosopher", description := "FILOSOF" },
  { id := "servant", name := "servant", description := "SLUHA" }
]

def relations : List FormRelation := []

end Stump2006.Forms
