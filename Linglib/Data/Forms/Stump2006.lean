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
    columns := [("Case", "nom"), ("Number", "sg")] }

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
    columns := [("Case", "gen"), ("Number", "sg")] }

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
    columns := [("Case", "dat"), ("Number", "sg")] }

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
    columns := [("Case", "acc"), ("Number", "sg")] }

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
    columns := [("Case", "voc"), ("Number", "sg")] }

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
    columns := [("Case", "loc"), ("Number", "sg")] }

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
    columns := [("Case", "ins"), ("Number", "sg")] }

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
    columns := [("Case", "nom"), ("Number", "pl")] }

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
    columns := [("Case", "gen"), ("Number", "pl")] }

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
    columns := [("Case", "dat"), ("Number", "pl")] }

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
    columns := [("Case", "acc"), ("Number", "pl")] }

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
    columns := [("Case", "voc"), ("Number", "pl")] }

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
    columns := [("Case", "loc"), ("Number", "pl")] }

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
    columns := [("Case", "ins"), ("Number", "pl")] }

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
    columns := [("Case", "nom"), ("Number", "sg")] }

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
    columns := [("Case", "gen"), ("Number", "sg")] }

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
    columns := [("Case", "dat"), ("Number", "sg")] }

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
    columns := [("Case", "acc"), ("Number", "sg")] }

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
    columns := [("Case", "voc"), ("Number", "sg")] }

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
    columns := [("Case", "loc"), ("Number", "sg")] }

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
    columns := [("Case", "ins"), ("Number", "sg")] }

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
    columns := [("Case", "nom"), ("Number", "pl")] }

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
    columns := [("Case", "gen"), ("Number", "pl")] }

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
    columns := [("Case", "dat"), ("Number", "pl")] }

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
    columns := [("Case", "acc"), ("Number", "pl")] }

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
    columns := [("Case", "voc"), ("Number", "pl")] }

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
    columns := [("Case", "loc"), ("Number", "pl")] }

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
    columns := [("Case", "ins"), ("Number", "pl")] }

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
    columns := [("Case", "nom"), ("Number", "sg")] }

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
    columns := [("Case", "gen"), ("Number", "sg")] }

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
    columns := [("Case", "dat"), ("Number", "sg")] }

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
    columns := [("Case", "acc"), ("Number", "sg")] }

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
    columns := [("Case", "voc"), ("Number", "sg")] }

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
    columns := [("Case", "loc"), ("Number", "sg")] }

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
    columns := [("Case", "ins"), ("Number", "sg")] }

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
    columns := [("Case", "nom"), ("Number", "pl")] }

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
    columns := [("Case", "gen"), ("Number", "pl")] }

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
    columns := [("Case", "dat"), ("Number", "pl")] }

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
    columns := [("Case", "acc"), ("Number", "pl")] }

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
    columns := [("Case", "voc"), ("Number", "pl")] }

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
    columns := [("Case", "loc"), ("Number", "pl")] }

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
    columns := [("Case", "ins"), ("Number", "pl")] }

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
    columns := [("Case", "nom"), ("Number", "sg")] }

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
    columns := [("Case", "gen"), ("Number", "sg")] }

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
    columns := [("Case", "dat"), ("Number", "sg")] }

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
    columns := [("Case", "acc"), ("Number", "sg")] }

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
    columns := [("Case", "voc"), ("Number", "sg")] }

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
    columns := [("Case", "loc"), ("Number", "sg")] }

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
    columns := [("Case", "ins"), ("Number", "sg")] }

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
    columns := [("Case", "nom"), ("Number", "pl")] }

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
    columns := [("Case", "gen"), ("Number", "pl")] }

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
    columns := [("Case", "dat"), ("Number", "pl")] }

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
    columns := [("Case", "acc"), ("Number", "pl")] }

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
    columns := [("Case", "voc"), ("Number", "pl")] }

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
    columns := [("Case", "loc"), ("Number", "pl")] }

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
    columns := [("Case", "ins"), ("Number", "pl")] }

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
    columns := [("Case", "nom"), ("Number", "sg")] }

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
    columns := [("Case", "gen"), ("Number", "sg")] }

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
    columns := [("Case", "dat"), ("Number", "sg")] }

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
    columns := [("Case", "acc"), ("Number", "sg")] }

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
    columns := [("Case", "voc"), ("Number", "sg")] }

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
    columns := [("Case", "loc"), ("Number", "sg")] }

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
    columns := [("Case", "ins"), ("Number", "sg")] }

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
    columns := [("Case", "nom"), ("Number", "pl")] }

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
    columns := [("Case", "gen"), ("Number", "pl")] }

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
    columns := [("Case", "dat"), ("Number", "pl")] }

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
    columns := [("Case", "acc"), ("Number", "pl")] }

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
    columns := [("Case", "voc"), ("Number", "pl")] }

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
    columns := [("Case", "loc"), ("Number", "pl")] }

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
    columns := [("Case", "ins"), ("Number", "pl")] }

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
    columns := [("Case", "nom"), ("Number", "sg")] }

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
    columns := [("Case", "gen"), ("Number", "sg")] }

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
    columns := [("Case", "dat"), ("Number", "sg")] }

def philosopher_dat_sg_u : Form :=
  { id := "stump2006_philosopher_dat_sg_u"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofu"
    segments := ["f", "i", "l", "o", "s", "o", "f", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Case", "dat"), ("Number", "sg")] }

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
    columns := [("Case", "acc"), ("Number", "sg")] }

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
    columns := [("Case", "voc"), ("Number", "sg")] }

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
    columns := [("Case", "loc"), ("Number", "sg")] }

def philosopher_loc_sg_u : Form :=
  { id := "stump2006_philosopher_loc_sg_u"
    languageId := "czec1258"
    parameterId := "philosopher"
    form := "filosofu"
    segments := ["f", "i", "l", "o", "s", "o", "f", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ]
    columns := [("Case", "loc"), ("Number", "sg")] }

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
    columns := [("Case", "ins"), ("Number", "sg")] }

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
    columns := [("Case", "nom"), ("Number", "pl")] }

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
    columns := [("Case", "gen"), ("Number", "pl")] }

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
    columns := [("Case", "dat"), ("Number", "pl")] }

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
    columns := [("Case", "acc"), ("Number", "pl")] }

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
    columns := [("Case", "voc"), ("Number", "pl")] }

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
    columns := [("Case", "loc"), ("Number", "pl")] }

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
    columns := [("Case", "ins"), ("Number", "pl")] }

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
    columns := [("Case", "nom"), ("Number", "sg")] }

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
    columns := [("Case", "gen"), ("Number", "sg")] }

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
    columns := [("Case", "dat"), ("Number", "sg")] }

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
    columns := [("Case", "acc"), ("Number", "sg")] }

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
    columns := [("Case", "voc"), ("Number", "sg")] }

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
    columns := [("Case", "loc"), ("Number", "sg")] }

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
    columns := [("Case", "ins"), ("Number", "sg")] }

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
    columns := [("Case", "nom"), ("Number", "pl")] }

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
    columns := [("Case", "gen"), ("Number", "pl")] }

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
    columns := [("Case", "dat"), ("Number", "pl")] }

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
    columns := [("Case", "acc"), ("Number", "pl")] }

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
    columns := [("Case", "voc"), ("Number", "pl")] }

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
    columns := [("Case", "loc"), ("Number", "pl")] }

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
    columns := [("Case", "ins"), ("Number", "pl")] }

def philologist_nom_sg : Form :=
  { id := "stump2006_philologist_nom_sg"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filolog"
    segments := ["f", "i", "l", "o", "l", "o", "g"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "nom"), ("Number", "sg")] }

def philologist_gen_sg : Form :=
  { id := "stump2006_philologist_gen_sg"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologa"
    segments := ["f", "i", "l", "o", "l", "o", "g", "a"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "gen"), ("Number", "sg")] }

def philologist_dat_sg : Form :=
  { id := "stump2006_philologist_dat_sg"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologovi"
    segments := ["f", "i", "l", "o", "l", "o", "g", "o", "v", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "dat"), ("Number", "sg")] }

def philologist_dat_sg_u : Form :=
  { id := "stump2006_philologist_dat_sg_u"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologu"
    segments := ["f", "i", "l", "o", "l", "o", "g", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "dat"), ("Number", "sg")] }

def philologist_acc_sg : Form :=
  { id := "stump2006_philologist_acc_sg"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologa"
    segments := ["f", "i", "l", "o", "l", "o", "g", "a"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "acc"), ("Number", "sg")] }

def philologist_voc_sg : Form :=
  { id := "stump2006_philologist_voc_sg"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologu"
    segments := ["f", "i", "l", "o", "l", "o", "g", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "voc"), ("Number", "sg")] }

def philologist_loc_sg : Form :=
  { id := "stump2006_philologist_loc_sg"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologovi"
    segments := ["f", "i", "l", "o", "l", "o", "g", "o", "v", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "loc"), ("Number", "sg")] }

def philologist_loc_sg_u : Form :=
  { id := "stump2006_philologist_loc_sg_u"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologu"
    segments := ["f", "i", "l", "o", "l", "o", "g", "u"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "loc"), ("Number", "sg")] }

def philologist_ins_sg : Form :=
  { id := "stump2006_philologist_ins_sg"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologem"
    segments := ["f", "i", "l", "o", "l", "o", "g", "e", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "ins"), ("Number", "sg")] }

def philologist_nom_pl : Form :=
  { id := "stump2006_philologist_nom_pl"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologové"
    segments := ["f", "i", "l", "o", "l", "o", "g", "o", "v", "é"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "nom"), ("Number", "pl")] }

def philologist_gen_pl : Form :=
  { id := "stump2006_philologist_gen_pl"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologů"
    segments := ["f", "i", "l", "o", "l", "o", "g", "ů"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "gen"), ("Number", "pl")] }

def philologist_dat_pl : Form :=
  { id := "stump2006_philologist_dat_pl"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologům"
    segments := ["f", "i", "l", "o", "l", "o", "g", "ů", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "dat"), ("Number", "pl")] }

def philologist_acc_pl : Form :=
  { id := "stump2006_philologist_acc_pl"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filology"
    segments := ["f", "i", "l", "o", "l", "o", "g", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "acc"), ("Number", "pl")] }

def philologist_voc_pl : Form :=
  { id := "stump2006_philologist_voc_pl"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filologové"
    segments := ["f", "i", "l", "o", "l", "o", "g", "o", "v", "é"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "voc"), ("Number", "pl")] }

def philologist_loc_pl : Form :=
  { id := "stump2006_philologist_loc_pl"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filolozích"
    segments := ["f", "i", "l", "o", "l", "o", "z", "í", "ch"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "loc"), ("Number", "pl")] }

def philologist_ins_pl : Form :=
  { id := "stump2006_philologist_ins_pl"
    languageId := "czec1258"
    parameterId := "philologist"
    form := "filology"
    segments := ["f", "i", "l", "o", "l", "o", "g", "y"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "ins"), ("Number", "pl")] }

def man_nom_sg : Form :=
  { id := "stump2006_man_nom_sg"
    languageId := "czec1258"
    parameterId := "man"
    form := "muž"
    segments := ["m", "u", "ž"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "nom"), ("Number", "sg")] }

def man_gen_sg : Form :=
  { id := "stump2006_man_gen_sg"
    languageId := "czec1258"
    parameterId := "man"
    form := "muže"
    segments := ["m", "u", "ž", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "gen"), ("Number", "sg")] }

def man_dat_sg : Form :=
  { id := "stump2006_man_dat_sg"
    languageId := "czec1258"
    parameterId := "man"
    form := "mužovi"
    segments := ["m", "u", "ž", "o", "v", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "dat"), ("Number", "sg")] }

def man_dat_sg_i : Form :=
  { id := "stump2006_man_dat_sg_i"
    languageId := "czec1258"
    parameterId := "man"
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "dat"), ("Number", "sg")] }

def man_acc_sg : Form :=
  { id := "stump2006_man_acc_sg"
    languageId := "czec1258"
    parameterId := "man"
    form := "muže"
    segments := ["m", "u", "ž", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "acc"), ("Number", "sg")] }

def man_voc_sg : Form :=
  { id := "stump2006_man_voc_sg"
    languageId := "czec1258"
    parameterId := "man"
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "voc"), ("Number", "sg")] }

def man_loc_sg : Form :=
  { id := "stump2006_man_loc_sg"
    languageId := "czec1258"
    parameterId := "man"
    form := "mužovi"
    segments := ["m", "u", "ž", "o", "v", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "loc"), ("Number", "sg")] }

def man_loc_sg_i : Form :=
  { id := "stump2006_man_loc_sg_i"
    languageId := "czec1258"
    parameterId := "man"
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "loc"), ("Number", "sg")] }

def man_ins_sg : Form :=
  { id := "stump2006_man_ins_sg"
    languageId := "czec1258"
    parameterId := "man"
    form := "mužem"
    segments := ["m", "u", "ž", "e", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "ins"), ("Number", "sg")] }

def man_nom_pl : Form :=
  { id := "stump2006_man_nom_pl"
    languageId := "czec1258"
    parameterId := "man"
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "nom"), ("Number", "pl")] }

def man_nom_pl_ove : Form :=
  { id := "stump2006_man_nom_pl_ove"
    languageId := "czec1258"
    parameterId := "man"
    form := "mužové"
    segments := ["m", "u", "ž", "o", "v", "é"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "nom"), ("Number", "pl")] }

def man_gen_pl : Form :=
  { id := "stump2006_man_gen_pl"
    languageId := "czec1258"
    parameterId := "man"
    form := "mužů"
    segments := ["m", "u", "ž", "ů"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "gen"), ("Number", "pl")] }

def man_dat_pl : Form :=
  { id := "stump2006_man_dat_pl"
    languageId := "czec1258"
    parameterId := "man"
    form := "mužům"
    segments := ["m", "u", "ž", "ů", "m"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "dat"), ("Number", "pl")] }

def man_acc_pl : Form :=
  { id := "stump2006_man_acc_pl"
    languageId := "czec1258"
    parameterId := "man"
    form := "muže"
    segments := ["m", "u", "ž", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "acc"), ("Number", "pl")] }

def man_voc_pl : Form :=
  { id := "stump2006_man_voc_pl"
    languageId := "czec1258"
    parameterId := "man"
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "voc"), ("Number", "pl")] }

def man_voc_pl_ove : Form :=
  { id := "stump2006_man_voc_pl_ove"
    languageId := "czec1258"
    parameterId := "man"
    form := "mužové"
    segments := ["m", "u", "ž", "o", "v", "é"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "voc"), ("Number", "pl")] }

def man_loc_pl : Form :=
  { id := "stump2006_man_loc_pl"
    languageId := "czec1258"
    parameterId := "man"
    form := "mužích"
    segments := ["m", "u", "ž", "í", "ch"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "loc"), ("Number", "pl")] }

def man_ins_pl : Form :=
  { id := "stump2006_man_ins_pl"
    languageId := "czec1258"
    parameterId := "man"
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ]
    columns := [("Case", "ins"), ("Number", "pl")] }

def westerly_masc_nom_sg : Form :=
  { id := "stump2006_westerly_masc_nom_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyaṅ"
    segments := ["pratyaṅ"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "nom"), ("Number", "sg"), ("Grade", "strong")] }

def westerly_masc_voc_sg : Form :=
  { id := "stump2006_westerly_masc_voc_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyaṅ"
    segments := ["pratyaṅ"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "voc"), ("Number", "sg"), ("Grade", "strong")] }

def westerly_masc_acc_sg : Form :=
  { id := "stump2006_westerly_masc_acc_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyañcam"
    segments := ["pratyañc", "am"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "acc"), ("Number", "sg"), ("Grade", "strong")] }

def westerly_masc_ins_sg : Form :=
  { id := "stump2006_westerly_masc_ins_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcā"
    segments := ["pratīc", "ā"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "ins"), ("Number", "sg"), ("Grade", "weakest")] }

def westerly_masc_dat_sg : Form :=
  { id := "stump2006_westerly_masc_dat_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīce"
    segments := ["pratīc", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "dat"), ("Number", "sg"), ("Grade", "weakest")] }

def westerly_masc_abl_sg : Form :=
  { id := "stump2006_westerly_masc_abl_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcas"
    segments := ["pratīc", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "abl"), ("Number", "sg"), ("Grade", "weakest")] }

def westerly_masc_gen_sg : Form :=
  { id := "stump2006_westerly_masc_gen_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcas"
    segments := ["pratīc", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "gen"), ("Number", "sg"), ("Grade", "weakest")] }

def westerly_masc_loc_sg : Form :=
  { id := "stump2006_westerly_masc_loc_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīci"
    segments := ["pratīc", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "loc"), ("Number", "sg"), ("Grade", "weakest")] }

def westerly_masc_nom_du : Form :=
  { id := "stump2006_westerly_masc_nom_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyañcau"
    segments := ["pratyañc", "au"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "nom"), ("Number", "du"), ("Grade", "strong")] }

def westerly_masc_voc_du : Form :=
  { id := "stump2006_westerly_masc_voc_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyañcau"
    segments := ["pratyañc", "au"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "voc"), ("Number", "du"), ("Grade", "strong")] }

def westerly_masc_acc_du : Form :=
  { id := "stump2006_westerly_masc_acc_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyañcau"
    segments := ["pratyañc", "au"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "acc"), ("Number", "du"), ("Grade", "strong")] }

def westerly_masc_ins_du : Form :=
  { id := "stump2006_westerly_masc_ins_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "ins"), ("Number", "du"), ("Grade", "middle")] }

def westerly_masc_dat_du : Form :=
  { id := "stump2006_westerly_masc_dat_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "dat"), ("Number", "du"), ("Grade", "middle")] }

def westerly_masc_abl_du : Form :=
  { id := "stump2006_westerly_masc_abl_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "abl"), ("Number", "du"), ("Grade", "middle")] }

def westerly_masc_gen_du : Form :=
  { id := "stump2006_westerly_masc_gen_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcos"
    segments := ["pratīc", "os"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "gen"), ("Number", "du"), ("Grade", "weakest")] }

def westerly_masc_loc_du : Form :=
  { id := "stump2006_westerly_masc_loc_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcos"
    segments := ["pratīc", "os"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "loc"), ("Number", "du"), ("Grade", "weakest")] }

def westerly_masc_nom_pl : Form :=
  { id := "stump2006_westerly_masc_nom_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyañcas"
    segments := ["pratyañc", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "nom"), ("Number", "pl"), ("Grade", "strong")] }

def westerly_masc_voc_pl : Form :=
  { id := "stump2006_westerly_masc_voc_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyañcas"
    segments := ["pratyañc", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "voc"), ("Number", "pl"), ("Grade", "strong")] }

def westerly_masc_acc_pl : Form :=
  { id := "stump2006_westerly_masc_acc_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcas"
    segments := ["pratīc", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "acc"), ("Number", "pl"), ("Grade", "weakest")] }

def westerly_masc_ins_pl : Form :=
  { id := "stump2006_westerly_masc_ins_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhis"
    segments := ["pratyag", "bhis"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "ins"), ("Number", "pl"), ("Grade", "middle")] }

def westerly_masc_dat_pl : Form :=
  { id := "stump2006_westerly_masc_dat_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhyas"
    segments := ["pratyag", "bhyas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "dat"), ("Number", "pl"), ("Grade", "middle")] }

def westerly_masc_abl_pl : Form :=
  { id := "stump2006_westerly_masc_abl_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhyas"
    segments := ["pratyag", "bhyas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "abl"), ("Number", "pl"), ("Grade", "middle")] }

def westerly_masc_gen_pl : Form :=
  { id := "stump2006_westerly_masc_gen_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcām"
    segments := ["pratīc", "ām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "gen"), ("Number", "pl"), ("Grade", "weakest")] }

def westerly_masc_loc_pl : Form :=
  { id := "stump2006_westerly_masc_loc_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyakṣu"
    segments := ["pratyak", "ṣu"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "masc"), ("Case", "loc"), ("Number", "pl"), ("Grade", "middle")] }

def westerly_neut_nom_sg : Form :=
  { id := "stump2006_westerly_neut_nom_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyak"
    segments := ["pratyak"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "sg"), ("Grade", "middle")] }

def westerly_neut_voc_sg : Form :=
  { id := "stump2006_westerly_neut_voc_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyak"
    segments := ["pratyak"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "sg"), ("Grade", "middle")] }

def westerly_neut_acc_sg : Form :=
  { id := "stump2006_westerly_neut_acc_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyak"
    segments := ["pratyak"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "sg"), ("Grade", "middle")] }

def westerly_neut_ins_sg : Form :=
  { id := "stump2006_westerly_neut_ins_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcā"
    segments := ["pratīc", "ā"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "sg"), ("Grade", "weakest")] }

def westerly_neut_dat_sg : Form :=
  { id := "stump2006_westerly_neut_dat_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīce"
    segments := ["pratīc", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "sg"), ("Grade", "weakest")] }

def westerly_neut_abl_sg : Form :=
  { id := "stump2006_westerly_neut_abl_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcas"
    segments := ["pratīc", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "sg"), ("Grade", "weakest")] }

def westerly_neut_gen_sg : Form :=
  { id := "stump2006_westerly_neut_gen_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcas"
    segments := ["pratīc", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "sg"), ("Grade", "weakest")] }

def westerly_neut_loc_sg : Form :=
  { id := "stump2006_westerly_neut_loc_sg"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīci"
    segments := ["pratīc", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "sg"), ("Grade", "weakest")] }

def westerly_neut_nom_du : Form :=
  { id := "stump2006_westerly_neut_nom_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcī"
    segments := ["pratīc", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "du"), ("Grade", "weakest")] }

def westerly_neut_voc_du : Form :=
  { id := "stump2006_westerly_neut_voc_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcī"
    segments := ["pratīc", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "du"), ("Grade", "weakest")] }

def westerly_neut_acc_du : Form :=
  { id := "stump2006_westerly_neut_acc_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcī"
    segments := ["pratīc", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "du"), ("Grade", "weakest")] }

def westerly_neut_ins_du : Form :=
  { id := "stump2006_westerly_neut_ins_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "du"), ("Grade", "middle")] }

def westerly_neut_dat_du : Form :=
  { id := "stump2006_westerly_neut_dat_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "du"), ("Grade", "middle")] }

def westerly_neut_abl_du : Form :=
  { id := "stump2006_westerly_neut_abl_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "du"), ("Grade", "middle")] }

def westerly_neut_gen_du : Form :=
  { id := "stump2006_westerly_neut_gen_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcos"
    segments := ["pratīc", "os"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "du"), ("Grade", "weakest")] }

def westerly_neut_loc_du : Form :=
  { id := "stump2006_westerly_neut_loc_du"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcos"
    segments := ["pratīc", "os"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "du"), ("Grade", "weakest")] }

def westerly_neut_nom_pl : Form :=
  { id := "stump2006_westerly_neut_nom_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyañci"
    segments := ["pratyañc", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "pl"), ("Grade", "strong")] }

def westerly_neut_voc_pl : Form :=
  { id := "stump2006_westerly_neut_voc_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyañci"
    segments := ["pratyañc", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "pl"), ("Grade", "strong")] }

def westerly_neut_acc_pl : Form :=
  { id := "stump2006_westerly_neut_acc_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyañci"
    segments := ["pratyañc", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "pl"), ("Grade", "strong")] }

def westerly_neut_ins_pl : Form :=
  { id := "stump2006_westerly_neut_ins_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhis"
    segments := ["pratyag", "bhis"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "pl"), ("Grade", "middle")] }

def westerly_neut_dat_pl : Form :=
  { id := "stump2006_westerly_neut_dat_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhyas"
    segments := ["pratyag", "bhyas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "pl"), ("Grade", "middle")] }

def westerly_neut_abl_pl : Form :=
  { id := "stump2006_westerly_neut_abl_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyagbhyas"
    segments := ["pratyag", "bhyas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "pl"), ("Grade", "middle")] }

def westerly_neut_gen_pl : Form :=
  { id := "stump2006_westerly_neut_gen_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratīcām"
    segments := ["pratīc", "ām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "pl"), ("Grade", "weakest")] }

def westerly_neut_loc_pl : Form :=
  { id := "stump2006_westerly_neut_loc_pl"
    languageId := "sans1269"
    parameterId := "westerly"
    form := "pratyakṣu"
    segments := ["pratyak", "ṣu"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "pl"), ("Grade", "middle")] }

def name_nom_sg : Form :=
  { id := "stump2006_name_nom_sg"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāma"
    segments := ["nāma"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "sg")] }

def name_voc_sg : Form :=
  { id := "stump2006_name_voc_sg"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāma"
    segments := ["nāma"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "sg")] }

def name_acc_sg : Form :=
  { id := "stump2006_name_acc_sg"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāma"
    segments := ["nāma"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "sg")] }

def name_ins_sg : Form :=
  { id := "stump2006_name_ins_sg"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmnā"
    segments := ["nāmn", "ā"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "sg")] }

def name_dat_sg : Form :=
  { id := "stump2006_name_dat_sg"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmne"
    segments := ["nāmn", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "sg")] }

def name_abl_sg : Form :=
  { id := "stump2006_name_abl_sg"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmnas"
    segments := ["nāmn", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "sg")] }

def name_gen_sg : Form :=
  { id := "stump2006_name_gen_sg"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmnas"
    segments := ["nāmn", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "sg")] }

def name_loc_sg : Form :=
  { id := "stump2006_name_loc_sg"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmni"
    segments := ["nāmn", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "sg")] }

def name_nom_du : Form :=
  { id := "stump2006_name_nom_du"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmnī"
    segments := ["nāmn", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "du")] }

def name_voc_du : Form :=
  { id := "stump2006_name_voc_du"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmnī"
    segments := ["nāmn", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "du")] }

def name_acc_du : Form :=
  { id := "stump2006_name_acc_du"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmnī"
    segments := ["nāmn", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "du")] }

def name_ins_du : Form :=
  { id := "stump2006_name_ins_du"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmabhyām"
    segments := ["nāma", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "du")] }

def name_dat_du : Form :=
  { id := "stump2006_name_dat_du"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmabhyām"
    segments := ["nāma", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "du")] }

def name_abl_du : Form :=
  { id := "stump2006_name_abl_du"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmabhyām"
    segments := ["nāma", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "du")] }

def name_gen_du : Form :=
  { id := "stump2006_name_gen_du"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmnos"
    segments := ["nāmn", "os"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "du")] }

def name_loc_du : Form :=
  { id := "stump2006_name_loc_du"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmnos"
    segments := ["nāmn", "os"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "du")] }

def name_nom_pl : Form :=
  { id := "stump2006_name_nom_pl"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmāni"
    segments := ["nāmān", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "pl")] }

def name_voc_pl : Form :=
  { id := "stump2006_name_voc_pl"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmāni"
    segments := ["nāmān", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "pl")] }

def name_acc_pl : Form :=
  { id := "stump2006_name_acc_pl"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmāni"
    segments := ["nāmān", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "pl")] }

def name_ins_pl : Form :=
  { id := "stump2006_name_ins_pl"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmabhis"
    segments := ["nāma", "bhis"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "pl")] }

def name_dat_pl : Form :=
  { id := "stump2006_name_dat_pl"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmabhyas"
    segments := ["nāma", "bhyas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "pl")] }

def name_abl_pl : Form :=
  { id := "stump2006_name_abl_pl"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmabhyas"
    segments := ["nāma", "bhyas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "pl")] }

def name_gen_pl : Form :=
  { id := "stump2006_name_gen_pl"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmnām"
    segments := ["nāmn", "ām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "pl")] }

def name_loc_pl : Form :=
  { id := "stump2006_name_loc_pl"
    languageId := "sans1269"
    parameterId := "name"
    form := "nāmasu"
    segments := ["nāma", "su"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "pl")] }

def day_nom_sg : Form :=
  { id := "stump2006_day_nom_sg"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahas"
    segments := ["ahas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "sg"), ("Stem", "ahas")] }

def day_voc_sg : Form :=
  { id := "stump2006_day_voc_sg"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahas"
    segments := ["ahas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "sg"), ("Stem", "ahas")] }

def day_acc_sg : Form :=
  { id := "stump2006_day_acc_sg"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahas"
    segments := ["ahas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "sg"), ("Stem", "ahas")] }

def day_ins_sg : Form :=
  { id := "stump2006_day_ins_sg"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahnā"
    segments := ["ahn", "ā"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "sg"), ("Stem", "ahn")] }

def day_dat_sg : Form :=
  { id := "stump2006_day_dat_sg"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahne"
    segments := ["ahn", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "sg"), ("Stem", "ahn")] }

def day_abl_sg : Form :=
  { id := "stump2006_day_abl_sg"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahnas"
    segments := ["ahn", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "sg"), ("Stem", "ahn")] }

def day_gen_sg : Form :=
  { id := "stump2006_day_gen_sg"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahnas"
    segments := ["ahn", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "sg"), ("Stem", "ahn")] }

def day_loc_sg : Form :=
  { id := "stump2006_day_loc_sg"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahni"
    segments := ["ahn", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "sg"), ("Stem", "ahn")] }

def day_nom_du : Form :=
  { id := "stump2006_day_nom_du"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahnī"
    segments := ["ahn", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "du"), ("Stem", "ahn")] }

def day_voc_du : Form :=
  { id := "stump2006_day_voc_du"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahnī"
    segments := ["ahn", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "du"), ("Stem", "ahn")] }

def day_acc_du : Form :=
  { id := "stump2006_day_acc_du"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahnī"
    segments := ["ahn", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "du"), ("Stem", "ahn")] }

def day_ins_du : Form :=
  { id := "stump2006_day_ins_du"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahobhyām"
    segments := ["aho", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "du"), ("Stem", "ahas")] }

def day_dat_du : Form :=
  { id := "stump2006_day_dat_du"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahobhyām"
    segments := ["aho", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "du"), ("Stem", "ahas")] }

def day_abl_du : Form :=
  { id := "stump2006_day_abl_du"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahobhyām"
    segments := ["aho", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "du"), ("Stem", "ahas")] }

def day_gen_du : Form :=
  { id := "stump2006_day_gen_du"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahnos"
    segments := ["ahn", "os"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "du"), ("Stem", "ahn")] }

def day_loc_du : Form :=
  { id := "stump2006_day_loc_du"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahnos"
    segments := ["ahn", "os"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "du"), ("Stem", "ahn")] }

def day_nom_pl : Form :=
  { id := "stump2006_day_nom_pl"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahāni"
    segments := ["ahān", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "pl"), ("Stem", "ahan")] }

def day_voc_pl : Form :=
  { id := "stump2006_day_voc_pl"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahāni"
    segments := ["ahān", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "pl"), ("Stem", "ahan")] }

def day_acc_pl : Form :=
  { id := "stump2006_day_acc_pl"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahāni"
    segments := ["ahān", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "pl"), ("Stem", "ahan")] }

def day_ins_pl : Form :=
  { id := "stump2006_day_ins_pl"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahobhis"
    segments := ["aho", "bhis"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "pl"), ("Stem", "ahas")] }

def day_dat_pl : Form :=
  { id := "stump2006_day_dat_pl"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahobhyas"
    segments := ["aho", "bhyas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "pl"), ("Stem", "ahas")] }

def day_abl_pl : Form :=
  { id := "stump2006_day_abl_pl"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahobhyas"
    segments := ["aho", "bhyas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "pl"), ("Stem", "ahas")] }

def day_gen_pl : Form :=
  { id := "stump2006_day_gen_pl"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahnām"
    segments := ["ahn", "ām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "pl"), ("Stem", "ahn")] }

def day_loc_pl : Form :=
  { id := "stump2006_day_loc_pl"
    languageId := "sans1269"
    parameterId := "day"
    form := "ahaḥsu"
    segments := ["ahaḥ", "su"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "pl"), ("Stem", "ahas")] }

def mind_nom_sg : Form :=
  { id := "stump2006_mind_nom_sg"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manas"
    segments := ["manas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "sg")] }

def mind_voc_sg : Form :=
  { id := "stump2006_mind_voc_sg"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manas"
    segments := ["manas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "sg")] }

def mind_acc_sg : Form :=
  { id := "stump2006_mind_acc_sg"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manas"
    segments := ["manas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "sg")] }

def mind_ins_sg : Form :=
  { id := "stump2006_mind_ins_sg"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manasā"
    segments := ["manas", "ā"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "sg")] }

def mind_dat_sg : Form :=
  { id := "stump2006_mind_dat_sg"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manase"
    segments := ["manas", "e"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "sg")] }

def mind_abl_sg : Form :=
  { id := "stump2006_mind_abl_sg"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manasas"
    segments := ["manas", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "sg")] }

def mind_gen_sg : Form :=
  { id := "stump2006_mind_gen_sg"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manasas"
    segments := ["manas", "as"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "sg")] }

def mind_loc_sg : Form :=
  { id := "stump2006_mind_loc_sg"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manasi"
    segments := ["manas", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "sg")] }

def mind_nom_du : Form :=
  { id := "stump2006_mind_nom_du"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manasī"
    segments := ["manas", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "du")] }

def mind_voc_du : Form :=
  { id := "stump2006_mind_voc_du"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manasī"
    segments := ["manas", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "du")] }

def mind_acc_du : Form :=
  { id := "stump2006_mind_acc_du"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manasī"
    segments := ["manas", "ī"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "du")] }

def mind_ins_du : Form :=
  { id := "stump2006_mind_ins_du"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manobhyām"
    segments := ["mano", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "du")] }

def mind_dat_du : Form :=
  { id := "stump2006_mind_dat_du"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manobhyām"
    segments := ["mano", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "du")] }

def mind_abl_du : Form :=
  { id := "stump2006_mind_abl_du"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manobhyām"
    segments := ["mano", "bhyām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "du")] }

def mind_gen_du : Form :=
  { id := "stump2006_mind_gen_du"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manasos"
    segments := ["manas", "os"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "du")] }

def mind_loc_du : Form :=
  { id := "stump2006_mind_loc_du"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manasos"
    segments := ["manas", "os"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "du")] }

def mind_nom_pl : Form :=
  { id := "stump2006_mind_nom_pl"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manāṃsi"
    segments := ["manāṃs", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "nom"), ("Number", "pl")] }

def mind_voc_pl : Form :=
  { id := "stump2006_mind_voc_pl"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manāṃsi"
    segments := ["manāṃs", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "voc"), ("Number", "pl")] }

def mind_acc_pl : Form :=
  { id := "stump2006_mind_acc_pl"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manāṃsi"
    segments := ["manāṃs", "i"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "acc"), ("Number", "pl")] }

def mind_ins_pl : Form :=
  { id := "stump2006_mind_ins_pl"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manobhis"
    segments := ["mano", "bhis"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "ins"), ("Number", "pl")] }

def mind_dat_pl : Form :=
  { id := "stump2006_mind_dat_pl"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manobhyas"
    segments := ["mano", "bhyas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "dat"), ("Number", "pl")] }

def mind_abl_pl : Form :=
  { id := "stump2006_mind_abl_pl"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manobhyas"
    segments := ["mano", "bhyas"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "abl"), ("Number", "pl")] }

def mind_gen_pl : Form :=
  { id := "stump2006_mind_gen_pl"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manasām"
    segments := ["manas", "ām"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "gen"), ("Number", "pl")] }

def mind_loc_pl : Form :=
  { id := "stump2006_mind_loc_pl"
    languageId := "sans1269"
    parameterId := "mind"
    form := "manaḥsu"
    segments := ["manaḥ", "su"]
    comment := ""
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ]
    columns := [("Gender", "neut"), ("Case", "loc"), ("Number", "pl")] }

def all : List Form := [room_nom_sg, room_gen_sg, room_dat_sg, room_acc_sg, room_voc_sg, room_loc_sg, room_ins_sg, room_nom_pl, room_gen_pl, room_dat_pl, room_acc_pl, room_voc_pl, room_loc_pl, room_ins_pl, spring_nom_sg, spring_gen_sg, spring_dat_sg, spring_acc_sg, spring_voc_sg, spring_loc_sg, spring_ins_sg, spring_nom_pl, spring_gen_pl, spring_dat_pl, spring_acc_pl, spring_voc_pl, spring_loc_pl, spring_ins_pl, bridge_nom_sg, bridge_gen_sg, bridge_dat_sg, bridge_acc_sg, bridge_voc_sg, bridge_loc_sg, bridge_ins_sg, bridge_nom_pl, bridge_gen_pl, bridge_dat_pl, bridge_acc_pl, bridge_voc_pl, bridge_loc_pl, bridge_ins_pl, woman_nom_sg, woman_gen_sg, woman_dat_sg, woman_acc_sg, woman_voc_sg, woman_loc_sg, woman_ins_sg, woman_nom_pl, woman_gen_pl, woman_dat_pl, woman_acc_pl, woman_voc_pl, woman_loc_pl, woman_ins_pl, president_nom_sg, president_gen_sg, president_dat_sg, president_acc_sg, president_voc_sg, president_loc_sg, president_ins_sg, president_nom_pl, president_gen_pl, president_dat_pl, president_acc_pl, president_voc_pl, president_loc_pl, president_ins_pl, philosopher_nom_sg, philosopher_gen_sg, philosopher_dat_sg, philosopher_dat_sg_u, philosopher_acc_sg, philosopher_voc_sg, philosopher_loc_sg, philosopher_loc_sg_u, philosopher_ins_sg, philosopher_nom_pl, philosopher_gen_pl, philosopher_dat_pl, philosopher_acc_pl, philosopher_voc_pl, philosopher_loc_pl, philosopher_ins_pl, servant_nom_sg, servant_gen_sg, servant_dat_sg, servant_acc_sg, servant_voc_sg, servant_loc_sg, servant_ins_sg, servant_nom_pl, servant_gen_pl, servant_dat_pl, servant_acc_pl, servant_voc_pl, servant_loc_pl, servant_ins_pl, philologist_nom_sg, philologist_gen_sg, philologist_dat_sg, philologist_dat_sg_u, philologist_acc_sg, philologist_voc_sg, philologist_loc_sg, philologist_loc_sg_u, philologist_ins_sg, philologist_nom_pl, philologist_gen_pl, philologist_dat_pl, philologist_acc_pl, philologist_voc_pl, philologist_loc_pl, philologist_ins_pl, man_nom_sg, man_gen_sg, man_dat_sg, man_dat_sg_i, man_acc_sg, man_voc_sg, man_loc_sg, man_loc_sg_i, man_ins_sg, man_nom_pl, man_nom_pl_ove, man_gen_pl, man_dat_pl, man_acc_pl, man_voc_pl, man_voc_pl_ove, man_loc_pl, man_ins_pl, westerly_masc_nom_sg, westerly_masc_voc_sg, westerly_masc_acc_sg, westerly_masc_ins_sg, westerly_masc_dat_sg, westerly_masc_abl_sg, westerly_masc_gen_sg, westerly_masc_loc_sg, westerly_masc_nom_du, westerly_masc_voc_du, westerly_masc_acc_du, westerly_masc_ins_du, westerly_masc_dat_du, westerly_masc_abl_du, westerly_masc_gen_du, westerly_masc_loc_du, westerly_masc_nom_pl, westerly_masc_voc_pl, westerly_masc_acc_pl, westerly_masc_ins_pl, westerly_masc_dat_pl, westerly_masc_abl_pl, westerly_masc_gen_pl, westerly_masc_loc_pl, westerly_neut_nom_sg, westerly_neut_voc_sg, westerly_neut_acc_sg, westerly_neut_ins_sg, westerly_neut_dat_sg, westerly_neut_abl_sg, westerly_neut_gen_sg, westerly_neut_loc_sg, westerly_neut_nom_du, westerly_neut_voc_du, westerly_neut_acc_du, westerly_neut_ins_du, westerly_neut_dat_du, westerly_neut_abl_du, westerly_neut_gen_du, westerly_neut_loc_du, westerly_neut_nom_pl, westerly_neut_voc_pl, westerly_neut_acc_pl, westerly_neut_ins_pl, westerly_neut_dat_pl, westerly_neut_abl_pl, westerly_neut_gen_pl, westerly_neut_loc_pl, name_nom_sg, name_voc_sg, name_acc_sg, name_ins_sg, name_dat_sg, name_abl_sg, name_gen_sg, name_loc_sg, name_nom_du, name_voc_du, name_acc_du, name_ins_du, name_dat_du, name_abl_du, name_gen_du, name_loc_du, name_nom_pl, name_voc_pl, name_acc_pl, name_ins_pl, name_dat_pl, name_abl_pl, name_gen_pl, name_loc_pl, day_nom_sg, day_voc_sg, day_acc_sg, day_ins_sg, day_dat_sg, day_abl_sg, day_gen_sg, day_loc_sg, day_nom_du, day_voc_du, day_acc_du, day_ins_du, day_dat_du, day_abl_du, day_gen_du, day_loc_du, day_nom_pl, day_voc_pl, day_acc_pl, day_ins_pl, day_dat_pl, day_abl_pl, day_gen_pl, day_loc_pl, mind_nom_sg, mind_voc_sg, mind_acc_sg, mind_ins_sg, mind_dat_sg, mind_abl_sg, mind_gen_sg, mind_loc_sg, mind_nom_du, mind_voc_du, mind_acc_du, mind_ins_du, mind_dat_du, mind_abl_du, mind_gen_du, mind_loc_du, mind_nom_pl, mind_voc_pl, mind_acc_pl, mind_ins_pl, mind_dat_pl, mind_abl_pl, mind_gen_pl, mind_loc_pl]

def parameters : List Parameter := [
  { id := "room", name := "room", description := "POKOJ" },
  { id := "spring", name := "spring", description := "PRAMEN" },
  { id := "bridge", name := "bridge", description := "MOST" },
  { id := "woman", name := "woman", description := "ŽENA" },
  { id := "president", name := "president", description := "PŘEDSEDA" },
  { id := "philosopher", name := "philosopher", description := "FILOSOF" },
  { id := "servant", name := "servant", description := "SLUHA" },
  { id := "philologist", name := "philologist", description := "FILOLOG" },
  { id := "man", name := "man", description := "MUŽ" },
  { id := "westerly", name := "westerly", description := "PRATYAÑC" },
  { id := "name", name := "name", description := "NĀMAN" },
  { id := "day", name := "day", description := "AHAN" },
  { id := "mind", name := "mind", description := "MANAS" }
]

def relations : List FormRelation := []

end Stump2006.Forms
