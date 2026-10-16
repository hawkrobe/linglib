module

public import Linglib.Data.Forms.Schema

/-!
# `Vago2017` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Vago2017.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Vago2017.Forms`.
-/

@[expose] public section

namespace Vago2017.Forms

open Data.Forms

def hordonk : Form :=
  { id := "vago2017_hordonk"
    languageId := "hung1274"
    parameterId := "our_barrel"
    form := "hordónk"
    segments := ["h", "o", "r", "d", "ó", "n", "k"]
    source := [
      ⟨"vago-2017", "Table 1"⟩
    ]
    columns := [("Left", "hordó"), ("LeftKind", "root"), ("Right", "unk"), ("RightKind", "suffix"), ("Deleted", "second"), ("Hierarchy", "regular")] }

def erdesz : Form :=
  { id := "vago2017_erdesz"
    languageId := "hung1274"
    parameterId := "forester"
    form := "erdész"
    segments := ["e", "r", "d", "é", "sz"]
    source := [
      ⟨"vago-2017", "(7a), Table 2"⟩
    ]
    columns := [("Left", "erdő"), ("LeftKind", "root"), ("Right", "ész"), ("RightKind", "suffix"), ("Deleted", "first"), ("Hierarchy", "v1Deletion")] }

def eszperantoul : Form :=
  { id := "vago2017_eszperantoul"
    languageId := "hung1274"
    parameterId := "in_esperanto"
    form := "eszperantóul"
    segments := ["e", "sz", "p", "e", "r", "a", "n", "t", "ó", "u", "l"]
    source := [
      ⟨"vago-2017", "Table 3"⟩
    ]
    columns := [("Left", "eszperantó"), ("LeftKind", "root"), ("Right", "ul"), ("RightKind", "suffix"), ("Deleted", "none"), ("Hierarchy", "noDeletion")] }

def tanulnunk : Form :=
  { id := "vago2017_tanulnunk"
    languageId := "hung1274"
    parameterId := "we_have_to_study"
    form := "tanulnunk"
    segments := ["t", "a", "n", "u", "l", "n", "u", "n", "k"]
    source := [
      ⟨"vago-2017", "(20c), Table 4"⟩
    ]
    columns := [("Before", "tanul"), ("BeforeKind", "root"), ("Left", "ni"), ("LeftKind", "suffix"), ("Right", "unk"), ("RightKind", "suffix"), ("Deleted", "first"), ("Hierarchy", "v1Deletion")] }

def hoznank : Form :=
  { id := "vago2017_hoznank"
    languageId := "hung1274"
    parameterId := "we_would_bring"
    form := "hoznánk"
    segments := ["h", "o", "z", "n", "á", "n", "k"]
    source := [
      ⟨"vago-2017", "(17), (21a)"⟩
    ]
    columns := [("Before", "hoz"), ("BeforeKind", "root"), ("Left", "ná"), ("LeftKind", "suffix"), ("Right", "unk"), ("RightKind", "suffix"), ("Deleted", "second"), ("Hierarchy", "regular")] }

def kapujan : Form :=
  { id := "vago2017_kapujan"
    languageId := "hung1274"
    parameterId := "on_his_gate"
    form := "kapuján"
    segments := ["k", "a", "p", "u", "j", "á", "n"]
    source := [
      ⟨"vago-2017", "(18a), (21b)"⟩
    ]
    columns := [("Before", "kapu"), ("BeforeKind", "root"), ("Left", "já"), ("LeftKind", "suffix"), ("Right", "on"), ("RightKind", "suffix"), ("Deleted", "second"), ("Hierarchy", "regular")] }

def kapuink : Form :=
  { id := "vago2017_kapuink"
    languageId := "hung1274"
    parameterId := "our_gates"
    form := "kapuink"
    segments := ["k", "a", "p", "u", "i", "n", "k"]
    source := [
      ⟨"vago-2017", "(18b), (23a)"⟩
    ]
    columns := [("Before", "kapu"), ("BeforeKind", "root"), ("Left", "i"), ("LeftKind", "suffix"), ("Right", "unk"), ("RightKind", "suffix"), ("Deleted", "second"), ("Hierarchy", "regular")] }

def nyomozonk : Form :=
  { id := "vago2017_nyomozonk"
    languageId := "hung1274"
    parameterId := "our_detective"
    form := "nyomozónk"
    segments := ["ny", "o", "m", "o", "z", "ó", "n", "k"]
    source := [
      ⟨"vago-2017", "(19), (23b)"⟩
    ]
    columns := [("Before", "nyomoz"), ("BeforeKind", "root"), ("Left", "ó"), ("LeftKind", "suffix"), ("Right", "unk"), ("RightKind", "suffix"), ("Deleted", "second"), ("Hierarchy", "regular")] }

def all : List Form := [hordonk, erdesz, eszperantoul, tanulnunk, hoznank, kapujan, kapuink, nyomozonk]

def relations : List FormRelation := []

end Vago2017.Forms
