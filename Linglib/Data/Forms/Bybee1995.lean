module

public import Linglib.Data.Forms.Schema

/-!
# `Bybee1995` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Bybee1995.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Bybee1995.Forms`.
-/

@[expose] public section

namespace Bybee1995.Forms

open Data.Forms

def strung : Form :=
  { id := "bybee1995_strung"
    languageId := "stan1293"
    parameterId := "string_past"
    form := "strung"
    segments := ["str", "ʌ", "ŋ"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def stung : Form :=
  { id := "bybee1995_stung"
    languageId := "stan1293"
    parameterId := "sting_past"
    form := "stung"
    segments := ["st", "ʌ", "ŋ"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def flung : Form :=
  { id := "bybee1995_flung"
    languageId := "stan1293"
    parameterId := "fling_past"
    form := "flung"
    segments := ["fl", "ʌ", "ŋ"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def hung : Form :=
  { id := "bybee1995_hung"
    languageId := "stan1293"
    parameterId := "hang_past"
    form := "hung"
    segments := ["h", "ʌ", "ŋ"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def strike : Form :=
  { id := "bybee1995_strike"
    languageId := "stan1293"
    parameterId := "strike"
    form := "strike"
    segments := ["str", "aɪ", "k"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def struck : Form :=
  { id := "bybee1995_struck"
    languageId := "stan1293"
    parameterId := "strike_past"
    form := "struck"
    segments := ["str", "ʌ", "k"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def sneak : Form :=
  { id := "bybee1995_sneak"
    languageId := "stan1293"
    parameterId := "sneak"
    form := "sneak"
    segments := ["sn", "i", "k"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def snuck : Form :=
  { id := "bybee1995_snuck"
    languageId := "stan1293"
    parameterId := "sneak_past"
    form := "snuck"
    segments := ["sn", "ʌ", "k"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def drag : Form :=
  { id := "bybee1995_drag"
    languageId := "stan1293"
    parameterId := "drag"
    form := "drag"
    segments := ["dr", "æ", "g"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def drug : Form :=
  { id := "bybee1995_drug"
    languageId := "stan1293"
    parameterId := "drag_past"
    form := "drug"
    segments := ["dr", "ʌ", "g"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def string : Form :=
  { id := "bybee1995_string"
    languageId := "stan1293"
    parameterId := "string"
    form := "string"
    segments := ["str", "ɪ", "ŋ"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def all : List Form := [strung, stung, flung, hung, strike, struck, sneak, snuck, drag, drug, string]

def relations : List FormRelation := [
  { id := "bybee1995_string_strung", form := string, target := strung, relation := "past", source := [
      ⟨"bybee-1995", "2"⟩
    ] },
  { id := "bybee1995_strike_struck", form := strike, target := struck, relation := "past", source := [
      ⟨"bybee-1995", "2"⟩
    ] },
  { id := "bybee1995_sneak_snuck", form := sneak, target := snuck, relation := "past", source := [
      ⟨"bybee-1995", "2"⟩
    ] },
  { id := "bybee1995_drag_drug", form := drag, target := drug, relation := "past", source := [
      ⟨"bybee-1995", "2"⟩
    ] }
]

end Bybee1995.Forms
