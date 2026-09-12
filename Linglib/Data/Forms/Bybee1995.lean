import Linglib.Data.Forms.Schema

/-!
# `Bybee1995` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Bybee1995.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Bybee1995.Forms`.
-/

namespace Bybee1995.Forms

open Data.Forms

def strung : Form :=
  { id := "bybee1995_strung"
    languageId := "stan1293"
    parameterId := "string_past"
    form := "strung"
    segments := ["str", "ʌ", "ŋ"]
    comment := "central member of the product-oriented class"
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def stung : Form :=
  { id := "bybee1995_stung"
    languageId := "stan1293"
    parameterId := "sting_past"
    form := "stung"
    segments := ["st", "ʌ", "ŋ"]
    comment := "member of the product-oriented class"
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def flung : Form :=
  { id := "bybee1995_flung"
    languageId := "stan1293"
    parameterId := "fling_past"
    form := "flung"
    segments := ["fl", "ʌ", "ŋ"]
    comment := "member of the product-oriented class"
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def hung : Form :=
  { id := "bybee1995_hung"
    languageId := "stan1293"
    parameterId := "hang_past"
    form := "hung"
    segments := ["h", "ʌ", "ŋ"]
    comment := "member of the product-oriented class"
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def strike : Form :=
  { id := "bybee1995_strike"
    languageId := "stan1293"
    parameterId := "strike"
    form := "strike"
    segments := ["str", "aɪ", "k"]
    comment := "base of a dialectal new member; its vowel is not /ɪ/"
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def struck : Form :=
  { id := "bybee1995_struck"
    languageId := "stan1293"
    parameterId := "strike_past"
    form := "struck"
    segments := ["str", "ʌ", "k"]
    comment := "dialectal new member of the class"
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def sneak : Form :=
  { id := "bybee1995_sneak"
    languageId := "stan1293"
    parameterId := "sneak"
    form := "sneak"
    segments := ["sn", "i", "k"]
    comment := "base of a dialectal new member; its vowel is not /ɪ/"
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def snuck : Form :=
  { id := "bybee1995_snuck"
    languageId := "stan1293"
    parameterId := "sneak_past"
    form := "snuck"
    segments := ["sn", "ʌ", "k"]
    comment := "dialectal new member of the class"
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def drag : Form :=
  { id := "bybee1995_drag"
    languageId := "stan1293"
    parameterId := "drag"
    form := "drag"
    segments := ["dr", "æ", "g"]
    comment := "base of a dialectal new member; its vowel is not /ɪ/"
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def drug : Form :=
  { id := "bybee1995_drug"
    languageId := "stan1293"
    parameterId := "drag_past"
    form := "drug"
    segments := ["dr", "ʌ", "g"]
    comment := "dialectal new member of the class"
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def string : Form :=
  { id := "bybee1995_string"
    languageId := "stan1293"
    parameterId := "string"
    form := "string"
    segments := ["str", "ɪ", "ŋ"]
    comment := "base of strung"
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def all : List Form := [strung, stung, flung, hung, strike, struck, sneak, snuck, drag, drug, string]

def parameters : List Parameter := [
  { id := "string_past", name := "string (past)", description := "" },
  { id := "sting_past", name := "sting (past)", description := "" },
  { id := "fling_past", name := "fling (past)", description := "" },
  { id := "hang_past", name := "hang (past)", description := "" },
  { id := "strike", name := "strike", description := "" },
  { id := "strike_past", name := "strike (past)", description := "" },
  { id := "sneak", name := "sneak", description := "" },
  { id := "sneak_past", name := "sneak (past)", description := "" },
  { id := "drag", name := "drag", description := "" },
  { id := "drag_past", name := "drag (past)", description := "" },
  { id := "string", name := "string", description := "" }
]

def relations : List FormRelation := [
  { id := "bybee1995_string_strung", formId := "bybee1995_string", targetId := "bybee1995_strung", relation := "past", source := [
      ⟨"bybee-1995", "2"⟩
    ] },
  { id := "bybee1995_strike_struck", formId := "bybee1995_strike", targetId := "bybee1995_struck", relation := "past", source := [
      ⟨"bybee-1995", "2"⟩
    ] },
  { id := "bybee1995_sneak_snuck", formId := "bybee1995_sneak", targetId := "bybee1995_snuck", relation := "past", source := [
      ⟨"bybee-1995", "2"⟩
    ] },
  { id := "bybee1995_drag_drug", formId := "bybee1995_drag", targetId := "bybee1995_drug", relation := "past", source := [
      ⟨"bybee-1995", "2"⟩
    ] }
]

end Bybee1995.Forms
