module

public import Linglib.Data.Forms.Schema

/-!
# `HeinzLai2013` — CLDF form data

Auto-generated from `Linglib/Data/Forms/HeinzLai2013.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace HeinzLai2013.Forms`.
-/

@[expose] public section

namespace HeinzLai2013.Forms

open Data.Forms

def ipin : Form :=
  { id := "heinzlai2013_ipin"
    languageId := "nucl1301"
    parameterId := "rope_gen"
    form := "ipin"
    segments := ["i", "p", "i", "n"]
    comment := "Table 1 cites Nevins (2010: 32)."
    source := [
      ⟨"heinz-lai-2013", "Table 1a"⟩,
      ⟨"heinz-lai-2013", "Table 2a"⟩
    ]
    columns := [("Underlying", "/ip-un/")] }

def elin : Form :=
  { id := "heinzlai2013_elin"
    languageId := "nucl1301"
    parameterId := "hand_gen"
    form := "elin"
    segments := ["e", "l", "i", "n"]
    comment := "Table 1 prints the gloss as 'and'. Table 1 cites Nevins (2010: 32)."
    source := [
      ⟨"heinz-lai-2013", "Table 1b"⟩,
      ⟨"heinz-lai-2013", "Table 2a"⟩
    ]
    columns := [("Underlying", "/el-un/")] }

def sonun : Form :=
  { id := "heinzlai2013_sonun"
    languageId := "nucl1301"
    parameterId := "end_gen"
    form := "sonun"
    segments := ["s", "o", "n", "u", "n"]
    comment := "Table 1 cites Nevins (2010: 32)."
    source := [
      ⟨"heinz-lai-2013", "Table 1c"⟩,
      ⟨"heinz-lai-2013", "Table 2a"⟩
    ]
    columns := [("Underlying", "/son-un/")] }

def pulun : Form :=
  { id := "heinzlai2013_pulun"
    languageId := "nucl1301"
    parameterId := "stamp_gen"
    form := "pulun"
    segments := ["p", "u", "l", "u", "n"]
    comment := "Table 1 cites Nevins (2010: 32)."
    source := [
      ⟨"heinz-lai-2013", "Table 1d"⟩,
      ⟨"heinz-lai-2013", "Table 2a"⟩
    ]
    columns := [("Underlying", "/pul-un/")] }

def all : List Form := [ipin, elin, sonun, pulun]

def parameters : List Parameter := [
  { id := "rope_gen", name := "rope-GEN", description := "" },
  { id := "hand_gen", name := "hand-GEN", description := "" },
  { id := "end_gen", name := "end-GEN", description := "" },
  { id := "stamp_gen", name := "stamp-GEN", description := "" }
]

def relations : List FormRelation := []

end HeinzLai2013.Forms
