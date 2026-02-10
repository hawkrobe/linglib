import Linglib.Fragments.English.FunctionWords

/-!
# English Auxiliary Diagnostics: NICE Properties (Huddleston 1976)

NICE = Negation, Inversion, Code (VP ellipsis), Emphasis.
These four properties distinguish true auxiliaries from main verbs in English.
Full auxiliaries exhibit all four; semi-auxiliaries exhibit a proper subset.

## NICE Tests

| Property | Test | Example |
|----------|------|---------|
| Negation | Can negate with *not* | *He can not go* |
| Inversion | Subject-aux inversion in questions | *Can he go?* |
| Code | VP ellipsis (stranding) | *He can and she can too* |
| Emphasis | Emphatic stress for verum focus | *He CAN go* |

## References

- Huddleston, R. (1976). Some theoretical issues in the description of the
  English verb. *Lingua* 40:331-383.
- Palmer, F. R. (2001). Mood and Modality. 2nd ed. CUP.
-/

namespace Phenomena.AuxiliaryVerbs.Diagnostics

open Fragments.English.FunctionWords (AuxType)

/-! ## Types -/

/-- The four NICE properties. -/
inductive NICEProperty where
  | negation   -- direct negation with *not*
  | inversion  -- subject-auxiliary inversion
  | code       -- VP ellipsis (code = stranding under ellipsis)
  | emphasis   -- emphatic/contrastive stress
  deriving DecidableEq, Repr, BEq

/-- A NICE profile records which of the 4 properties a form exhibits. -/
structure NICEProfile where
  auxForm : String
  auxType : AuxType
  negation : Bool
  inversion : Bool
  code : Bool
  emphasis : Bool
  deriving Repr, BEq

/-! ## Classification functions -/

/-- How many NICE properties does this form exhibit? -/
def NICEProfile.niceCount (p : NICEProfile) : Nat :=
  (if p.negation then 1 else 0) +
  (if p.inversion then 1 else 0) +
  (if p.code then 1 else 0) +
  (if p.emphasis then 1 else 0)

/-- Full auxiliary: exhibits all 4 NICE properties. -/
def NICEProfile.isFullAux (p : NICEProfile) : Bool :=
  p.niceCount == 4

/-- Semi-auxiliary: exhibits some but not all NICE properties. -/
def NICEProfile.isSemiAux (p : NICEProfile) : Bool :=
  0 < p.niceCount && p.niceCount < 4

/-! ## Data: English auxiliary NICE profiles -/

/-- Modals (can, will, etc.) — full NICE. -/
def modals : NICEProfile :=
  { auxForm := "can/will/must/..."
  , auxType := .modal
  , negation := true, inversion := true, code := true, emphasis := true }

/-- *be* — full NICE. -/
def be : NICEProfile :=
  { auxForm := "be"
  , auxType := .be
  , negation := true, inversion := true, code := true, emphasis := true }

/-- *have* — full NICE. -/
def have_ : NICEProfile :=
  { auxForm := "have"
  , auxType := .have
  , negation := true, inversion := true, code := true, emphasis := true }

/-- *do* — full NICE (do-support is itself a NICE diagnostic trigger). -/
def do_ : NICEProfile :=
  { auxForm := "do"
  , auxType := .doSupport
  , negation := true, inversion := true, code := true, emphasis := true }

/-- *need* — semi-auxiliary (negation + inversion, but limited code/emphasis). -/
def need : NICEProfile :=
  { auxForm := "need"
  , auxType := .modal
  , negation := true, inversion := true, code := false, emphasis := false }

/-- *dare* — semi-auxiliary (negation + inversion, but limited code/emphasis). -/
def dare : NICEProfile :=
  { auxForm := "dare"
  , auxType := .modal
  , negation := true, inversion := true, code := false, emphasis := false }

/-- *ought* — semi-auxiliary (negation + emphasis, but limited inversion/code). -/
def ought : NICEProfile :=
  { auxForm := "ought"
  , auxType := .modal
  , negation := true, inversion := false, code := false, emphasis := true }

def allProfiles : List NICEProfile :=
  [modals, be, have_, do_, need, dare, ought]

/-! ## Classification theorems -/

theorem modals_are_full : modals.isFullAux = true := rfl
theorem be_is_full : be.isFullAux = true := rfl
theorem have_is_full : have_.isFullAux = true := rfl
theorem do_is_full : do_.isFullAux = true := rfl

theorem need_is_semi : need.isSemiAux = true := rfl
theorem dare_is_semi : dare.isSemiAux = true := rfl
theorem ought_is_semi : ought.isSemiAux = true := rfl

/-! ## Bridge to Phenomena modules

Each NICE property connects to an independently formalized phenomenon. -/

/-- Map each NICE property to the Phenomena module that formalizes it. -/
def niceToModule : NICEProperty → String
  | .negation  => "Phenomena.Negation"
  | .inversion => "Phenomena.WordOrder.SubjectAuxInversion"
  | .code      => "Phenomena.Ellipsis"
  | .emphasis  => "Phenomena.Focus"

end Phenomena.AuxiliaryVerbs.Diagnostics
