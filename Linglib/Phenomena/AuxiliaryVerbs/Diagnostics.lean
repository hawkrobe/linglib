import Linglib.Fragments.English.FunctionWords
import Linglib.Phenomena.WordOrder.SubjectAuxInversion
import Linglib.Phenomena.Focus.PolarityStress

/-!
# English Auxiliary Diagnostics: NICE Properties
@cite{huddleston-1976} @cite{palmer-2001}

@cite{huddleston-1976} coined the NICE acronym for four properties of English
auxiliaries identified by Palmer: Negation, Inversion, Code, Emphasis.

| Property | Test | Example |
|----------|------|---------|
| Negation | Direct negation with *not* | *He can not go* |
| Inversion | Subject-aux inversion in questions | *Can he go?* |
| Code | VP ellipsis (stranding) | *He can and she can too* |
| Emphasis | Emphatic stress for verum focus | *He CAN go* |

## End-to-End Chain

This file creates a three-link chain from Fragment to empirical data:

    Fragment (AuxEntry: form, auxType, negForm)
      → NICE profile (per-entry, derived from Fragment fields)
        → SAI predictions (each NICE property maps to an SAI context)
          → SAI data (Phenomena.WordOrder.SubjectAuxInversion)

Each link is verified by theorems: changing a Fragment entry's `form` or
`negForm` breaks the NICE profile theorems, and changing an SAI datum's
acceptability breaks the prediction theorems.
-/

namespace Phenomena.AuxiliaryVerbs.Diagnostics

open Fragments.English.FunctionWords (AuxEntry AuxType)

/-! ## Types -/

/-- The four NICE properties. -/
inductive NICEProperty where
  | negation   -- direct negation with *not*
  | inversion  -- subject-auxiliary inversion
  | code       -- VP ellipsis (code = stranding under ellipsis)
  | emphasis   -- emphatic/contrastive stress
  deriving DecidableEq, Repr

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

/-! ## Link 1: Fragment → NICE Profiles

Per-entry NICE profiles. Each derives `auxForm` and `auxType` from the
Fragment `AuxEntry`, making the connection structural: changing a Fragment
entry's form breaks the corresponding theorem. -/

/-- Full NICE profile for a true auxiliary Fragment entry. -/
def fullNICE (e : AuxEntry) : NICEProfile :=
  { auxForm := e.form, auxType := e.auxType
  , negation := true, inversion := true, code := true, emphasis := true }

section FragmentBridge
open Fragments.English.FunctionWords

/-- Contracted negation: whether the Fragment entry has a `negForm`.
    Paradigm gaps (`may`, `am`) lack contracted forms. -/
def hasContractedNeg (e : AuxEntry) : Bool := e.negForm.isSome

-- Full auxiliaries: all 4 NICE properties
def canProfile     := fullNICE can
def couldProfile   := fullNICE could
def willProfile    := fullNICE will
def wouldProfile   := fullNICE would
def shallProfile   := fullNICE shall
def shouldProfile  := fullNICE should
def mayProfile     := fullNICE may
def mightProfile   := fullNICE might
def mustProfile    := fullNICE must
def isProfile      := fullNICE is_
def amProfile      := fullNICE am
def areProfile     := fullNICE are
def wasProfile     := fullNICE was
def wereProfile    := fullNICE were
def doProfile      := fullNICE do_
def doesProfile    := fullNICE does
def didProfile     := fullNICE did
def haveProfile    := fullNICE have_
def hasAuxProfile  := fullNICE has
def hadProfile     := fullNICE had

-- Semi-auxiliaries: partial NICE
def needProfile : NICEProfile :=
  { auxForm := need.form, auxType := need.auxType
  , negation := true, inversion := true, code := false, emphasis := false }

def dareProfile : NICEProfile :=
  { auxForm := dare.form, auxType := dare.auxType
  , negation := true, inversion := true, code := false, emphasis := false }

/-- *Ought* has partial NICE: negation (*oughtn't*) and emphasis (*He OUGHT to go*)
    but not code (*?He ought and she ought too*). Inversion is set to `false`
    following @cite{huddleston-1976}'s conservative classification, though
    *Ought he to go?* is grammatical for many speakers (especially BrE). -/
def oughtProfile : NICEProfile :=
  { auxForm := ought.form, auxType := ought.auxType
  , negation := true, inversion := false, code := false, emphasis := true }

/-! ### Classification theorems -/

theorem can_is_full   : canProfile.isFullAux = true := rfl
theorem is_is_full    : isProfile.isFullAux = true := rfl
theorem do_is_full    : doProfile.isFullAux = true := rfl
theorem have_is_full  : haveProfile.isFullAux = true := rfl

theorem need_is_semi  : needProfile.isSemiAux = true := rfl
theorem dare_is_semi  : dareProfile.isSemiAux = true := rfl
theorem ought_is_semi : oughtProfile.isSemiAux = true := rfl

/-! ### Per-entry form verification

These theorems verify that NICE profiles match their Fragment entries.
Changing a Fragment entry's `form` field breaks the theorem. -/

theorem can_form   : canProfile.auxForm = "can"   := rfl
theorem may_form   : mayProfile.auxForm = "may"   := rfl
theorem is_form    : isProfile.auxForm = "is"     := rfl
theorem do_form    : doProfile.auxForm = "do"     := rfl
theorem have_form  : haveProfile.auxForm = "have" := rfl
theorem need_form  : needProfile.auxForm = "need" := rfl
theorem dare_form  : dareProfile.auxForm = "dare" := rfl
theorem ought_form : oughtProfile.auxForm = "ought" := rfl

/-! ### Contracted negation bridge

@cite{huddleston-1976} notes NICE Negation is about direct negation with
*not*; contracted negation (*-n't*) is a stronger sub-property with
paradigm gaps at *may* and *am*. -/

-- Full contracted paradigm
theorem can_has_neg   : hasContractedNeg can = true := rfl
theorem will_has_neg  : hasContractedNeg will = true := rfl
theorem is_has_neg    : hasContractedNeg is_ = true := rfl
theorem do_has_neg    : hasContractedNeg do_ = true := rfl
theorem have_has_neg  : hasContractedNeg have_ = true := rfl

-- Paradigm gaps
theorem may_lacks_neg : hasContractedNeg may = false := rfl
theorem am_lacks_neg  : hasContractedNeg am = false := rfl

-- Semi-modals have contracted negation (needn't, daren't, oughtn't)
theorem need_has_neg  : hasContractedNeg need = true := rfl
theorem dare_has_neg  : hasContractedNeg dare = true := rfl
theorem ought_has_neg : hasContractedNeg ought = true := rfl

end FragmentBridge

/-! ## Link 2: NICE Properties → SAI Predictions

Each NICE property maps to a specific SAI context type. Full auxiliaries
participate directly; lexical verbs require do-support.

| NICE Property | SAI Context | Aux Example | Lex Verb (do-support) |
|---------------|-------------|-------------|-----------------------|
| Inversion | matrixWh/matrixYN | *Can he go?* | *Does he go?* |
| Negation | sententialNegation | *Sue is not eating* | *Sue does not eat* |
| Code | vpEllipsis | *She can too* | *He does too* |
| Emphasis | emphatic | *She IS eating* | *Sue DOES eat* |
-/

section SAIBridge
open Phenomena.WordOrder.SubjectAuxInversion

/-- NICE Inversion → SAI: auxiliaries invert in matrix questions;
    lexical verbs cannot (do-support required). -/
theorem nice_inversion_predicts_sai :
    -- NICE says `can` has inversion
    canProfile.inversion = true ∧
    -- SAI data: "What can John eat?" is grammatical with inversion
    ex01.inverted = true ∧ ex01.acceptability = .grammatical ∧
    -- SAI data: "*Eats John pizza?" — lexical verb can't invert
    ex28.inverted = true ∧ ex28.acceptability = .ungrammatical :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- NICE Negation → SAI: auxiliaries raise past negation;
    lexical verbs cannot (do-support required). -/
theorem nice_negation_predicts_sai :
    -- NICE says `is` has negation
    isProfile.negation = true ∧
    -- SAI data: "Sue is not eating fish" is grammatical
    ex34.context = .sententialNegation ∧ ex34.acceptability = .grammatical ∧
    -- SAI data: "*Sue not eats fish" is ungrammatical
    ex33.context = .sententialNegation ∧ ex33.acceptability = .ungrammatical :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- NICE Code → SAI: VP ellipsis strands auxiliary or do-support. -/
theorem nice_code_confirmed_by_sai :
    -- NICE says `do` has code
    doProfile.code = true ∧
    -- SAI data: "She runs faster than he does" (do-support strands tense)
    ex38.context = .vpEllipsis ∧ ex38.acceptability = .grammatical :=
  ⟨rfl, rfl, rfl⟩

/-- NICE Emphasis → SAI: auxiliaries bear verum focus directly;
    lexical verbs need do-support. -/
theorem nice_emphasis_predicts_sai :
    -- NICE says `is` has emphasis
    isProfile.emphasis = true ∧
    -- SAI data: "She IS eating fish" (auxiliary bears verum focus)
    ex40.context = .emphatic ∧ ex40.acceptability = .grammatical ∧
    -- SAI data: "Sue DOES eat fish" (do-support for lexical verb verum)
    ex39.context = .emphatic ∧ ex39.acceptability = .grammatical :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Do-support is the repair strategy when lexical verbs (which lack NICE
    properties) need to participate in SAI contexts. All four NICE contexts
    have grammatical do-support alternatives in the SAI data. -/
theorem do_support_repairs_all_nice_contexts :
    -- Inversion: "Where does Sue eat fish?"
    ex27.context = .matrixWh ∧ ex27.acceptability = .grammatical ∧
    -- Negation: "Sue does not eat fish"
    ex32.context = .sententialNegation ∧ ex32.acceptability = .grammatical ∧
    -- Code: "She runs faster than he does"
    ex38.context = .vpEllipsis ∧ ex38.acceptability = .grammatical ∧
    -- Emphasis: "Sue DOES eat fish"
    ex39.context = .emphatic ∧ ex39.acceptability = .grammatical :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SAIBridge

/-! ## Link 3: NICE Emphasis ↔ Polarity Stress

NICE Emphasis (emphatic stress on auxiliary for verum focus) is the same
phenomenon as polarity stress: prosodic prominence on the auxiliary targets
truth/polarity rather than content alternatives (@cite{hohle-1992}). -/

section PolarityStressBridge
open Phenomena.Focus.PolarityStress

/-- NICE Emphasis maps to polarity stress on the auxiliary: both describe
    prosodic prominence on AUX signaling verum focus. The PolarityStress
    datum confirms this with "John DOES drink" (stressed AUX in declarative). -/
theorem nice_emphasis_is_polarity_stress :
    -- NICE says full auxiliaries have emphasis
    doProfile.emphasis = true ∧
    -- PolarityStress data: "John DOES drink" stresses auxiliary
    emphaticDoDeclarative.stressedElement = "auxiliary" ∧
    emphaticDoDeclarative.clauseType = "declarative" :=
  ⟨rfl, rfl, rfl⟩

/-- Content focus is distinct from NICE Emphasis: stressing the subject
    ("JOHN drinks") targets content alternatives, not polarity. -/
theorem content_focus_not_nice_emphasis :
    contentFocusSubject.stressedElement = "subject" ∧
    contentFocusSubject.effect = "Identifies who drinks (content focus, not polarity)" :=
  ⟨rfl, rfl⟩

end PolarityStressBridge

/-! ## Aggregate Collections -/

def allFullProfiles : List NICEProfile :=
  [canProfile, couldProfile, willProfile, wouldProfile,
   shallProfile, shouldProfile,
   mayProfile, mightProfile, mustProfile,
   isProfile, amProfile, areProfile, wasProfile, wereProfile,
   doProfile, doesProfile, didProfile,
   haveProfile, hasAuxProfile, hadProfile]

def allSemiProfiles : List NICEProfile :=
  [needProfile, dareProfile, oughtProfile]

def allProfiles : List NICEProfile :=
  allFullProfiles ++ allSemiProfiles

end Phenomena.AuxiliaryVerbs.Diagnostics
