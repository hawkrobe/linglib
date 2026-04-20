import Linglib.Fragments.English.Auxiliaries
import Linglib.Phenomena.WordOrder.SubjectAuxInversion

/-!
# English Auxiliary Diagnostics: NICE Properties
@cite{huddleston-1976} @cite{palmer-2001}

@cite{huddleston-1976} coined the NICE acronym for four properties of English
auxiliaries identified by @cite{palmer-2001}: Negation, Inversion, Code,
Emphasis.

| Property | Test                              | Example          |
|----------|-----------------------------------|------------------|
| Negation | Direct negation with *not*        | *He can not go*  |
| Inversion| Subject-aux inversion in questions| *Can he go?*     |
| Code     | VP ellipsis (stranding)           | *He can and she can too* |
| Emphasis | Emphatic stress for verum focus   | *He CAN go*      |

## End-to-end chain

`AuxEntry` (Fragment) → `AuxClass` (Huddleston classification) →
`NICEProfile` (4-Bool feature vector) → `predictSAI` → `SAIDatum.acceptability`.

Each link is a function, not a stipulated table. Changing a Fragment
entry's `form` reroutes its `AuxClass`; changing `predictSAI`'s rule
breaks the bridge theorems against the SAI data; changing an SAI datum's
acceptability breaks them too.
-/

namespace Phenomena.AuxiliaryVerbs.Diagnostics

open Fragments.English.Auxiliaries (AuxEntry AuxType)
open Phenomena.WordOrder.SubjectAuxInversion (SAIContext Acceptability SAIDatum)

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
  negation  : Bool
  inversion : Bool
  code      : Bool
  emphasis  : Bool
  deriving Repr, BEq, DecidableEq

/-- Project a profile by NICE property. -/
def NICEProfile.has (p : NICEProfile) : NICEProperty → Bool
  | .negation  => p.negation
  | .inversion => p.inversion
  | .code      => p.code
  | .emphasis  => p.emphasis

/-- How many NICE properties does this profile exhibit? -/
def NICEProfile.count (p : NICEProfile) : Nat :=
  (if p.negation  then 1 else 0) + (if p.inversion then 1 else 0) +
  (if p.code      then 1 else 0) + (if p.emphasis  then 1 else 0)

/-- Full auxiliary: exhibits all 4 NICE properties. -/
def NICEProfile.isFull (p : NICEProfile) : Bool := p.count == 4

/-- Semi-auxiliary: some but not all. -/
def NICEProfile.isSemi (p : NICEProfile) : Bool := 0 < p.count ∧ p.count < 4

/-- Lexical verb (no NICE properties). -/
def NICEProfile.isLexical (p : NICEProfile) : Bool := p.count == 0

/-! ## Huddleston classification

@cite{huddleston-1976} groups English auxiliaries into three NICE classes:
- **Full**: modals + do/be/have — all four properties.
- **Semi (N+I)**: *dare*, *need* — Negation and Inversion only.
- **Semi (N+E)**: *ought* — Negation and Emphasis only (Inversion is
  conservative; *Ought he to go?* is grammatical for many BrE speakers). -/

/-- NICE-diagnostic class of an auxiliary. -/
inductive AuxClass where
  | full     -- all 4 NICE properties
  | semiNI   -- Negation + Inversion (need, dare)
  | semiNE   -- Negation + Emphasis (ought)
  deriving DecidableEq, Repr

/-- The NICE feature vector predicted by Huddleston's class. -/
def AuxClass.toNICE : AuxClass → NICEProfile
  | .full   => ⟨true,  true,  true,  true⟩
  | .semiNI => ⟨true,  true,  false, false⟩
  | .semiNE => ⟨true,  false, false, true⟩

/-- Classify a Fragment auxiliary entry per Huddleston's NICE diagnostic.
    Only `dare`, `need`, `ought` are semi; everything else in the Fragment
    auxiliary inventory is full. -/
def auxClass (e : AuxEntry) : AuxClass :=
  match e.form with
  | "ought" => .semiNE
  | "dare"  => .semiNI
  | "need"  => .semiNI
  | _       => .full

/-- NICE profile for a Fragment auxiliary entry, derived from its class. -/
def nice (e : AuxEntry) : NICEProfile := (auxClass e).toNICE

/-- NICE profile for a non-auxiliary lexical verb (no NICE properties). -/
def lexicalVerbNICE : NICEProfile := ⟨false, false, false, false⟩

/-! ## Contracted negation (Fragment-derived)

@cite{huddleston-1976} notes that NICE Negation concerns direct *not*-
negation; contracted negation (*-n't*) is a stronger sub-property with
paradigm gaps at *may* and *am*. The `negForm : Option String` field in
`AuxEntry` records each entry's contracted form (or absence). -/

/-- Whether a Fragment entry has a contracted negative form. -/
def hasContractedNeg (e : AuxEntry) : Bool := e.negForm.isSome

section FragmentChecks
open Fragments.English.Auxiliaries

theorem can_has_neg     : hasContractedNeg can    = true  := rfl
theorem will_has_neg    : hasContractedNeg will   = true  := rfl
theorem is_has_neg      : hasContractedNeg is_    = true  := rfl
theorem do_has_neg      : hasContractedNeg do_    = true  := rfl
theorem have_has_neg    : hasContractedNeg have_  = true  := rfl
theorem need_has_neg    : hasContractedNeg need   = true  := rfl
theorem dare_has_neg    : hasContractedNeg dare   = true  := rfl
theorem ought_has_neg   : hasContractedNeg ought  = true  := rfl
-- Paradigm gaps:
theorem may_lacks_neg   : hasContractedNeg may    = false := rfl
theorem am_lacks_neg    : hasContractedNeg am     = false := rfl

end FragmentChecks

/-! ## Aggregate collections -/

section Collections
open Fragments.English.Auxiliaries

/-- Full auxiliaries (modals + do/be/have). -/
def allFullAuxiliaries : List AuxEntry :=
  [ can, could, will, would, shall, should, may, might, must
  , is_, am, are, was, were
  , do_, does, did
  , have_, has, had ]

/-- Semi-modals (Huddleston's N+I and N+E classes combined). -/
def allSemiModals : List AuxEntry := [need, dare, ought]

def allAuxiliaries : List AuxEntry := allFullAuxiliaries ++ allSemiModals

/-- Every full auxiliary classifies as full under `nice`. -/
theorem all_full_classify_full :
    allFullAuxiliaries.all (λ e => (nice e).isFull) = true := by decide

/-- Every semi-modal classifies as semi under `nice`. -/
theorem all_semi_classify_semi :
    allSemiModals.all (λ e => (nice e).isSemi) = true := by decide

end Collections

/-! ## SAI prediction from NICE profile

NICE properties predict participation in specific SAI contexts:

| NICE Property | SAI Context        | Aux example           | Lex verb (do-support) |
|---------------|--------------------|-----------------------|------------------------|
| Inversion     | matrixWh / matrixYN| *Can he go?*          | *Does he go?*          |
| Negation      | sententialNegation | *Sue is not eating*   | *Sue does not eat*     |
| Code          | vpEllipsis         | *She can too*         | *He does too*          |
| Emphasis      | emphatic           | *She IS eating*       | *Sue DOES eat*         |

Other SAI contexts (embedded, echo, conditional inversion, ...) are not
directly diagnosed by NICE — for those, `predictSAI` defers to
`grammatical` since NICE does not constrain them. -/

/-- The NICE property that an SAI context diagnoses (if any). -/
def saiContextNICE : SAIContext → Option NICEProperty
  | .matrixWh | .matrixYN  => some .inversion
  | .sententialNegation    => some .negation
  | .vpEllipsis            => some .code
  | .emphatic              => some .emphasis
  | _                      => none

/-- Predict SAI acceptability from a NICE profile. The verb's profile
    must license the NICE property the context diagnoses; otherwise the
    prediction is `ungrammatical` (do-support is the standard repair —
    modeled by giving `do_` the auxiliary profile and predicting from
    that, rather than via predicate-internal repair logic). -/
def predictSAI (p : NICEProfile) (ctx : SAIContext) : Acceptability :=
  match saiContextNICE ctx with
  | none      => .grammatical
  | some prop => if p.has prop then .grammatical else .ungrammatical

/-! ## Bridge: `predictSAI` agrees with the SAI table

A representative sample of (NICE-profile, SAIDatum) pairs covering
auxiliary-passes and lexical-verb-fails for each NICE property, plus
do-support successes (where `do` itself is the auxiliary). -/

section SAIBridge
open Fragments.English.Auxiliaries
open Phenomena.WordOrder.SubjectAuxInversion

/-- Pairs of (NICE profile, SAI datum) where `predictSAI` should reproduce
    the datum's `acceptability`. -/
def predictionTable : List (NICEProfile × SAIDatum) :=
  [ -- Auxiliary participates directly in NICE contexts:
    (nice can,  ex01)   -- inversion (matrixWh)   → grammatical
  , (nice is_,  ex34)   -- negation (sentNeg)     → grammatical
  , (nice do_,  ex38)   -- code (vpEllipsis)      → grammatical
  , (nice is_,  ex40)   -- emphasis (emphatic)    → grammatical
  -- Lexical verb fails NICE diagnosis:
  , (lexicalVerbNICE, ex28)  -- *Eats John pizza?     (matrixYN)
  , (lexicalVerbNICE, ex33)  -- *Sue not eats fish    (sentNeg)
  -- Do-support: `do` carries the auxiliary profile in NICE contexts:
  , (nice do_,  ex27)   -- "Where does Sue eat fish?" (matrixWh)
  , (nice do_,  ex32)   -- "Sue does not eat fish"    (sentNeg)
  , (nice do_,  ex39)   -- "Sue DOES eat fish"        (emphatic)
  ]

/-- `predictSAI` agrees with the SAI table on every entry of
    `predictionTable`. Changing `nice`, `predictSAI`,
    `saiContextNICE`, or any `SAIDatum.acceptability` referenced
    above breaks this theorem. -/
theorem predictSAI_agrees :
    predictionTable.all (λ (p, d) => predictSAI p d.context == d.acceptability)
      = true := by decide

end SAIBridge

end Phenomena.AuxiliaryVerbs.Diagnostics
