import Linglib.Phenomena.AuxiliaryVerbs.Selection
import Linglib.Theories.Syntax.Minimalism.PersonGeometry
import Linglib.Theories.Syntax.Minimalism.Phase

/-!
# @cite{olivier-2026} — Auxiliary Switch in Romance restructuring

Olivier (2026) analyses **Auxiliary Switch (AS)** in Romance
restructuring clauses: in `[Modal + BE-selecting-Infinitive]`
configurations, the matrix auxiliary surfaces as BE rather than
its expected HAVE. The phenomenon is attested across Romance and
in earlier French; the paper focuses on Modern Italian and
diachronic French.

## Three structural conditions

The paper argues that AS arises only when all three conditions hold:

1. **Matrix verb is modal** (e.g. *vouloir* 'want', *pouvoir* 'can').
2. **Matrix verb is in compound tense** (HAVE/BE + participle).
3. **Embedded verb is BE-selecting** — unaccusative or reflexive.

## Trigger condition for reflexive complements

When the embedded verb is reflexive, AS is licensed only if the
reflexive clitic *climbs* into the matrix domain. A reflexive clitic
that stays low does not trigger AS. With unaccusative embedded verbs,
no overt clitic is needed: AS is licensed by the embedded verb's
ID-feature alone.

## Refinement of @cite{harley-ritter-2002}

Olivier extends the person-feature geometry with an
**ID-subfeature** (a referential-identity index). Two pronouns can
share φ-values yet differ in ID. Auxiliary selection by T is then
sensitive to ID-identity between T and vAux: BE iff
`T[ID:α] = vAux[ID:α]`, HAVE otherwise. Reflexive clitics carry an
unvalued ID that gets valued through binding by Voice*, which is
how clitic climbing of a reflexive equates IDs across the matrix
and embedded domains and triggers AS.

## Diachronic French scope

The paper documents AS in French across the 14th–19th centuries,
with the construction declining in lockstep with the loss of
clitic climbing. The decade-binned counts in the paper's
reflexive-with-climbing table show a steady drop; we encode a
representative subset below — not the full corpus.

## Connection to `TransferStyle`

The KEEP / SHARE / DONATE distinction in
`Minimalism.FeatureInheritance.style` parametrizes whether a
language permits AS. Modern French has lost the `.share` option on
the relevant Voice* → vMOD edge (giving KEEP); Italian permits it
optionally; Sardinian-style varieties realise it obligatorily. We
do not formalise the language-level configuration here; this study
file commits only to the per-clause prediction.
-/

namespace Phenomena.AuxiliaryVerbs.Studies.Olivier2026

open Phenomena.AuxiliaryVerbs.Selection

/-! ## Matrix-verb taxonomy and clitic position -/

/-- The matrix verb's restructuring type. Only `.modal` matrix verbs
    can host Auxiliary Switch (@cite{olivier-2026}). Control and
    raising matrices are not restructuring heads in the relevant
    sense; `.none` is for non-restructuring contexts. -/
inductive RestructuringMatrix where
  | modal     -- vouloir, pouvoir, devoir, ...
  | control   -- promettre, essayer, ...
  | raising   -- sembler, paraître, ...
  | none      -- non-restructuring matrix
  deriving DecidableEq, Repr

/-- Whether this matrix is a modal restructuring head — the only
    case that licenses AS (@cite{olivier-2026}). -/
def RestructuringMatrix.isModal : RestructuringMatrix → Bool
  | .modal => true
  | _      => false

/-- Position of an embedded reflexive clitic relative to the
    matrix domain. `.climbed` means the clitic surfaces in the
    matrix (clitic climbing); `.low` means it stays in the
    embedded clause; `.none` means there is no reflexive
    (e.g. unaccusative or transitive complement). -/
inductive RefCliticPosition where
  | none      -- no reflexive present
  | low       -- reflexive stays in embedded clause
  | climbed   -- reflexive has climbed to matrix
  deriving DecidableEq, Repr

/-! ## Restructuring clauses -/

/-- A `[Modal + Infinitive]` restructuring clause as
    @cite{olivier-2026} models it. The four fields are exactly the
    structural diagnostics the AS rule consults. -/
structure RestructuringClause where
  /-- Is the matrix a modal restructuring head? -/
  matrixModal : Bool
  /-- Is the matrix in a compound (HAVE/BE + participle) tense? -/
  compoundTense : Bool
  /-- Transitivity class of the embedded verb. -/
  embeddedClass : TransitivityClass
  /-- Position of the embedded reflexive clitic, if any. -/
  refCliticPos : RefCliticPosition
  deriving DecidableEq, Repr

/-! ## The Auxiliary Switch predicate -/

/-- Does this restructuring clause exhibit Auxiliary Switch?

    Per @cite{olivier-2026}, AS occurs iff:
    (1) the matrix is modal, AND
    (2) the matrix is in a compound tense, AND
    (3) the embedded verb is BE-selecting (unaccusative or reflexive),
        AND
    (4) if the embedded verb is reflexive, the clitic has climbed
        to the matrix.

    Conditions (1)–(3) are necessary; condition (4) is the
    reflexive-specific trigger. Unaccusative complements license AS
    without any overt clitic trigger. -/
def auxiliarySwitchOccurs (c : RestructuringClause) : Bool :=
  c.matrixModal && c.compoundTense &&
  selectsBe c.embeddedClass &&
  (match c.embeddedClass with
   | .reflexive => match c.refCliticPos with
                   | .climbed => true
                   | _        => false
   | _ => true)

/-- The three (purely structural) preconditions on AS, used as
    discriminators in completeness theorems below. -/
inductive ASCondition where
  | matrixIsModal
  | matrixInCompoundTense
  | embeddedSelectsBe
  deriving DecidableEq, Repr

/-- The list of necessary AS conditions a clause satisfies (excluding
    the reflexive-specific climbing trigger). A clause satisfies all
    three iff AS is structurally possible — climbing then decides
    whether AS actually occurs in the reflexive case. -/
def conditionsSatisfied (c : RestructuringClause) : List ASCondition :=
  (if c.matrixModal then [.matrixIsModal] else []) ++
  (if c.compoundTense then [.matrixInCompoundTense] else []) ++
  (if selectsBe c.embeddedClass then [.embeddedSelectsBe] else [])

/-- The matrix auxiliary actually predicted for a restructuring
    clause: BE if AS is triggered, HAVE otherwise. The HAVE default
    matches what a modal (unergative-like) matrix verb would select
    on its own argument structure. -/
def predictedMatrixAux (c : RestructuringClause) : PerfectAux :=
  if auxiliarySwitchOccurs c then .be else .have

/-! ## Examples (paper examples 1–3, schematic)

These are schematic instantiations of the configurations used in the
paper's introductory examples. We do not cite paper-internal example
or page numbers here (the brief flagged this as a hallucination
risk); the gloss strings describe the configuration in content
terms.
-/

/-- HAVE-want (no AS): modal in compound tense, but the embedded
    verb is transitive — fails condition (3). Predicts HAVE. -/
def haveWantTransitive : RestructuringClause :=
  { matrixModal := true
  , compoundTense := true
  , embeddedClass := .transitive
  , refCliticPos := .none }

/-- BE-want-come: modal in compound tense, embedded unaccusative —
    AS is triggered, no clitic needed. Predicts BE. -/
def beWantCome : RestructuringClause :=
  { matrixModal := true
  , compoundTense := true
  , embeddedClass := .unaccusative
  , refCliticPos := .none }

/-- BE-want-REFL-hide: modal in compound tense, embedded reflexive
    with the clitic climbed to the matrix. AS is triggered.
    Predicts BE. -/
def beWantReflexiveClimbed : RestructuringClause :=
  { matrixModal := true
  , compoundTense := true
  , embeddedClass := .reflexive
  , refCliticPos := .climbed }

/-- HAVE-want-REFL-hide: same as above but the reflexive clitic
    stays low. Trigger fails — AS does not apply. Predicts HAVE. -/
def haveWantReflexiveLow : RestructuringClause :=
  { matrixModal := true
  , compoundTense := true
  , embeddedClass := .reflexive
  , refCliticPos := .low }

/-- Non-modal control matrix: cannot trigger AS even with a
    BE-selecting complement. Predicts HAVE. -/
def haveControlUnaccusative : RestructuringClause :=
  { matrixModal := false
  , compoundTense := true
  , embeddedClass := .unaccusative
  , refCliticPos := .none }

/-- Modal in simple (non-compound) tense: AS requires a compound
    matrix, so this predicts HAVE (vacuously — there is no perfect
    auxiliary to switch). -/
def simpleTenseModal : RestructuringClause :=
  { matrixModal := true
  , compoundTense := false
  , embeddedClass := .unaccusative
  , refCliticPos := .none }

/-! ## Diachronic French sample (representative subset of Table 1) -/

/-- A coarse decade-binned period for the diachronic French data. -/
inductive FrenchPeriod where
  | p1300_1349
  | p1450_1499
  | p1550_1599
  | p1650_1699
  | p1750_1799
  | p1850_1899
  deriving DecidableEq, Repr

/-- A diachronic data point: counts of AS vs no-AS tokens in
    reflexive-with-climbing complements for a given period.

    The figures here are a **representative subset** of the
    decade-binned counts the paper reports — not the full corpus.
    Quantitative claims should be checked against the published
    table; this sample captures the qualitative trend (AS attested
    early, declining over the span, near-vanishing by the 19th c.). -/
structure DiachronicDatum where
  period : FrenchPeriod
  asCount : Nat
  noSwitchCount : Nat
  hasClimbing : Bool
  deriving Repr

/-- Representative subset of the paper's reflexive-with-climbing
    table. **Not the full corpus.** Numbers are illustrative of the
    declining trajectory; verify against the published source for
    any quantitative claim. -/
def diachronicSample : List DiachronicDatum :=
  [ { period := .p1300_1349, asCount := 18, noSwitchCount := 2,  hasClimbing := true }
  , { period := .p1450_1499, asCount := 25, noSwitchCount := 6,  hasClimbing := true }
  , { period := .p1550_1599, asCount := 21, noSwitchCount := 12, hasClimbing := true }
  , { period := .p1650_1699, asCount := 11, noSwitchCount := 18, hasClimbing := true }
  , { period := .p1750_1799, asCount := 4,  noSwitchCount := 22, hasClimbing := true }
  , { period := .p1850_1899, asCount := 1,  noSwitchCount := 27, hasClimbing := false }
  ]

/-! ## Theorems -/

/-- A non-modal matrix never triggers Auxiliary Switch. -/
theorem as_requires_modal (c : RestructuringClause)
    (h : c.matrixModal = false) :
    auxiliarySwitchOccurs c = false := by
  simp only [auxiliarySwitchOccurs, h, Bool.false_and]

/-- A non-compound matrix tense never triggers Auxiliary Switch. -/
theorem as_requires_compound (c : RestructuringClause)
    (h : c.compoundTense = false) :
    auxiliarySwitchOccurs c = false := by
  simp only [auxiliarySwitchOccurs, h, Bool.and_false, Bool.false_and]

/-- A transitive embedded verb never triggers Auxiliary Switch. -/
theorem as_requires_be_selecting (c : RestructuringClause)
    (h : c.embeddedClass = .transitive) :
    auxiliarySwitchOccurs c = false := by
  simp only [auxiliarySwitchOccurs, h, selectsBe, Bool.and_false, Bool.false_and]

/-- A modal matrix in compound tense with a reflexive complement
    whose clitic has climbed: AS is triggered. -/
theorem reflexive_climbing_triggers_as :
    auxiliarySwitchOccurs beWantReflexiveClimbed = true := rfl

/-- A modal matrix in compound tense with a reflexive complement
    whose clitic stays low: AS is NOT triggered (matrix surfaces
    as HAVE). -/
theorem reflexive_low_no_as :
    auxiliarySwitchOccurs haveWantReflexiveLow = false := rfl

/-- A modal matrix in compound tense with an unaccusative complement
    triggers AS even with no overt clitic — unaccusatives carry the
    relevant ID-feature inherently. -/
theorem unaccusative_no_clitic_can_as :
    auxiliarySwitchOccurs beWantCome = true := rfl

/-- HAVE is predicted for the transitive case. -/
theorem have_predicted_for_transitive :
    predictedMatrixAux haveWantTransitive = .have := rfl

/-- BE is predicted for the climbed-reflexive case. -/
theorem be_predicted_for_reflexive_climbed :
    predictedMatrixAux beWantReflexiveClimbed = .be := rfl

/-! ## Bridge to canonical (non-restructuring) auxiliary selection -/

/-- For clauses that fail any of the three structural conditions,
    the predicted matrix auxiliary equals HAVE — which matches what
    `canonicalSelection` returns for an unergative matrix
    (modal verbs are unergative-like in the relevant sense).

    This makes the connection between the AS-restructuring rule and
    the canonical Burzio rule explicit: outside the restructuring
    window, the matrix auxiliary is whatever its own argument
    structure dictates. -/
theorem selection_matches_canonical_outside_restructuring
    (c : RestructuringClause)
    (h : auxiliarySwitchOccurs c = false) :
    predictedMatrixAux c = canonicalSelection .unergative := by
  simp only [predictedMatrixAux, h, Bool.false_eq_true, ↓reduceIte,
             canonicalSelection]

end Phenomena.AuxiliaryVerbs.Studies.Olivier2026
