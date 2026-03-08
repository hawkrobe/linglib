/-!
# Minimal Pronoun Theory
@cite{kratzer-1998} @cite{kratzer-2009} @cite{safir-2014} @cite{landau-2015} @cite{landau-2018}

All instances of bound variable anaphora — reflexives, PRO, bound variable
pronouns — are syntactically identical: bare D heads with unvalued φ-features
("minimal pronouns"). Cross-linguistic variation in their surface form
(null, reflexive, pronoun) reduces entirely to variation in **vocabulary items**,
language-specific contextual allomorphs applied postsyntactically.

## Key Definitions

- `BVAContext`: The four licensing contexts for bound variable anaphora
- `VocabItem`: A context-sensitive realization rule (D[πφ] → Form / context)
- `MinPronInventory`: A language's vocabulary item inventory + elsewhere default
- `OCSignature`: @cite{landau-2013}'s Obligatory Control diagnostic package
- `BVASyncretism`: Cross-linguistic syncretism patterns across BVA contexts

## Core Claims

1. Minimal pronouns are D heads with unvalued φ-features
2. φ-values are transmitted from the antecedent (via Agree or variable binding)
3. Vocabulary items map valued feature bundles to surface forms, conditioned
   by syntactic context (locally bound, controlled subject, etc.)
4. The **Elsewhere Condition**: if no context-specific item matches, the
   default (pronoun) applies (@cite{safir-2014}: "all anaphoric diversity
   is morphological")
5. Cross-linguistic variation in anaphoric exponence reduces to variation
   in vocabulary item inventories
-/

namespace Syntax.Minimalism.MinimalPronoun

-- ════════════════════════════════════════════════════════════════
-- § 1: Licensing Contexts
-- ════════════════════════════════════════════════════════════════

/-- The four syntactic contexts in which a minimal pronoun can occur.
    Each context may trigger a different vocabulary item (surface form). -/
inductive BVAContext where
  /-- Subject of a controlled clause — PRO in English -/
  | controlledSubject
  /-- Locally bound — reflexive in English (Condition A domain) -/
  | locallyBound
  /-- Bound by a non-local c-commanding antecedent -/
  | boundVariable
  /-- Free / referential (unbound) -/
  | free
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2: Vocabulary Items and the Elsewhere Condition
-- ════════════════════════════════════════════════════════════════

/-- A vocabulary item: a context-specific realization rule for a minimal pronoun.

    In DM terms: D[πφ] → `form` / `context` ...

    Vocabulary items are ordered by specificity. When multiple items could
    apply, the most specific (first in the list) wins. -/
structure VocabItem (Form : Type) where
  /-- The syntactic context this item is restricted to -/
  context : BVAContext
  /-- The surface form this item realizes -/
  form : Form

/-- A language's inventory of vocabulary items for minimal pronouns.

    The `items` list is ordered by specificity (most specific first).
    The `elsewhere` form applies when no context-specific item matches.

    @cite{safir-2014}: "from this single element, all anaphoric diversity
    is morphological" -/
structure MinPronInventory (Form : Type) where
  /-- Context-specific vocabulary items, ordered by specificity -/
  items : List (VocabItem Form)
  /-- Default exponence: applies when no specific item matches.
      Crosslinguistically, this is the pronoun form (@cite{safir-2014}). -/
  elsewhere : Form

/-- The Elsewhere Condition: find the first vocabulary item whose context
    matches; if none does, use the elsewhere (default pronoun) form. -/
def MinPronInventory.realize {Form : Type}
    (inv : MinPronInventory Form) (ctx : BVAContext) : Form :=
  match inv.items.find? (·.context == ctx) with
  | some item => item.form
  | none => inv.elsewhere

/-- A language's realized form for controlled subjects specifically.
    This is the function that distinguishes null-PRO from overt-PRO languages. -/
def MinPronInventory.controlForm {Form : Type}
    (inv : MinPronInventory Form) : Form :=
  inv.realize .controlledSubject

-- ════════════════════════════════════════════════════════════════
-- § 3: Obligatory Control Signature
-- ════════════════════════════════════════════════════════════════

/-- @cite{landau-2013}'s Obligatory Control signature.

    A clause S exhibits OC iff its subject satisfies both conditions:
    (a) the controller(s) X must be codependent(s) of S
    (b) PRO (or part of it) must be interpreted as a bound variable

    Additional diagnostics derived from (a)-(b):
    - Under VPE, only sloppy readings available (from (b))
    - Exhaustive binding required — no partial control (from (b))
    - Local c-commanding antecedent required (from (a)) -/
structure OCSignature where
  /-- (a): Controller must be argument of the matrix predicate -/
  controllerCodependent : Bool
  /-- (b): Embedded subject interpreted as bound variable -/
  boundVariable : Bool
  /-- Derived from (b): VPE allows only sloppy, not strict readings -/
  sloppyOnly : Bool
  /-- Derived from (b): No partial control (subset/superset antecedent) -/
  exhaustive : Bool
  /-- Derived from (a): Antecedent must locally c-command -/
  localCCommand : Bool
  deriving DecidableEq, BEq, Repr

/-- The full OC signature: all diagnostics positive. -/
def ocFull : OCSignature where
  controllerCodependent := true
  boundVariable := true
  sloppyOnly := true
  exhaustive := true
  localCCommand := true

/-- No OC: none of the diagnostics hold. -/
def ocNone : OCSignature where
  controllerCodependent := false
  boundVariable := false
  sloppyOnly := false
  exhaustive := false
  localCCommand := false

/-- Does a clause type show obligatory control? -/
def OCSignature.isOC (sig : OCSignature) : Bool :=
  sig.controllerCodependent && sig.boundVariable

-- ════════════════════════════════════════════════════════════════
-- § 4: Cross-Linguistic Syncretism Typology
-- ════════════════════════════════════════════════════════════════

/-- Cross-linguistic syncretism among BVA forms.

    Records whether each BVA context uses the same form as the
    referential (free) pronoun. "=" means syncretic with the referential
    pronoun; "×" means a distinct form is used.

    Table 92 in @cite{ostrove-2026}:
    ```
                      Reflexive  Controlled subj  Bound var pronoun
    English              ×            ×                 =
    Quiegolani Zap.      =            =                 =
    Haitian              =            ×                 =
    SMPM                 ×            =                 =
    ```
-/
structure BVASyncretism where
  language : String
  /-- Is the reflexive form identical to the referential pronoun? -/
  reflexiveEqReferential : Bool
  /-- Is the controlled subject form identical to the referential pronoun? -/
  controlledEqReferential : Bool
  /-- Is the bound variable pronoun identical to the referential pronoun? -/
  boundVarEqReferential : Bool
  deriving DecidableEq, BEq, Repr

/-- Derive syncretism from a vocabulary item inventory.

    A context is syncretic with the referential pronoun iff its
    realized form equals the elsewhere (pronoun) form — i.e., no
    context-specific vocabulary item overrides the default. -/
def syncretismFromInventory {Form : Type} [BEq Form]
    (inv : MinPronInventory Form) (lang : String := "") : BVASyncretism where
  language := lang
  reflexiveEqReferential := inv.realize .locallyBound == inv.elsewhere
  controlledEqReferential := inv.realize .controlledSubject == inv.elsewhere
  boundVarEqReferential := inv.realize .boundVariable == inv.elsewhere

-- ════════════════════════════════════════════════════════════════
-- § 5: Standard Surface Forms
-- ════════════════════════════════════════════════════════════════

/-- Standard surface form categories for bound variable anaphora.

    These are the cross-linguistically attested exponence options for
    minimal pronouns. Each vocabulary item maps a BVA context to one
    of these forms. -/
inductive PronForm where
  /-- Silent (null PRO) -/
  | null
  /-- Overt pronoun (φ-matching clitic or full form) -/
  | pronoun
  /-- Reflexive anaphor (English *-self*, SMPM *mí* + pronoun) -/
  | reflexive
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 6: Copy Control Typology
-- ════════════════════════════════════════════════════════════════

/-- Types of copy control (@cite{polinsky-potsdam-2006},
    @cite{ostrove-2026} §5).

    Copy control: the subject of a control clause is a phonologically
    overt copy of its controller. Four subtypes are distinguished by
    the nature of the copy and its distribution. -/
inductive CopyControlType where
  /-- Full copy: PRO is a full DP copy of the controller.
      Attested in San Lucas Quievaní Zapotec, Copala Triqui. -/
  | fullCopy
  /-- Logophoric pronominal: PRO is a pronoun, occurs only in
      attitude reports. Attested in Gengbe, Mandarin. -/
  | logophoricPronominal
  /-- Scope-sensitive pronominal: PRO is a pronoun, triggered by
      scope-taking operators (focus). Attested in Italian, Hungarian,
      European Portuguese. -/
  | scopeSensitivePronominal
  /-- Obligatory pronominal: PRO is an overt clitic pronoun in all
      control contexts, showing the full OC signature. Attested in
      SMPM, Gã, Büli. -/
  | obligatoryPronominal
  deriving DecidableEq, BEq, Repr

/-- Properties distinguishing copy control types. -/
structure CopyControlProfile where
  controlType : CopyControlType
  /-- Does the copy show the full OC signature (bound variable, exhaustive)? -/
  showsOC : Bool
  /-- Is the copy restricted to attitude report contexts? -/
  attitudeOnly : Bool
  /-- Does the copy require a scope-taking operator (focus, only)? -/
  requiresScopeOperator : Bool
  /-- Can the copy bear focus? -/
  copyCanBearFocus : Bool
  deriving DecidableEq, BEq, Repr

/-- Profile for each copy control type. -/
def copyControlProfile : CopyControlType → CopyControlProfile
  | .fullCopy => ⟨.fullCopy, false, false, false, true⟩
  | .logophoricPronominal => ⟨.logophoricPronominal, false, true, false, true⟩
  | .scopeSensitivePronominal => ⟨.scopeSensitivePronominal, false, false, true, true⟩
  | .obligatoryPronominal => ⟨.obligatoryPronominal, true, false, false, false⟩

-- ════════════════════════════════════════════════════════════════
-- § 7: Exempt Anaphors
-- ════════════════════════════════════════════════════════════════

/-- Exempt anaphors (@cite{pollard-sag-1994}): reflexive forms used
    outside their canonical binding domain (Condition A domain).

    Key constraint: exempt anaphors cannot have quantified antecedents.
    This is used in @cite{ostrove-2026} §6 to argue for base-generation
    over movement in control. -/
structure ExemptAnaphorProfile where
  /-- Exempt anaphors available in this language -/
  hasExemptAnaphors : Bool
  /-- Can exempt anaphors have quantified antecedents? -/
  allowsQuantifiedAntecedent : Bool
  deriving DecidableEq, BEq, Repr

/-- The two analyses of obligatory control derivation. -/
inductive ControlDerivation where
  /-- Controller base-generated in matrix; PRO base-generated in
      embedded clause. Two distinct syntactic positions, linked by
      variable binding. -/
  | baseGeneration
  /-- Controller enters derivation in embedded subject position and
      moves to matrix position. One DP, two copies. -/
  | movement
  deriving DecidableEq, BEq, Repr

/-- Movement predicts exempt anaphors are UNAVAILABLE with quantified
    controllers (because the copy in embedded position would be a QP,
    violating the exempt anaphor constraint).

    Base-generation predicts exempt anaphors ARE available (the pronoun
    in embedded position is a genuine pronoun, not a copy of the QP). -/
def predictsExemptWithQuantifiedController : ControlDerivation → Bool
  | .baseGeneration => true
  | .movement       => false

end Syntax.Minimalism.MinimalPronoun
