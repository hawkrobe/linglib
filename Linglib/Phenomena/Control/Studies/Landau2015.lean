import Linglib.Theories.Syntax.Minimalism.MinimalPronoun

/-!
# Landau (2015): A Two-Tiered Theory of Control
@cite{landau-2015} @cite{landau-2004} @cite{landau-2013}

MIT Press. ISBN 978-0-262-02963-1.

OC in complement clauses divides into two subtypes:
- **Predicative control**: nonattitude complements, PRO moves to Spec,Fin,
  control via syntactic predication
- **Logophoric control**: attitude complements, C^OC projects a perspectival
  coordinate, control via predication + variable binding

## Key Definitions

- `ControlTier`: The two tiers of control (predicative vs. logophoric)
- `LandauPredicateClass`: Eight predicate classes mapped to control tiers
- `LandauClauseClass`: Finiteness scale (C-subjunctive, F-subjunctive, finite)
- `agrBlocksControl`: The OC-NC generalization — [+Agr] blocks logophoric
  control but not predicative control (70)
- `TTCContrast`: The six empirical contrasts between the two tiers (table (80))

## Core Claims

1. OC splits into predicative (nonattitude, EC) and logophoric (attitude, PC)
2. Predicative control: predication only; logophoric: predication + variable binding
3. [+Agr] blocks logophoric control but not predicative control (the OC-NC
   generalization, (70))
4. Feature Transmission asymmetry: predication is NOT contingent on feature
   matching (60a); variable binding IS (60b)
5. Six empirical contrasts systematically align with the predicative/logophoric
   divide (table (80)): inflected complements, [−human] PRO, implicit control,
   control shift, partial control, split control
-/

namespace Phenomena.Control.Studies.Landau2015

open Syntax.Minimalism.MinimalPronoun

-- ════════════════════════════════════════════════════════════════
-- § 1: The Two-Tiered Theory of Control
-- ════════════════════════════════════════════════════════════════

/-- The two tiers of obligatory control (table (119) of @cite{landau-2015}).

    Predicative control (EC complements):
    - Selected by nonattitude predicates (implicative, aspectual, modal, evaluative)
    - PRO moves to Spec,Fin → control via syntactic predication
    - Forces exhaustive control (EC)
    - Complement head: transitive Fin_{[uD]}

    Logophoric control (PC complements):
    - Selected by attitude predicates (factive, propositional, desiderative,
      interrogative)
    - C^OC projects a perspectival coordinate → control via predication +
      variable binding
    - Allows partial control (PC)
    - Complement head: transitive C^OC_{[uD]}
    - Associated with obligatory *de se* interpretation -/
inductive ControlTier where
  /-- Predicative control: nonattitude, predication only -/
  | predicative
  /-- Logophoric control: attitude, predication + variable binding -/
  | logophoric
  deriving DecidableEq, BEq, Repr

/-- Attitude complements allow logophoric control;
    nonattitude complements force predicative control. -/
def ControlTier.isAttitude : ControlTier → Bool
  | .predicative => false
  | .logophoric  => true

/-- Partial control is available only under logophoric control.
    Predicative control forces exhaustive control (EC).
    @cite{landau-2015} Ch 5 -/
def ControlTier.allowsPartialControl : ControlTier → Bool
  | .predicative => false
  | .logophoric  => true

/-- Obligatory *de se* arises only under logophoric control.
    Predicative contexts are free of the *de se* entailment. -/
def ControlTier.obligatoryDeSe : ControlTier → Bool
  | .predicative => false
  | .logophoric  => true

/-- Control shift (from subject to object controller) is available
    only under logophoric control. -/
def ControlTier.allowsControlShift : ControlTier → Bool
  | .predicative => false
  | .logophoric  => true

/-- [−human] PRO is compatible with predicative control but
    incompatible with logophoric control (81).

    In predicative control, PRO is bound by a simple λ-operator;
    neither the binder nor the bindee carries any inherent semantic
    feature. In logophoric control, PRO is bound by pro_x/pro_y,
    which is mapped to the AUTHOR/ADDRESSEE function; since the
    latter is only defined for humans, the former will be too. -/
def ControlTier.allowsNonhumanPRO : ControlTier → Bool
  | .predicative => true
  | .logophoric  => false

/-- Implicit control (controller not syntactically present) is
    available only under logophoric control (93).

    EC verbs require the controller to be syntactically present
    (condition on syntactic predication (90)). PC verbs allow
    implicit controllers because the AUTHOR/ADDRESSEE coordinate
    is discourse-anchored, not predication-dependent. -/
def ControlTier.allowsImplicitControl : ControlTier → Bool
  | .predicative => false
  | .logophoric  => true

/-- Split control (two arguments jointly control PRO) is available
    only under logophoric control (Ch 5). -/
def ControlTier.allowsSplitControl : ControlTier → Bool
  | .predicative => false
  | .logophoric  => true

-- ════════════════════════════════════════════════════════════════
-- § 2: Predicate Classification
-- ════════════════════════════════════════════════════════════════

/-- @cite{landau-2015}'s predicate classification by complement type.

    (4) Predicates selecting untensed complements [−T] → nonattitude:
      (a) Implicative: avoid, dare, manage, remember, ...
      (b) Aspectual: begin, continue, finish, start, stop
      (c) Modal: have, is able, may, must, need, should
      (d) Evaluative: bold, crazy, kind, rude, silly, smart

    (5) Predicates selecting tensed complements [+T] → attitude:
      (a) Factive: dislike, glad, hate, regret, sorry, ...
      (b) Propositional: affirm, believe, claim, declare, say, think
      (c) Desiderative: agree, choose, decide, hope, intend, want, ...
      (d) Interrogative: ask, guess, inquire, know, wonder

    Under the TTC, (4) maps to predicative control and (5) to logophoric. -/
inductive LandauPredicateClass where
  | implicative    -- (4a) nonattitude, EC
  | aspectual      -- (4b) nonattitude, EC
  | modal          -- (4c) nonattitude, EC
  | evaluative     -- (4d) nonattitude, EC
  | factive        -- (5a) attitude, PC
  | propositional  -- (5b) attitude, PC
  | desiderative   -- (5c) attitude, PC
  | interrogative  -- (5d) attitude, PC
  deriving DecidableEq, BEq, Repr

/-- Map predicate class to control tier. -/
def LandauPredicateClass.controlTier : LandauPredicateClass → ControlTier
  | .implicative | .aspectual | .modal | .evaluative => .predicative
  | .factive | .propositional | .desiderative | .interrogative => .logophoric

/-- Nonattitude predicates force exhaustive control. -/
theorem implicative_ec :
    LandauPredicateClass.implicative.controlTier.allowsPartialControl = false := rfl
theorem aspectual_ec :
    LandauPredicateClass.aspectual.controlTier.allowsPartialControl = false := rfl

/-- Attitude predicates allow partial control. -/
theorem desiderative_pc :
    LandauPredicateClass.desiderative.controlTier.allowsPartialControl = true := rfl
theorem propositional_pc :
    LandauPredicateClass.propositional.controlTier.allowsPartialControl = true := rfl

-- ════════════════════════════════════════════════════════════════
-- § 3: The OC-NC Generalization
-- ════════════════════════════════════════════════════════════════

/-- The OC-NC generalization ((70) in @cite{landau-2015}):

    "[+Agr] blocks logophoric control but not predicative control."

    In nonattitude complements (predicative), embedded inflection is
    compatible with control because predication does not depend on
    Feature Transmission (see (60a) in @cite{landau-2015}).

    In attitude complements (logophoric), embedded inflection blocks
    control because variable binding REQUIRES Feature Transmission
    ((60b)), and [+Agr] valued by the embedded T preempts this. -/
def agrBlocksControl : ControlTier → Bool
  | .predicative => false  -- predication is NOT contingent on feature matching
  | .logophoric  => true   -- variable binding IS contingent on feature matching

/-- Predicative control survives in inflected complements. -/
theorem predicative_survives_agr :
    agrBlocksControl .predicative = false := rfl

/-- Logophoric control is blocked by inflected complements. -/
theorem logophoric_blocked_by_agr :
    agrBlocksControl .logophoric = true := rfl

-- ════════════════════════════════════════════════════════════════
-- § 4: Clause Classes
-- ════════════════════════════════════════════════════════════════

/-- @cite{landau-2004}'s finiteness scale, as recast in @cite{landau-2015}.

    The [±T] distinction is subsumed by the attitude/nonattitude distinction:
    - C-subjunctives (untensed, OC) → nonattitude → predicative control
    - F-subjunctives (tensed, non-OC possible) → attitude → logophoric control
    - Fully finite (indicative) → no control -/
inductive LandauClauseClass where
  | cSubjunctive   -- Untensed nonfinite, predicative control
  | fSubjunctive   -- Tensed nonfinite, logophoric control
  | finite          -- Fully finite, no control
  deriving DecidableEq, BEq, Repr

/-- Map clause class to control tier (when control obtains). -/
def LandauClauseClass.controlTier : LandauClauseClass → Option ControlTier
  | .cSubjunctive => some .predicative
  | .fSubjunctive => some .logophoric
  | .finite       => none

/-- Does a clause class exhibit OC? -/
def LandauClauseClass.hasOC : LandauClauseClass → Bool
  | .cSubjunctive => true
  | .fSubjunctive => false
  | .finite       => false

-- ════════════════════════════════════════════════════════════════
-- § 5: Table (80) — Empirical Contrasts
-- ════════════════════════════════════════════════════════════════

/-- The six empirical contrasts between the two types of control
    (table (80) in @cite{landau-2015}).

    Each contrast shows a property that aligns with exactly one
    control tier. The "✓" entries indicate the tier where the
    property is available; the "*" entries indicate the tier where
    it is blocked.

    | Property               | Predicative | Logophoric |
    |------------------------|:-----------:|:----------:|
    | Inflected complement   |     ✓       |     *      |
    | [−human] PRO           |     ✓       |     *      |
    | Implicit control       |     *       |     ✓      |
    | Control shift          |     *       |     ✓      |
    | Partial control        |     *       |     ✓      |
    | Split control          |     *       |     ✓      | -/
structure TTCContrast where
  name : String
  /-- Available under predicative control? -/
  predicative : Bool
  /-- Available under logophoric control? -/
  logophoric : Bool
  deriving DecidableEq, BEq, Repr

def ttcContrasts : List TTCContrast :=
  [ ⟨"inflected complement", true,  false⟩
  , ⟨"[−human] PRO",         true,  false⟩
  , ⟨"implicit control",     false, true⟩
  , ⟨"control shift",        false, true⟩
  , ⟨"partial control",      false, true⟩
  , ⟨"split control",        false, true⟩ ]

/-- Every contrast in table (80) is derived from `ControlTier` properties. -/
theorem inflected_complement_predicative :
    (agrBlocksControl .predicative = false) ∧ (agrBlocksControl .logophoric = true) :=
  ⟨rfl, rfl⟩

theorem nonhuman_pro_predicative :
    ControlTier.allowsNonhumanPRO .predicative = true
    ∧ ControlTier.allowsNonhumanPRO .logophoric = false := ⟨rfl, rfl⟩

theorem implicit_control_logophoric :
    ControlTier.allowsImplicitControl .predicative = false
    ∧ ControlTier.allowsImplicitControl .logophoric = true := ⟨rfl, rfl⟩

theorem control_shift_logophoric :
    ControlTier.allowsControlShift .predicative = false
    ∧ ControlTier.allowsControlShift .logophoric = true := ⟨rfl, rfl⟩

theorem partial_control_logophoric :
    ControlTier.allowsPartialControl .predicative = false
    ∧ ControlTier.allowsPartialControl .logophoric = true := ⟨rfl, rfl⟩

theorem split_control_logophoric :
    ControlTier.allowsSplitControl .predicative = false
    ∧ ControlTier.allowsSplitControl .logophoric = true := ⟨rfl, rfl⟩

/-- All six contrasts are systematically derived from the TTC:
    the first two are predicative-only, the last four are logophoric-only.
    This is the central empirical prediction of the book. -/
theorem all_contrasts_derived :
    -- predicative-only properties
    (agrBlocksControl .predicative = false ∧ agrBlocksControl .logophoric = true)
    ∧ (ControlTier.allowsNonhumanPRO .predicative = true
       ∧ ControlTier.allowsNonhumanPRO .logophoric = false)
    -- logophoric-only properties
    ∧ (ControlTier.allowsImplicitControl .predicative = false
       ∧ ControlTier.allowsImplicitControl .logophoric = true)
    ∧ (ControlTier.allowsControlShift .predicative = false
       ∧ ControlTier.allowsControlShift .logophoric = true)
    ∧ (ControlTier.allowsPartialControl .predicative = false
       ∧ ControlTier.allowsPartialControl .logophoric = true)
    ∧ (ControlTier.allowsSplitControl .predicative = false
       ∧ ControlTier.allowsSplitControl .logophoric = true) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- ════════════════════════════════════════════════════════════════
-- § 6: Cross-Linguistic BVA Syncretism
-- ════════════════════════════════════════════════════════════════

/-- Cross-linguistic syncretism among BVA forms.

    Records whether each BVA context uses the same form as the
    referential (free) pronoun. "=" means syncretic with the referential
    pronoun; "×" means a distinct form is used.

    This typology is used by @cite{ostrove-2026} (table 92) to
    classify languages by their minimal pronoun inventory. -/
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
-- § 7: Copy Control Typology
-- ════════════════════════════════════════════════════════════════

/-- Types of copy control (@cite{polinsky-potsdam-2006}).

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

/-- Profile for each copy control type.

    `showsOC`: whether this type demonstrates the full OC signature
    (bound variable interpretation, exhaustive binding). For non-obligatory
    types, `false` means "not demonstrated," not necessarily "confirmed absent."

    | Type                    | showsOC | attOnly | scopeOp | focus |
    |-------------------------|:-------:|:-------:|:-------:|:-----:|
    | fullCopy                |    -    |    -    |    -    |   ✓   |
    | logophoricPronominal    |    -    |    ✓    |    -    |   ✓   |
    | scopeSensitivePronominal|    -    |    -    |    ✓    |   ✓   |
    | obligatoryPronominal    |    ✓    |    -    |    -    |   -   | -/
def copyControlProfile : CopyControlType → CopyControlProfile
  --                                        showsOC  attOnly  scopeOp  focus
  | .fullCopy                 => ⟨.fullCopy,                 false, false, false, true⟩
  | .logophoricPronominal     => ⟨.logophoricPronominal,     false, true,  false, true⟩
  | .scopeSensitivePronominal => ⟨.scopeSensitivePronominal, false, false, true,  true⟩
  | .obligatoryPronominal     => ⟨.obligatoryPronominal,     true,  false, false, false⟩

-- ════════════════════════════════════════════════════════════════
-- § 8: Exempt Anaphors
-- ════════════════════════════════════════════════════════════════

/-- Exempt anaphors (@cite{pollard-sag-1992}): reflexive forms used
    outside their canonical binding domain (Condition A domain).

    Key constraint: exempt anaphors cannot have quantified antecedents. -/
structure ExemptAnaphorProfile where
  /-- Exempt anaphors available in this language -/
  hasExemptAnaphors : Bool
  /-- Can exempt anaphors have quantified antecedents? -/
  allowsQuantifiedAntecedent : Bool
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 9: Control Derivation
-- ════════════════════════════════════════════════════════════════

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

end Phenomena.Control.Studies.Landau2015
