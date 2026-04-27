import Linglib.Theories.Syntax.Minimalist.MinimalPronoun
import Linglib.Theories.Semantics.Verb.VerbEntry
import Linglib.Phenomena.Complementation.Typology
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Landau (2015): A Two-Tiered Theory of Control
@cite{landau-2015} @cite{landau-2004} @cite{landau-2013}

MIT Press. ISBN 978-0-262-02885-1.

OC in complement clauses divides into two subtypes:
- **Predicative control**: nonattitude complements, PRO moves to Spec,Fin,
  control via syntactic predication
- **Logophoric control**: attitude complements, C^OC projects a perspectival
  coordinate, control via predication + variable binding

## Key Definitions

- `ControlTier`: The two tiers of control (predicative vs. logophoric)
- `LandauPredicateClass`: Eight predicate classes mapped to control tiers
- `LandauClauseClass`: Finiteness scale (C-subjunctive, F-subjunctive, finite)
- `FeatureTransmissionAsymmetry`: The mechanism deriving `agrBlocksControl`
- `agrBlocksControl`: The OC-NC generalization — [+Agr] blocks logophoric
  control but not predicative control (70)
- `TTCContrast`: The six empirical contrasts between the two tiers (table (80))
- `derivedLandauClass`: Maps VerbCore fields to Landau predicate classes
- `DeSeReading`: Object control *de se*/*de te* distinction (table (36))

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

namespace Landau2015

open Minimalist.MinimalPronoun
open Core.Verbs (VerbCore ControlType Attitude ComplementType)

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
  deriving DecidableEq, Repr

/-- Logophoric control corresponds to attitude complements. -/
def ControlTier.isAttitude : ControlTier → Bool
  | .predicative => false
  | .logophoric  => true

/-- Condition on syntactic predication ((90) in @cite{landau-2015}):
    "The argument predicated of must be syntactically represented."

    In predicative control, the controller must be syntactically present
    because predication is a syntactic relation requiring two syntactically
    represented terms (the referential argument and the predicate).

    In logophoric control, the AUTHOR/ADDRESSEE coordinate is
    discourse-anchored, not predication-dependent, so the controller
    may remain implicit. -/
def ControlTier.requiresSyntacticController : ControlTier → Bool
  | .predicative => true
  | .logophoric  => false

/-- [−human] PRO is compatible with predicative control but
    incompatible with logophoric control ((81) in @cite{landau-2015}).

    In predicative control, PRO is bound by a simple λ-operator;
    neither the binder nor the bindee carries any inherent semantic
    feature. In logophoric control, PRO is bound by pro_x/pro_y,
    which is mapped to the AUTHOR/ADDRESSEE function; since the
    latter is only defined for humans, the former will be too.

    This is the negation of `isAttitude`: only logophoric control
    (attitude contexts) imposes a humanness requirement. -/
def ControlTier.allowsNonhumanPRO : ControlTier → Bool
  | .predicative => true
  | .logophoric  => false

/-! Five properties of control are all unified by the logophoric tier.
    Partial control, obligatory *de se*, control shift, implicit control,
    and split control are all available under logophoric control and blocked
    under predicative control. This reflects the paper's central claim that
    these five properties derive from the same underlying mechanism:
    variable binding of a perspectival coordinate.

    Rather than defining five identical functions, we derive each as
    `isAttitude` and prove they agree. -/

/-- Partial control is available only under logophoric control.
    Predicative control forces exhaustive control (EC).
    @cite{landau-2015} Ch 5, §5.1 -/
def ControlTier.allowsPartialControl := ControlTier.isAttitude

/-- Obligatory *de se* arises only under logophoric control.
    Predicative contexts are free of the *de se* entailment.
    @cite{landau-2015} §3.4 -/
def ControlTier.obligatoryDeSe := ControlTier.isAttitude

/-- Control shift (from subject to object controller) is available
    only under logophoric control. Predicative control enters a biunique
    predication relation that no other DP can saturate.
    @cite{landau-2015} §4.3 -/
def ControlTier.allowsControlShift := ControlTier.isAttitude

/-- Implicit control is the complement of requiring a syntactic controller.
    Derived from the condition on syntactic predication (90). -/
def ControlTier.allowsImplicitControl := ControlTier.isAttitude

/-- Split control (two arguments jointly control PRO) is available
    only under logophoric control.
    @cite{landau-2015} Ch 5, §5.2 -/
def ControlTier.allowsSplitControl := ControlTier.isAttitude

/-- Implicit control derives from condition (90): predicative control
    requires a syntactically present controller, so `allowsImplicitControl`
    is the negation of `requiresSyntacticController`. -/
theorem implicit_control_from_predication_condition (tier : ControlTier) :
    tier.allowsImplicitControl = !tier.requiresSyntacticController := by
  cases tier <;> rfl

/-- [−human] PRO derives from the logophoric mechanism:
    `allowsNonhumanPRO` is the negation of `isAttitude`. -/
theorem nonhuman_pro_from_attitude (tier : ControlTier) :
    tier.allowsNonhumanPRO = !tier.isAttitude := by
  cases tier <;> rfl

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

    Under the TTC, (4) maps to predicative control and (5) to logophoric.

    Note: (4d) evaluative predicates are *adjectives*, not verbs. No
    evaluative verbs exist in the English Fragment; this class is currently
    unreachable via `derivedLandauClass`. -/
inductive LandauPredicateClass where
  | implicative    -- (4a) nonattitude, EC
  | aspectual      -- (4b) nonattitude, EC
  | modal          -- (4c) nonattitude, EC
  | evaluative     -- (4d) nonattitude, EC (adjectives only)
  | factive        -- (5a) attitude, PC
  | propositional  -- (5b) attitude, PC
  | desiderative   -- (5c) attitude, PC
  | interrogative  -- (5d) attitude, PC
  deriving DecidableEq, Repr

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
-- § 3: Feature Transmission Asymmetry (60)
-- ════════════════════════════════════════════════════════════════

/-- The Feature Transmission asymmetry ((60) in @cite{landau-2015}).

    This is the single most important mechanism in the TTC. It is the
    reason why [+Agr] blocks logophoric control but not predicative
    control (the OC-NC generalization).

    (60a) The formation of a predication relation is *not* contingent
          on feature matching between the subject and the predicate.
    (60b) The formation of a variable binding relation *is* contingent
          on feature matching between the binder and the pronominal variable.

    The asymmetry is independently motivated: predication tolerates
    φ-feature mismatches (Icelandic quirky constructions, (63)), while
    variable binding requires φ-agreement between binder and bindee
    (@cite{heim-2008}, @cite{kratzer-2009}). -/
structure FeatureTransmissionAsymmetry where
  /-- (60a): Predication does NOT require feature matching. -/
  predicationContingentOnFeatureMatch : Bool
  /-- (60b): Variable binding DOES require feature matching. -/
  variableBindingContingentOnFeatureMatch : Bool

/-- The empirically motivated Feature Transmission asymmetry. -/
def ftAsymmetry : FeatureTransmissionAsymmetry where
  predicationContingentOnFeatureMatch := false
  variableBindingContingentOnFeatureMatch := true

-- ════════════════════════════════════════════════════════════════
-- § 4: The OC-NC Generalization (derived)
-- ════════════════════════════════════════════════════════════════

/-- The OC-NC generalization ((70) in @cite{landau-2015}):

    "[+Agr] blocks logophoric control but not predicative control."

    This is now DERIVED from the Feature Transmission asymmetry (60):
    - Predicative control uses predication → not contingent on feature
      matching (60a) → [+Agr] cannot block it
    - Logophoric control uses variable binding → contingent on feature
      matching (60b) → [+Agr] preempts Feature Transmission → blocks it -/
def agrBlocksControl : ControlTier → Bool
  | .predicative => ftAsymmetry.predicationContingentOnFeatureMatch
  | .logophoric  => ftAsymmetry.variableBindingContingentOnFeatureMatch

/-- Predicative control survives in inflected complements. -/
theorem predicative_survives_agr :
    agrBlocksControl .predicative = false := rfl

/-- Logophoric control is blocked by inflected complements. -/
theorem logophoric_blocked_by_agr :
    agrBlocksControl .logophoric = true := rfl

/-- The OC-NC generalization is derived from the Feature Transmission
    asymmetry, not stipulated. -/
theorem agr_blocks_derived_from_ft :
    (agrBlocksControl .predicative = ftAsymmetry.predicationContingentOnFeatureMatch)
    ∧ (agrBlocksControl .logophoric = ftAsymmetry.variableBindingContingentOnFeatureMatch) :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 5: Clause Classes
-- ════════════════════════════════════════════════════════════════

/-- @cite{landau-2004}'s finiteness scale, as recast in @cite{landau-2015}.

    The [±T] distinction is subsumed by the attitude/nonattitude distinction:
    - C-subjunctives (untensed, [−T]) → nonattitude → predicative control
    - F-subjunctives (tensed, [+T,−Agr]) → attitude → logophoric control
    - Fully finite ([+T,+Agr]) → no control (OC-NC generalization)

    F-subjunctives DO permit OC (logophoric). Whether OC is realized
    depends on [±Agr]: [+Agr] blocks logophoric control per the OC-NC
    generalization. Greek controlled subjunctives ([+T,−Agr]) show OC;
    Greek indicatives ([+T,+Agr]) do not. -/
inductive LandauClauseClass where
  | cSubjunctive   -- Untensed nonfinite, predicative control
  | fSubjunctive   -- Tensed nonfinite, logophoric control
  | finite          -- Fully finite, no control
  deriving DecidableEq, Repr

/-- Map clause class to control tier (when control obtains). -/
def LandauClauseClass.controlTier : LandauClauseClass → Option ControlTier
  | .cSubjunctive => some .predicative
  | .fSubjunctive => some .logophoric
  | .finite       => none

/-- Whether a clause class structurally permits OC.

    Both C-subjunctives and F-subjunctives permit OC. F-subjunctives
    permit logophoric OC when [−Agr]; this OC is blocked by [+Agr]
    per the OC-NC generalization. Fully finite clauses ([+T,+Agr])
    never permit OC.

    See `hasOCWithAgr` for the Agr-sensitive version. -/
def LandauClauseClass.permitsOC : LandauClauseClass → Bool
  | .cSubjunctive => true
  | .fSubjunctive => true   -- logophoric OC, blocked only by [+Agr]
  | .finite       => false

/-- Whether OC is realized given Agr status.

    Composes the clause class with the OC-NC generalization:
    - C-subjunctives: always OC (predicative, Agr-independent)
    - F-subjunctives [−Agr]: OC (logophoric)
    - F-subjunctives [+Agr]: no OC (logophoric blocked by Agr)
    - Fully finite: no OC -/
def LandauClauseClass.hasOCWithAgr (c : LandauClauseClass) (hasAgr : Bool) : Bool :=
  match c.controlTier with
  | none => false
  | some tier => c.permitsOC && (!hasAgr || !agrBlocksControl tier)

/-- C-subjunctives have OC regardless of Agr. -/
theorem cSubjunctive_oc_any_agr (agr : Bool) :
    LandauClauseClass.cSubjunctive.hasOCWithAgr agr = true := by
  cases agr <;> rfl

/-- F-subjunctives have OC when [−Agr]. -/
theorem fSubjunctive_oc_without_agr :
    LandauClauseClass.fSubjunctive.hasOCWithAgr false = true := rfl

/-- F-subjunctives lose OC when [+Agr] (the OC-NC generalization). -/
theorem fSubjunctive_no_oc_with_agr :
    LandauClauseClass.fSubjunctive.hasOCWithAgr true = false := rfl

/-- Fully finite clauses never have OC. -/
theorem finite_no_oc (agr : Bool) :
    LandauClauseClass.finite.hasOCWithAgr agr = false := by
  cases agr <;> rfl

-- ════════════════════════════════════════════════════════════════
-- § 6: Table (80) — Empirical Contrasts
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
  deriving DecidableEq, Repr, Inhabited

/-- The six contrasts from table (80), encoded as data. -/
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

/-- The `ttcContrasts` data agrees with the derived `ControlTier` properties.
    Each contrast's Bool pair matches the corresponding tier function. -/
theorem ttcContrasts_consistent :
    -- Row 0: inflected complement ↔ ¬agrBlocksControl
    ((!agrBlocksControl .predicative) = (ttcContrasts[0]!.predicative))
    ∧ ((!agrBlocksControl .logophoric) = (ttcContrasts[0]!.logophoric))
    -- Row 1: [−human] PRO ↔ allowsNonhumanPRO
    ∧ (ControlTier.allowsNonhumanPRO .predicative = ttcContrasts[1]!.predicative)
    ∧ (ControlTier.allowsNonhumanPRO .logophoric = ttcContrasts[1]!.logophoric)
    -- Row 2: implicit control ↔ allowsImplicitControl
    ∧ (ControlTier.allowsImplicitControl .predicative = ttcContrasts[2]!.predicative)
    ∧ (ControlTier.allowsImplicitControl .logophoric = ttcContrasts[2]!.logophoric)
    -- Row 3: control shift ↔ allowsControlShift
    ∧ (ControlTier.allowsControlShift .predicative = ttcContrasts[3]!.predicative)
    ∧ (ControlTier.allowsControlShift .logophoric = ttcContrasts[3]!.logophoric)
    -- Row 4: partial control ↔ allowsPartialControl
    ∧ (ControlTier.allowsPartialControl .predicative = ttcContrasts[4]!.predicative)
    ∧ (ControlTier.allowsPartialControl .logophoric = ttcContrasts[4]!.logophoric)
    -- Row 5: split control ↔ allowsSplitControl
    ∧ (ControlTier.allowsSplitControl .predicative = ttcContrasts[5]!.predicative)
    ∧ (ControlTier.allowsSplitControl .logophoric = ttcContrasts[5]!.logophoric) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- EC verbs resist impersonal passives ((98) in @cite{landau-2015}).

    This is a direct consequence of (90): predicative control requires a
    syntactically present controller, and impersonal passives suppress the
    external argument. PC verbs allow impersonal passives because logophoric
    control does not require a syntactically present controller.

    Cross-linguistic evidence: Hebrew (99), German (96a, 100), Dutch (101),
    Russian (102). -/
theorem ec_resists_impersonal_passives :
    ControlTier.requiresSyntacticController .predicative = true
    ∧ ControlTier.requiresSyntacticController .logophoric = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 7: Cross-Linguistic BVA Syncretism
-- ════════════════════════════════════════════════════════════════

/-- Cross-linguistic syncretism among BVA forms.

    Records whether each BVA context uses the same form as the
    referential (free) pronoun. "=" means syncretic with the referential
    pronoun; "×" means a distinct form is used.

    Used by @cite{ostrove-2026} (table 92) and grounded in the minimal
    pronoun approach of @cite{kratzer-2009} and @cite{safir-2014}. -/
structure BVASyncretism where
  language : String
  /-- Is the reflexive form identical to the referential pronoun? -/
  reflexiveEqReferential : Bool
  /-- Is the controlled subject form identical to the referential pronoun? -/
  controlledEqReferential : Bool
  /-- Is the bound variable pronoun identical to the referential pronoun? -/
  boundVarEqReferential : Bool
  deriving DecidableEq, Repr

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
-- § 8: Copy Control Typology
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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

/-- Profile for each copy control type. -/
def copyControlProfile : CopyControlType → CopyControlProfile
  | .fullCopy                 => ⟨.fullCopy,                 false, false, false, true⟩
  | .logophoricPronominal     => ⟨.logophoricPronominal,     false, true,  false, true⟩
  | .scopeSensitivePronominal => ⟨.scopeSensitivePronominal, false, false, true,  true⟩
  | .obligatoryPronominal     => ⟨.obligatoryPronominal,     true,  false, false, false⟩

-- ════════════════════════════════════════════════════════════════
-- § 9: Exempt Anaphors
-- ════════════════════════════════════════════════════════════════

/-- Exempt anaphors (@cite{pollard-sag-1992}): reflexive forms used
    outside their canonical binding domain (Condition A domain).

    Key constraint: exempt anaphors cannot have quantified antecedents. -/
structure ExemptAnaphorProfile where
  /-- Exempt anaphors available in this language -/
  hasExemptAnaphors : Bool
  /-- Can exempt anaphors have quantified antecedents? -/
  allowsQuantifiedAntecedent : Bool
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 10: Control Derivation
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
  deriving DecidableEq, Repr

/-- Movement predicts exempt anaphors are UNAVAILABLE with quantified
    controllers. Base-generation predicts they ARE available. -/
def predictsExemptWithQuantifiedController : ControlDerivation → Bool
  | .baseGeneration => true
  | .movement       => false

-- ════════════════════════════════════════════════════════════════
-- § 11: De Se / De Te in Object Control (table (36))
-- ════════════════════════════════════════════════════════════════

/-- The two logophoric readings of OC PRO under attitude predicates
    (table (36) in @cite{landau-2015}).

    Under logophoric control, PRO is bound by a projected coordinate
    of the embedded context of evaluation. Which coordinate is
    projected depends on the object control verb subclass:
    - Psychological verbs (*convince*, *persuade*, *tempt*) project
      the AUTHOR coordinate → obligatory *de se*
    - Communicative verbs (*tell*, *ask*, *recommend*) project
      the ADDRESSEE coordinate → obligatory *de te* -/
inductive DeSeReading where
  /-- PRO = AUTHOR(i'): attitude holder's identification of self -/
  | deSe
  /-- PRO = ADDRESSEE(i'): attitude holder's identification of addressee -/
  | deTe
  deriving DecidableEq, Repr

/-- Object control verb subclasses (table (36)). -/
inductive ObjectControlSubclass where
  /-- Psychological verbs: *convince*, *persuade*, *dissuade*, *tempt* -/
  | psychological
  /-- Communicative verbs: *tell*, *ask*, *urge*, *recommend* -/
  | communicative
  deriving DecidableEq, Repr

/-- Map object control subclass to its logophoric reading.
    Psychological verbs bind the AUTHOR coordinate (*de se*);
    communicative verbs bind the ADDRESSEE coordinate (*de te*). -/
def objectControlReading : ObjectControlSubclass → DeSeReading
  | .psychological => .deSe
  | .communicative => .deTe

theorem psychological_deSe :
    objectControlReading .psychological = .deSe := rfl

theorem communicative_deTe :
    objectControlReading .communicative = .deTe := rfl

-- ════════════════════════════════════════════════════════════════
-- § 12: Derived Landau Class from VerbCore
-- ════════════════════════════════════════════════════════════════

/-- Derive @cite{landau-2015}'s predicate class from VerbCore fields.

    This creates a bridge from Fragment verb entries to the TTC by
    deriving the predicate classification from existing semantic fields
    rather than storing it independently.

    Returns `none` when the classification cannot be determined from
    the available fields (e.g., `try` has no `implicative`,
    `attitude`, or `cosType`).

    Mapping:
    - `cosType` present → `.aspectual` (begin, stop, continue, ...)
    - `implicative` present → `.implicative` (manage, fail, ...)
    - `causative` present → `.implicative` (force, cause — implicative
      causatives in Landau's (4a))
    - `factivePresup` and attitude → `.factive` (regret, know, ...)
    - `attitude.doxastic` → `.propositional` (believe, think, ...)
    - `attitude.preferential` → `.desiderative` (want, hope, ...)
    - `takesQuestionBase` without attitude → `.interrogative` (wonder, ask) -/
def derivedLandauClass (v : VerbCore) : Option LandauPredicateClass :=
  if v.cosType.isSome then some .aspectual
  else if v.implicative.isSome then some .implicative
  else if v.causative.isSome then some .implicative
  else if v.factivePresup then some .factive
  else if v.takesQuestionBase && v.attitude.isNone then some .interrogative
  else match v.attitude with
    | some (.doxastic _)     => some .propositional
    | some (.preferential _) => some .desiderative
    | none                   => none

/-- Derive control tier from VerbCore fields.

    A verb induces logophoric control iff it selects an attitude
    complement — detected by the presence of `attitude`,
    `factivePresup`, or `takesQuestionBase`. Otherwise it induces
    predicative control.

    Returns `none` for verbs that are not control verbs. -/
def derivedControlTier (v : VerbCore) : Option ControlTier :=
  if v.controlType == ControlType.none && v.altControlType == ControlType.none then Option.none
  else match derivedLandauClass v with
    | some cls => some cls.controlTier
    | none =>
      -- Fallback: if we can't determine the Landau class but the verb
      -- is a control verb, check for attitude markers directly
      if v.attitude.isSome || v.factivePresup || v.takesQuestionBase
      then some .logophoric
      else some .predicative

-- ════════════════════════════════════════════════════════════════
-- § 13: Per-Verb Verification Theorems
-- ════════════════════════════════════════════════════════════════

section VerbVerification
open Fragments.English.Predicates.Verbal

-- Predicative (EC) verbs: derived class → predicative tier

/-- "stop" (CoS cessation) → aspectual → predicative -/
theorem stop_aspectual :
    derivedLandauClass stop.toVerbCore = some .aspectual := rfl

/-- "start" (CoS inception) → aspectual → predicative -/
theorem start_aspectual :
    derivedLandauClass start.toVerbCore = some .aspectual := rfl

/-- "begin" (CoS inception) → aspectual → predicative -/
theorem begin_aspectual :
    derivedLandauClass begin_.toVerbCore = some .aspectual := rfl

/-- "continue" (CoS continuation) → aspectual → predicative -/
theorem continue_aspectual :
    derivedLandauClass continue_.toVerbCore = some .aspectual := rfl

/-- "manage" (positive implicative) → implicative → predicative -/
theorem manage_implicative :
    derivedLandauClass manage.toVerbCore = some .implicative := rfl

/-- "fail" (negative implicative) → implicative → predicative -/
theorem fail_implicative :
    derivedLandauClass fail.toVerbCore = some .implicative := rfl

/-- "remember" (positive implicative) → implicative → predicative -/
theorem remember_implicative :
    derivedLandauClass remember.toVerbCore = some .implicative := rfl

/-- "forget" (negative implicative) → implicative → predicative -/
theorem forget_implicative :
    derivedLandauClass forget.toVerbCore = some .implicative := rfl

/-- "force" (coercive causative) → implicative → predicative -/
theorem force_implicative :
    derivedLandauClass force.toVerbCore = some .implicative := rfl

-- Logophoric (PC) verbs: derived class → logophoric tier

/-- "want" (preferential attitude) → desiderative → logophoric -/
theorem want_desiderative :
    derivedLandauClass want.toVerbCore = some .desiderative := rfl

/-- "hope" (preferential attitude) → desiderative → logophoric -/
theorem hope_desiderative :
    derivedLandauClass hope.toVerbCore = some .desiderative := rfl

/-- "promise" (preferential attitude) → desiderative → logophoric.
    Previously unclassified; fixed by adding `attitude` to the
    Fragment entry per @cite{landau-2015} (5c). -/
theorem promise_desiderative :
    derivedLandauClass promise.toVerbCore = some .desiderative := rfl

/-- "persuade" (preferential attitude, object control) → desiderative → logophoric.
    Previously unclassified; fixed by adding `attitude` per
    @cite{landau-2015} table (36). -/
theorem persuade_desiderative :
    derivedLandauClass persuade.toVerbCore = some .desiderative := rfl

/-- "regret" (factive) → factive → logophoric -/
theorem regret_factive :
    derivedLandauClass regret.toVerbCore = some .factive := rfl

/-- "know" (factive + question) → factive → logophoric -/
theorem know_factive :
    derivedLandauClass know.toVerbCore = some .factive := rfl

/-- "believe" (doxastic attitude) → propositional → logophoric -/
theorem believe_propositional :
    derivedLandauClass believe.toVerbCore = some .propositional := rfl

/-- "think" (doxastic attitude) → propositional → logophoric -/
theorem think_propositional :
    derivedLandauClass think.toVerbCore = some .propositional := rfl

/-- "wonder" (question-embedding, non-attitude) → interrogative → logophoric -/
theorem wonder_interrogative :
    derivedLandauClass wonder.toVerbCore = some .interrogative := rfl

-- Negative test: verbs that should NOT be classifiable

/-- "try" has no cosType, implicative, causative, factivePresup,
    takesQuestionBase, or attitude. It cannot be classified by
    `derivedLandauClass`. This is correct: "try" is not implicative (trying
    doesn't entail succeeding) and not clearly attitudinal. -/
theorem try_unclassifiable :
    derivedLandauClass try_.toVerbCore = none := rfl

-- Control tier verification: derived tier matches expected tier

theorem stop_predicative_tier :
    (derivedLandauClass stop.toVerbCore).map (·.controlTier) = some .predicative := rfl

theorem manage_predicative_tier :
    (derivedLandauClass manage.toVerbCore).map (·.controlTier) = some .predicative := rfl

theorem want_logophoric_tier :
    (derivedLandauClass want.toVerbCore).map (·.controlTier) = some .logophoric := rfl

theorem regret_logophoric_tier :
    (derivedLandauClass regret.toVerbCore).map (·.controlTier) = some .logophoric := rfl

theorem believe_logophoric_tier :
    (derivedLandauClass believe.toVerbCore).map (·.controlTier) = some .logophoric := rfl

theorem wonder_logophoric_tier :
    (derivedLandauClass wonder.toVerbCore).map (·.controlTier) = some .logophoric := rfl

theorem promise_logophoric_tier :
    (derivedLandauClass promise.toVerbCore).map (·.controlTier) = some .logophoric := rfl

theorem persuade_logophoric_tier :
    (derivedLandauClass persuade.toVerbCore).map (·.controlTier) = some .logophoric := rfl

-- Object control de se/de te: per-verb bridge

/-- "persuade" is a psychological object control verb → de se (table (36)). -/
theorem persuade_psychological_deSe :
    objectControlReading .psychological = .deSe := rfl

end VerbVerification

-- ════════════════════════════════════════════════════════════════
-- § 14: Noonan CTP → Landau Tier Bridge
-- ════════════════════════════════════════════════════════════════

open Phenomena.Complementation.Typology

/-- Map @cite{noonan-2007}'s CTP classes to @cite{landau-2015}'s
    control tiers.

    Noonan's twelve CTP classes partition into nonattitude (predicative)
    and attitude (logophoric) under the TTC:

    Predicative (nonattitude):
    - modal, phasal, achievement, negative → Landau's (4a-d)

    Logophoric (attitude):
    - utterance, propAttitude, commentative, knowledge,
      desiderative, manipulative → Landau's (5a-d)

    Remaining:
    - pretence: ambiguous (often nonattitude in control contexts)
    - perception: typically does not take controlled complements -/
def ctpToControlTier : CTPClass → Option ControlTier
  | .modal        => some .predicative
  | .phasal       => some .predicative
  | .achievement  => some .predicative
  | .negative     => some .predicative
  | .utterance    => some .logophoric
  | .propAttitude => some .logophoric
  | .commentative => some .logophoric
  | .knowledge    => some .logophoric
  | .desiderative => some .logophoric
  | .manipulative => some .logophoric
  | .pretence     => none   -- ambiguous
  | .perception   => none   -- typically no control complement

/-- Predicative CTP classes map to predicative control. -/
theorem phasal_predicative : ctpToControlTier .phasal = some .predicative := rfl
theorem achievement_predicative : ctpToControlTier .achievement = some .predicative := rfl
theorem modal_ctp_predicative : ctpToControlTier .modal = some .predicative := rfl

/-- Attitude CTP classes map to logophoric control. -/
theorem desiderative_ctp_logophoric : ctpToControlTier .desiderative = some .logophoric := rfl
theorem propAttitude_logophoric : ctpToControlTier .propAttitude = some .logophoric := rfl
theorem utterance_logophoric : ctpToControlTier .utterance = some .logophoric := rfl
theorem manipulative_logophoric : ctpToControlTier .manipulative = some .logophoric := rfl

/-- Map @cite{noonan-2007}'s CTP classes to @cite{landau-2015}'s
    predicate classes (where the mapping is unambiguous). -/
def ctpToLandauClass : CTPClass → Option LandauPredicateClass
  | .modal        => some .modal
  | .phasal       => some .aspectual
  | .achievement  => some .implicative
  | .negative     => some .implicative
  | .commentative => some .factive
  | .knowledge    => some .factive
  | .propAttitude => some .propositional
  | .utterance    => some .propositional
  | .desiderative => some .desiderative
  | .manipulative => some .desiderative
  | .pretence     => none
  | .perception   => none

/-- When both mappings are defined, they agree on the control tier. -/
theorem ctp_tier_consistent (c : CTPClass)
    (hTier : (ctpToControlTier c).isSome = true)
    (hClass : (ctpToLandauClass c).isSome = true) :
    ctpToControlTier c = (ctpToLandauClass c).map (·.controlTier) := by
  cases c <;> simp_all [ctpToControlTier, ctpToLandauClass, LandauPredicateClass.controlTier]

end Landau2015
