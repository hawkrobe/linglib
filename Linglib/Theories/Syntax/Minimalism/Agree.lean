/-
# Agree (Minimalist Feature Checking)


Formalization of Agree following @cite{chomsky-2000} and @cite{adger-2003}.

## The Agree Operation

Agree is the mechanism by which features are checked/valued:
1. A **probe** (head with unvalued feature) searches its c-command domain
2. It finds the closest **goal** (element with matching valued feature)
3. The probe's feature is valued by copying from the goal
4. Both features are then checked (and may delete at PF/LF)

## Architecture

This file contains the Agree *operation* and its structural conditions
(locality, activity, phase-boundedness, defective intervention). For
the feature *types* (PhiFeature, FeatureVal, etc.), see `Features.lean`.
For the *failure model* (what happens when Agree fails), see
`ObligatoryOperations.lean`. For the Case Filter, see `CaseFilter.lean`.

## Satisfaction Conditions

Standard Agree assumes a probe is satisfied by finding a matching valued
feature. @cite{deal-2024} and @cite{keine-2019} argue for richer conditions:
- **Feature match**: the standard case
- **Head encounter**: probe is satisfied by encountering a head of a
  particular category (e.g., Infl's probe stopped by transitive Voice)
- **Disjunctive**: probe is satisfied by ANY of several conditions

This captures e.g. Mam's Infl probe, which has satisfaction condition
[SAT: φ or Voice_TR] — it stops when it finds either matching
φ-features OR transitive Voice, whichever comes first.

-/

import Linglib.Theories.Syntax.Minimalism.Features
import Linglib.Theories.Syntax.Minimalism.Phase
import Linglib.Theories.Syntax.Minimalism.Probe

namespace Minimalism

open Core.Prominence

-- ============================================================================
-- § 1: Extended Lexical Items with Features
-- ============================================================================

/-- Extended LI with grammatical features

    This extends Harizanov's LI with Agree-relevant features.
    The original ⟨CAT, SEL⟩ handles selection; this adds φ, Case, etc. -/
structure ExtendedLI where
  base : LexicalItem        -- The base ⟨CAT, SEL⟩ structure
  features : FeatureBundle  -- Agree-relevant features
  deriving Repr

/-- Create an extended LI from a simple LI -/
def ExtendedLI.fromSimple (cat : Cat) (sel : SelStack) (feats : FeatureBundle) : ExtendedLI :=
  ⟨.simple cat sel, feats⟩

/-- Is this LI a probe (has unvalued features)? -/
def ExtendedLI.isProbe (li : ExtendedLI) : Bool :=
  li.features.any GramFeature.isUnvalued

/-- Is this LI a potential goal for a given feature type? -/
def ExtendedLI.isGoalFor (li : ExtendedLI) (ftype : FeatureVal) : Bool :=
  hasValuedFeature li.features ftype

-- ============================================================================
-- § 2: Agree Relation
-- ============================================================================

/-- A probe-goal pair for Agree -/
structure AgreeRelation where
  probe : SyntacticObject
  goal : SyntacticObject
  feature : FeatureVal      -- The feature type being checked
  probeFeatures : FeatureBundle
  goalFeatures : FeatureBundle

/-- The probe c-commands the goal within a given tree -/
def AgreeRelation.probeCommands (a : AgreeRelation) (root : SyntacticObject) : Prop :=
  cCommandsIn root a.probe a.goal

/-- The goal has the relevant valued feature -/
def AgreeRelation.goalHasFeature (a : AgreeRelation) : Bool :=
  hasValuedFeature a.goalFeatures a.feature

/-- The probe has the relevant unvalued feature -/
def AgreeRelation.probeNeedsFeature (a : AgreeRelation) : Bool :=
  hasUnvaluedFeature a.probeFeatures a.feature

/-- Valid Agree: probe c-commands goal (in tree), probe has unvalued, goal has valued -/
def validAgree (a : AgreeRelation) (root : SyntacticObject) : Prop :=
  a.probeCommands root ∧
  a.probeNeedsFeature = true ∧
  a.goalHasFeature = true

-- ============================================================================
-- § 3: Locality (Closest Goal)
-- ============================================================================

/-- X intervenes between probe and goal (within tree `root`) iff:
    - probe c-commands X
    - X c-commands goal
    - X has a matching valued feature -/
def intervenes (root : SyntacticObject) (probe x goal : SyntacticObject)
    (xFeatures : FeatureBundle) (ftype : FeatureVal) : Prop :=
  cCommandsIn root probe x ∧
  cCommandsIn root x goal ∧
  hasValuedFeature xFeatures ftype = true

/-- Goal is the closest matching goal for probe.

    **Caveat**: this definition existentially quantifies over feature
    bundles (`∃ xFeats`), meaning ANY structurally intervening node
    blocks regardless of its actual features. This is strictly stronger
    than necessary — a V° with no phi-features would block a phi-probe.
    For derivations that need to distinguish nodes by their actual
    features, use `closestGoalWith` (propositional, with feature
    assignment) or `closestGoalB` (boolean, with matching predicate). -/
def closestGoal (a : AgreeRelation) (root : SyntacticObject) : Prop :=
  validAgree a root ∧
  ¬∃ (x : SyntacticObject) (xFeats : FeatureBundle),
    isTermOf x root ∧
    x ≠ a.goal ∧
    intervenes root a.probe x a.goal xFeats a.feature

-- ============================================================================
-- § 3b: Feature-Aware Locality
-- ============================================================================

/-- A feature assignment maps each syntactic object in a tree to its
    actual feature bundle. -/
abbrev FeatureAssignment := SyntacticObject → FeatureBundle

/-- Goal is the closest matching goal for probe, given a feature
    assignment that determines each node's actual features.

    Compared to `closestGoal`: the existential `∃ xFeats` is replaced
    by `fa x`, so only nodes whose ACTUAL features match can intervene.
    This correctly models Agree: a V° (no phi-features) should not
    block T°'s phi-probe even if V° is structurally between T° and the
    subject DP. `closestGoal` is strictly stronger (see
    `closestGoal_implies_closestGoalWith`). -/
def closestGoalWith (a : AgreeRelation) (root : SyntacticObject)
    (fa : FeatureAssignment) : Prop :=
  validAgree a root ∧
  ¬∃ x, isTermOf x root ∧ x ≠ a.goal ∧
    intervenes root a.probe x a.goal (fa x) a.feature

/-- `closestGoal` (existential over features) implies `closestGoalWith`
    (fixed feature assignment): if no node with ANY features intervenes,
    then no node with its ACTUAL features intervenes. -/
theorem closestGoal_implies_closestGoalWith
    (a : AgreeRelation) (root : SyntacticObject) (fa : FeatureAssignment)
    (h : closestGoal a root) : closestGoalWith a root fa :=
  ⟨h.1, fun ⟨x, hTerm, hNeq, hInt⟩ => h.2 ⟨x, fa x, hTerm, hNeq, hInt⟩⟩

/-- Boolean closest-goal check: is `goal` the closest node matching
    `pred` in `probe`'s c-command domain within `root`?

    This is the computational counterpart of `closestGoalWith`, using
    decidable `cCommandsIn` and a matching predicate. `pred` determines
    which nodes are potential goals/interveners — typically a category
    check (e.g., "is this node D-bearing?").

    1. `probe` c-commands `goal`
    2. `goal` matches the predicate
    3. No other matching node is both c-commanded by `probe` AND
       c-commands `goal` (= no intervener) -/
def closestGoalB (root probe goal : SyntacticObject)
    (pred : SyntacticObject → Bool) : Bool :=
  decide (cCommandsIn root probe goal) &&
  pred goal &&
  !(root.subtrees.any fun x =>
    x != goal &&
    pred x &&
    decide (cCommandsIn root probe x) &&
    decide (cCommandsIn root x goal))

-- ============================================================================
-- § 3c: Horizons (@cite{keine-2019})
-- ============================================================================

/-- Is `target` behind a horizon of category `horizonCat` relative to
    `probe` in tree `root`?

    A leaf head `n` of category `horizonCat` creates a horizon: its
    c-command domain is opaque to the probe. `target` is behind the
    horizon iff there exists a leaf `n` with category `horizonCat`
    such that:
    1. `probe` c-commands `n` (n is in probe's search domain)
    2. `n` c-commands `target` (target is in n's opaque domain)

    This captures @cite{keine-2019}'s horizon mechanism: the probe
    cannot see past a head of the horizon category. Elements that
    are c-commanded by the horizon head are invisible to the probe.

    Example: N° is a horizon for wh-probes (@cite{aissen-polian-2025}).
    In `[DP D° [PossP Psr N°]]`, N° c-commands Psr (they are sisters),
    so wh-probes on C° cannot reach Psr. But D° is a sister of PossP,
    NOT c-commanded by N°, so the whole DP remains visible for
    pied-piping. -/
def behindHorizonB (root probe target : SyntacticObject)
    (horizonCat : Cat) : Bool :=
  root.subtrees.any fun n =>
    match n with
    | .leaf tok =>
      tok.item.outerCat == horizonCat &&
      decide (cCommandsIn root n target) &&
      decide (cCommandsIn root probe n)
    | .node _ _ => false

-- ============================================================================
-- § 4: Feature Valuation
-- ============================================================================

/-- Value an unvalued feature by copying from a valued one -/
def valueFeature (unvalued valued : GramFeature) : Option GramFeature :=
  match unvalued, valued with
  | .unvalued _, .valued v => some (.valued v)
  | _, _ => none

/-- Apply Agree: value the probe's feature from the goal.
    Uses `sameType` for matching, so a probe with [uPerson:_] will
    be valued by a goal with [Person:3rd] — the placeholder value is
    irrelevant, only the feature type matters. -/
def applyAgree (probeFeats goalFeats : FeatureBundle) (ftype : FeatureVal) :
    Option FeatureBundle :=
  match getValuedFeature goalFeats ftype with
  | none => none
  | some goalFeat =>
    some (probeFeats.map λ f =>
      if f.isUnvalued && f.featureType.sameType ftype then
        match valueFeature f goalFeat with
        | some v => v
        | none => f
      else f)

-- ============================================================================
-- § 5: Common Agree Configurations
-- ============================================================================

/-- T-Agree: T probes for φ-features on subject DP

    T has [uφ], subject DP has [φ] → T gets valued φ.
    The `.third` value on person probes is a conventional placeholder —
    `sameType` ignores the specific `PersonLevel` value, matching any
    `.person _` against any `.person _`. -/
structure TAgree where
  tHead : SyntacticObject
  subject : SyntacticObject
  tFeatures : FeatureBundle
  subjFeatures : FeatureBundle
  -- T has unvalued phi
  t_has_uphi : hasUnvaluedFeature tFeatures (.phi (.person .third)) = true ∨
               hasUnvaluedFeature tFeatures (.phi (.number .sg)) = true
  -- Subject has valued phi
  subj_has_phi : hasValuedFeature subjFeatures (.phi (.person .third)) = true ∨
                 hasValuedFeature subjFeatures (.phi (.number .sg)) = true

/-- C-Agree: C probes for [Q] feature

    C has [uQ], interrogative element has [+Q] → question is licensed -/
structure CAgree where
  cHead : SyntacticObject
  qElement : SyntacticObject
  cFeatures : FeatureBundle
  qFeatures : FeatureBundle
  -- C has unvalued Q
  c_has_uq : hasUnvaluedFeature cFeatures (.q false) = true
  -- Q-element has valued [+Q]
  q_has_q : hasValuedFeature qFeatures (.q true) = true

-- ============================================================================
-- § 6: Movement Triggered by Agree
-- ============================================================================

/-- EPP triggers movement to specifier

    When a head has [EPP], Agree is not enough - the goal must MOVE
    to the specifier position of the agreeing head. -/
def hasEPP (fb : FeatureBundle) : Bool :=
  fb.any λ f => match f with
    | .valued (.epp true) => true
    | .unvalued (.epp true) => true
    | _ => false

/-- Movement is triggered when probe has EPP -/
def agreeTriggersMoveement (probeFeats : FeatureBundle) : Bool :=
  hasEPP probeFeats

/-- T-to-C movement is triggered by [uQ] + [EPP] on C

    In matrix questions:
    - C has [uQ, EPP]
    - T has [+Q] (in some analyses) or movement satisfies EPP
    - T moves to C (head movement) -/
def tToCTriggered (cFeats : FeatureBundle) : Bool :=
  hasUnvaluedFeature cFeats (.q false) && hasEPP cFeats

-- ============================================================================
-- § 7: Worked Example - Subject-Auxiliary Inversion
-- ============================================================================

/-- Matrix C features: [uQ, EPP] -/
def matrixCFeatures : FeatureBundle :=
  [.unvalued (.q false), .valued (.epp true)]

/-- Embedded C features: [uQ] only (satisfied by wh-movement) -/
def embeddedCFeatures : FeatureBundle :=
  [.unvalued (.q false)]

/-- Matrix C triggers T-to-C -/
theorem matrix_triggers_t_to_c : tToCTriggered matrixCFeatures = true := rfl

/-- Embedded C does not trigger T-to-C -/
theorem embedded_no_t_to_c : tToCTriggered embeddedCFeatures = false := rfl

-- ============================================================================
-- § 8: Activity Condition (@cite{chomsky-2000}, 2001)
-- ============================================================================

/-- Is a feature bundle active? (has at least one unvalued feature)

    An element is active iff it has at least one unvalued feature.
    Typically, DPs are active when they have unvalued Case. -/
def isActive (fb : FeatureBundle) : Bool :=
  fb.any GramFeature.isUnvalued

/-- An element needs Case (has unvalued Case feature) -/
def needsCase (fb : FeatureBundle) : Bool :=
  fb.any λ f => f.isUnvalued && match f.featureType with
    | .case _ => true
    | _ => false

/-- An element has valued Case -/
def hasCase (fb : FeatureBundle) : Bool :=
  fb.any λ f => f.isValued && match f.featureType with
    | .case _ => true
    | _ => false

/-- Activity is typically determined by Case:
    A DP is active iff it lacks Case

    When a feature bundle contains only Case features, the bundle is active
    (has unvalued features) iff it needs Case (has unvalued Case). -/
theorem activity_via_case (fb : FeatureBundle)
    (h : fb.all λ f => match f.featureType with | .case _ => true | _ => false) :
    isActive fb ↔ needsCase fb := by
  constructor
  · intro hActive
    simp only [isActive, List.any_eq_true] at hActive
    simp only [needsCase, List.any_eq_true]
    obtain ⟨f, hfMem, hfUnval⟩ := hActive
    use f, hfMem
    simp only [Bool.and_eq_true]
    constructor
    · exact hfUnval
    · simp only [List.all_eq_true] at h
      exact h f hfMem
  · intro hNeeds
    simp only [needsCase, List.any_eq_true] at hNeeds
    simp only [isActive, List.any_eq_true]
    obtain ⟨f, hfMem, hfCond⟩ := hNeeds
    simp only [Bool.and_eq_true] at hfCond
    exact ⟨f, hfMem, hfCond.1⟩

-- ============================================================================
-- § 9: Active Goal (for Agree with Activity)
-- ============================================================================

/-- A goal that satisfies the Activity Condition -/
structure ActiveGoal where
  goal : SyntacticObject
  goalFeatures : FeatureBundle
  isActive : isActive goalFeatures = true
  deriving Repr

/-- Create an ActiveGoal if the features are indeed active -/
def mkActiveGoal (goal : SyntacticObject) (feats : FeatureBundle) : Option ActiveGoal :=
  if h : isActive feats then some ⟨goal, feats, h⟩
  else none

/-- Valid Agree with Activity Condition

    Agree requires:
    1. Probe c-commands goal (within tree)
    2. Probe has unvalued feature
    3. Goal has matching valued feature
    4. Goal is ACTIVE (has some unvalued feature) -/
def validAgreeWithActivity (a : AgreeRelation) (root : SyntacticObject) : Prop :=
  validAgree a root ∧
  isActive a.goalFeatures = true

-- ============================================================================
-- § 10: Multiple Agree (@cite{hiraiwa-2001}, 2005)
-- ============================================================================

/-- Multiple Agree: a probe agreeing with a list of goals -/
structure MultipleAgree where
  probe : SyntacticObject
  probeFeatures : FeatureBundle
  goals : List (SyntacticObject × FeatureBundle)
  feature : FeatureVal
  -- All goals must have the relevant valued feature
  goalsHaveFeature : goals.all (λ ⟨_, gf⟩ => hasValuedFeature gf feature)
  deriving Repr

/-- Is Multiple Agree valid? Each goal must be c-commanded by probe (within tree) -/
def MultipleAgree.isValid (ma : MultipleAgree) (root : SyntacticObject) : Prop :=
  hasUnvaluedFeature ma.probeFeatures ma.feature = true ∧
  ∀ (g : SyntacticObject × FeatureBundle), g ∈ ma.goals →
    cCommandsIn root ma.probe g.1

/-- Apply Multiple Agree: value probe's feature, mark all goals -/
def applyMultipleAgree (ma : MultipleAgree) : Option FeatureBundle :=
  match ma.goals.head? with
  | none => none
  | some (_, gf) =>
    match getValuedFeature gf ma.feature with
    | none => none
    | some goalFeat =>
      some (ma.probeFeatures.map λ f =>
        if f.isUnvalued && (f.featureType == ma.feature) then
          match valueFeature f goalFeat with
          | some v => v
          | none => f
        else f)

-- ============================================================================
-- § 11: Defective Intervention (@cite{chomsky-2000})
-- ============================================================================

/-- A defective element: has some matching features but incomplete set -/
structure DefectiveElement where
  so : SyntacticObject
  features : FeatureBundle
  -- Has at least one phi feature
  hasPartialPhi : (features.any λ f => match f.featureType with
    | .phi _ => true
    | _ => false) = true
  -- But not a complete phi set (deficient)
  isDeficient : Bool  -- Simplified: mark as deficient
  deriving Repr

/-- Does X defectively intervene between probe and goal (within tree `root`)?

    X defectively intervenes if:
    - X is between probe and goal (c-command wise)
    - X has matching features
    - X is defective (can't be a full goal) -/
def defectivelyIntervenes (root : SyntacticObject) (probe x goal : SyntacticObject)
    (xDef : DefectiveElement) (ftype : FeatureVal) : Prop :=
  cCommandsIn root probe x ∧
  cCommandsIn root x goal ∧
  xDef.so = x ∧
  xDef.isDeficient = true ∧
  (xDef.features.any λ f => featuresMatch f (.unvalued ftype)) = true

-- ============================================================================
-- § 12: Phase-Bounded Agree
-- ============================================================================

/-- Valid Agree with Phase Impenetrability Condition.

    Agree is blocked if the goal is inside a phase complement
    (and thus inaccessible under PIC). -/
def validAgreeWithPIC (strength : PICStrength) (phases : List Phase)
    (rel : AgreeRelation) (root : SyntacticObject) : Prop :=
  validAgree rel root ∧
    ¬∃ ph ∈ phases, phaseImpenetrable strength ph.head rel.goal

/-- PIC-bounded Agree with Activity Condition.

    The full Agree constraint: probe c-commands goal, feature matching holds,
    goal is active, AND no intervening phase boundary blocks the relation. -/
def fullAgree (strength : PICStrength) (phases : List Phase)
    (rel : AgreeRelation) (root : SyntacticObject) : Prop :=
  validAgreeWithActivity rel root ∧
    ¬∃ ph ∈ phases, phaseImpenetrable strength ph.head rel.goal

-- ============================================================================
-- § 13: Clause-Typing Agree Configurations
-- ============================================================================

/-- Fin-Agree: Fin probes for [±finite] on its complement (TP). -/
def finAgreeFeatures (isFinite : Bool) : FeatureBundle :=
  [.unvalued (.finite isFinite)]

/-- Force-Fin-Agree: Force/C probes for clause-type features on Fin. -/
def forceFinAgreeFeatures (isFactive : Bool) : FeatureBundle :=
  [.unvalued (.factive isFactive)]

/-- Neg-Agree: Neg probes for [±neg], licensing sentential negation. -/
def negAgreeFeatures : FeatureBundle :=
  [.unvalued (.neg true)]

/-- Rel-Agree: Rel probes for [±rel], licensing relative clause formation. -/
def relAgreeFeatures : FeatureBundle :=
  [.unvalued (.rel true)]

/-- Clause-typing features match correctly. -/
theorem finite_features_match :
    featuresMatch (.unvalued (.finite true)) (.valued (.finite true)) = true := rfl

theorem factive_features_match :
    featuresMatch (.unvalued (.factive true)) (.valued (.factive false)) = true := rfl

theorem neg_features_match :
    featuresMatch (.unvalued (.neg true)) (.valued (.neg true)) = true := rfl

theorem rel_features_match :
    featuresMatch (.unvalued (.rel true)) (.valued (.rel false)) = true := rfl

-- ============================================================================
-- § 14: Satisfaction Conditions (@cite{deal-2024}; @cite{keine-2019})
-- ============================================================================

/-- How a probe's search can be terminated.

    Standard Agree assumes a probe is satisfied only by finding a matching
    valued feature (simple feature match). @cite{deal-2024} argues for richer
    conditions to capture e.g. Mam's Infl probe, which is satisfied by
    EITHER matching φ-features OR encountering transitive Voice:

    **Mam example** (@cite{scott-2023}, via @cite{deal-2024}):
    - Infl carries [uφ] with satisfaction [SAT: φ or Voice_TR]
    - Intransitive: probe passes through (no Voice_TR) → finds S → real φ-agreement
    - Transitive: probe encounters Voice_TR → satisfied without copying φ → default "∅"

    This turns the Mam bridge's prose account into a computable derivation:
    ```
    def mamInflSatisfaction : SatisfactionCond :=
.disjunctive [.featureMatch (.phi (.person.third)),.headEncounter.v]
    ```
-/
inductive SatisfactionCond where
  /-- Standard: probe is satisfied by finding a matching valued feature. -/
  | featureMatch : FeatureVal → SatisfactionCond
  /-- Disjunctive: probe is satisfied by ANY of these conditions.
      Models @cite{deal-2024}'s interaction-based probes. -/
  | disjunctive : List SatisfactionCond → SatisfactionCond
  /-- Head encounter: probe is satisfied by encountering a head of this
      category, even without feature matching. The probe stops but copies
      no features — yielding the Elsewhere (default) exponent at PF. -/
  | headEncounter : Cat → SatisfactionCond
  deriving Repr

/-- Is an atomic (non-disjunctive) condition met? -/
private def atomicSatisfied (cond : SatisfactionCond) (fb : FeatureBundle)
    (ctx : Option Cat) : Bool :=
  match cond with
  | .featureMatch ft => hasValuedFeature fb ft
  | .headEncounter cat => ctx == some cat
  | .disjunctive _ => false  -- nested disjunctions handled at top level

/-- Check whether a satisfaction condition is met.

    `fb` is the feature bundle of the element the probe encounters.
    `ctx` is the syntactic category of that element (if it's a head).
    Returns `true` if the probe should stop searching. -/
def SatisfactionCond.isSatisfied (cond : SatisfactionCond) (fb : FeatureBundle)
    (ctx : Option Cat) : Bool :=
  match cond with
  | .featureMatch ft => hasValuedFeature fb ft
  | .disjunctive conds => conds.any (atomicSatisfied · fb ctx)
  | .headEncounter cat => ctx == some cat

/-- Did the probe copy features, or just stop?

    When satisfied by feature match, the probe copies features (→ real agreement).
    When satisfied by head encounter, no features are copied (→ default/Elsewhere).
    For disjunctive conditions, feature copying occurs iff the first satisfied
    condition is a feature match. -/
def SatisfactionCond.copiedFeatures (cond : SatisfactionCond) (fb : FeatureBundle)
    (ctx : Option Cat) : Bool :=
  match cond with
  | .featureMatch ft => hasValuedFeature fb ft
  | .disjunctive conds =>
    match conds.find? (atomicSatisfied · fb ctx) with
    | some (.featureMatch ft) => hasValuedFeature fb ft
    | _ => false  -- head encounter or nested → no features copied
  | .headEncounter _ => false

/-- Mam's Infl probe satisfaction condition:
    satisfied by EITHER matching φ-features OR encountering transitive Voice. -/
def mamInflSatisfaction : SatisfactionCond :=
  .disjunctive [.featureMatch (.phi (.person .third)), .headEncounter .v]

/-- Intransitive environment: the probe encounters a DP with φ-features
    (no Voice_TR in the way). Feature match is satisfied → real agreement. -/
theorem mam_intransitive_satisfied :
    mamInflSatisfaction.isSatisfied
      [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
      none = true := by rfl

/-- Transitive environment: the probe encounters Voice_TR (category.v).
    Head encounter is satisfied → probe stops without copying features. -/
theorem mam_transitive_satisfied :
    mamInflSatisfaction.isSatisfied [] (some .v) = true := by rfl

/-- In the transitive case, no features are copied — yielding default. -/
theorem mam_transitive_no_copy :
    mamInflSatisfaction.copiedFeatures [] (some .v) = false := by rfl

/-- In the intransitive case, features ARE copied — yielding real agreement. -/
theorem mam_intransitive_copies :
    mamInflSatisfaction.copiedFeatures
      [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
      none = true := by rfl

end Minimalism
