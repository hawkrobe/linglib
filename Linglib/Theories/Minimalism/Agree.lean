/-
# Agree (Minimalist Feature Checking)

Formalization of Agree following Chomsky (2000, 2001) and Adger (2003).

## The Agree Operation

Agree is the mechanism by which features are checked/valued:
1. A **probe** (head with unvalued feature) searches its c-command domain
2. It finds the closest **goal** (element with matching valued feature)
3. The probe's feature is valued by copying from the goal
4. Both features are then checked (and may delete at PF/LF)

## Key Concepts

- **Interpretable features**: Contribute to meaning (e.g., [person] on D)
- **Uninterpretable features**: Must be checked/deleted (e.g., [uPerson] on T)
- **Probe**: Head with unvalued uninterpretable feature
- **Goal**: Element with valued feature matching the probe
- **Locality**: Agree targets the closest c-commanded goal

## Examples

- T has [uφ] (unvalued phi-features), probes and finds subject DP with [φ]
- C has [uQ], probes and finds [+Q] on a question particle or wh-phrase
- v has [uCase:acc], assigns accusative to the closest DP in its domain

## References

- Chomsky, N. (2000). "Minimalist Inquiries"
- Chomsky, N. (2001). "Derivation by Phase"
- Adger, D. (2003). "Core Syntax", Chapter 4
-/

import Linglib.Theories.Minimalism.Labeling

namespace Minimalism

-- ============================================================================
-- Part 1: Feature Types
-- ============================================================================

/-- Phi-features (agreement features) -/
inductive PhiFeature where
  | person : Nat → PhiFeature        -- 1, 2, 3
  | number : Bool → PhiFeature       -- true = plural, false = singular
  | gender : Nat → PhiFeature        -- language-specific encoding
  deriving Repr, DecidableEq

/-- Case values -/
inductive CaseVal where
  | nom    -- nominative (subject)
  | acc    -- accusative (object)
  | dat    -- dative
  | gen    -- genitive
  | obl    -- oblique (default)
  deriving Repr, DecidableEq

/-- Feature values that can be checked via Agree -/
inductive FeatureVal where
  | phi : PhiFeature → FeatureVal
  | case : CaseVal → FeatureVal
  | wh : Bool → FeatureVal           -- [±wh]
  | q : Bool → FeatureVal            -- [±Q] (question)
  | epp : Bool → FeatureVal          -- EPP (needs specifier)
  | tense : Bool → FeatureVal        -- [±tense]
  deriving Repr, DecidableEq

/-- A grammatical feature: either valued or unvalued

    - Valued (interpretable): contributes to meaning, can be a goal
    - Unvalued (uninterpretable): must be checked, acts as probe -/
inductive GramFeature where
  | valued : FeatureVal → GramFeature
  | unvalued : FeatureVal → GramFeature  -- The FeatureVal indicates feature TYPE
  deriving Repr, DecidableEq

/-- Is this feature valued? -/
def GramFeature.isValued : GramFeature → Bool
  | .valued _ => true
  | .unvalued _ => false

/-- Is this feature unvalued (a potential probe)? -/
def GramFeature.isUnvalued : GramFeature → Bool
  | .valued _ => false
  | .unvalued _ => true

/-- Get the feature type (ignoring valued/unvalued distinction) -/
def GramFeature.featureType : GramFeature → FeatureVal
  | .valued v => v
  | .unvalued v => v

/-- Do two features match in type? (for Agree) -/
def featuresMatch (f1 f2 : GramFeature) : Bool :=
  match f1.featureType, f2.featureType with
  | .phi p1, .phi p2 => match p1, p2 with
    | .person _, .person _ => true
    | .number _, .number _ => true
    | .gender _, .gender _ => true
    | _, _ => false
  | .case _, .case _ => true
  | .wh _, .wh _ => true
  | .q _, .q _ => true
  | .epp _, .epp _ => true
  | .tense _, .tense _ => true
  | _, _ => false

-- ============================================================================
-- Part 2: Feature Bundles on Syntactic Objects
-- ============================================================================

/-- A feature bundle: list of grammatical features -/
abbrev FeatureBundle := List GramFeature

/-- Does the bundle have an unvalued feature of a given type? -/
def hasUnvaluedFeature (fb : FeatureBundle) (ftype : FeatureVal) : Bool :=
  fb.any λ f => f.isUnvalued && (f.featureType == ftype)

/-- Does the bundle have a valued feature of a given type? -/
def hasValuedFeature (fb : FeatureBundle) (ftype : FeatureVal) : Bool :=
  fb.any λ f => f.isValued && (f.featureType == ftype)

/-- Get the valued feature of a given type (if present) -/
def getValuedFeature (fb : FeatureBundle) (ftype : FeatureVal) : Option GramFeature :=
  fb.find? λ f => f.isValued && (f.featureType == ftype)

-- ============================================================================
-- Part 3: Extended Lexical Items with Features
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
-- Part 4: Agree Relation
-- ============================================================================

/-- A probe-goal pair for Agree -/
structure AgreeRelation where
  probe : SyntacticObject
  goal : SyntacticObject
  feature : FeatureVal      -- The feature type being checked
  probeFeatures : FeatureBundle
  goalFeatures : FeatureBundle

/-- The probe c-commands the goal -/
def AgreeRelation.probeCommands (a : AgreeRelation) : Prop :=
  cCommands a.probe a.goal

/-- The goal has the relevant valued feature -/
def AgreeRelation.goalHasFeature (a : AgreeRelation) : Bool :=
  hasValuedFeature a.goalFeatures a.feature

/-- The probe has the relevant unvalued feature -/
def AgreeRelation.probeNeedsFeature (a : AgreeRelation) : Bool :=
  hasUnvaluedFeature a.probeFeatures a.feature

/-- Valid Agree: probe c-commands goal, probe has unvalued, goal has valued -/
def validAgree (a : AgreeRelation) : Prop :=
  a.probeCommands ∧
  a.probeNeedsFeature = true ∧
  a.goalHasFeature = true

-- ============================================================================
-- Part 5: Locality (Closest Goal)
-- ============================================================================

/-- X intervenes between probe and goal iff:
    - probe c-commands X
    - X c-commands goal
    - X has a matching valued feature -/
def intervenes (probe x goal : SyntacticObject)
    (xFeatures : FeatureBundle) (ftype : FeatureVal) : Prop :=
  cCommands probe x ∧
  cCommands x goal ∧
  hasValuedFeature xFeatures ftype = true

/-- Goal is the closest matching goal for probe -/
def closestGoal (a : AgreeRelation) (root : SyntacticObject) : Prop :=
  validAgree a ∧
  ¬∃ (x : SyntacticObject) (xFeats : FeatureBundle),
    isTermOf x root ∧
    x ≠ a.goal ∧
    intervenes a.probe x a.goal xFeats a.feature

-- ============================================================================
-- Part 6: Feature Valuation
-- ============================================================================

/-- Value an unvalued feature by copying from a valued one -/
def valueFeature (unvalued valued : GramFeature) : Option GramFeature :=
  match unvalued, valued with
  | .unvalued _, .valued v => some (.valued v)
  | _, _ => none

/-- Apply Agree: value the probe's feature from the goal -/
def applyAgree (probeFeats goalFeats : FeatureBundle) (ftype : FeatureVal) :
    Option FeatureBundle :=
  match getValuedFeature goalFeats ftype with
  | none => none
  | some goalFeat =>
    some (probeFeats.map λ f =>
      if f.isUnvalued && (f.featureType == ftype) then
        match valueFeature f goalFeat with
        | some v => v
        | none => f
      else f)

-- ============================================================================
-- Part 7: Common Agree Configurations
-- ============================================================================

/-- T-Agree: T probes for φ-features on subject DP

    T has [uφ], subject DP has [φ] → T gets valued φ -/
structure TAgree where
  tHead : SyntacticObject
  subject : SyntacticObject
  tFeatures : FeatureBundle
  subjFeatures : FeatureBundle
  -- T has unvalued phi
  t_has_uphi : hasUnvaluedFeature tFeatures (.phi (.person 0)) = true ∨
               hasUnvaluedFeature tFeatures (.phi (.number false)) = true
  -- Subject has valued phi
  subj_has_phi : hasValuedFeature subjFeatures (.phi (.person 0)) = true ∨
                 hasValuedFeature subjFeatures (.phi (.number false)) = true

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
-- Part 8: Movement Triggered by Agree
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
-- Part 9: Worked Example - Subject-Auxiliary Inversion
-- ============================================================================

/-
## Deriving Subject-Auxiliary Inversion

In matrix questions:
1. C has [uQ, EPP] - unvalued Q feature, needs specifier
2. T (auxiliary) has [+Q] feature (or is attracted by EPP)
3. T moves to C to check [uQ] (head-to-head movement)
4. Subject remains in Spec-TP (below C+T)

Result: Aux-Subject-V order ("Can John eat?")

In embedded questions:
1. C has [uQ] but wh-movement satisfies it
2. No T-to-C movement needed
3. Subject stays before T

Result: Subject-Aux-V order ("what John can eat")
-/

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
-- Part 10: Case Assignment via Agree
-- ============================================================================

/-- Nominative Case is assigned by T

    T has [uCase:nom], assigns to closest DP in Spec-TP -/
def tAssignsNominative : FeatureBundle :=
  [.unvalued (.case .nom)]

/-- Accusative Case is assigned by v (transitive light verb)

    v has [uCase:acc], assigns to closest DP (object) -/
def vAssignsAccusative : FeatureBundle :=
  [.unvalued (.case .acc)]

/-- DP needs Case (Case Filter)

    All DPs have [uCase], must be valued by Agree -/
def dpNeedsCase : FeatureBundle :=
  [.unvalued (.case .obl)]  -- unvalued, will be valued by T or v

end Minimalism
