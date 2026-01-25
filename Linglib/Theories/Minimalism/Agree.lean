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

-- ============================================================================
-- Part 11: Activity Condition
-- ============================================================================

/-
## The Activity Condition (Chomsky 2000, 2001)

A goal is only "visible" to a probe if it is ACTIVE, i.e., if it has at least
one unvalued feature. Once all of a goal's features are valued, it becomes
inactive and is no longer accessible for further Agree operations.

This explains:
1. Why subjects don't undergo further agreement after Case is valued
2. Why moved elements "freeze in place" once their features are satisfied
3. Defective intervention effects
-/

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
  -- When all features are Case features, isActive ↔ needsCase
  constructor
  · -- isActive → needsCase
    intro hActive
    simp only [isActive, List.any_eq_true] at hActive
    simp only [needsCase, List.any_eq_true]
    obtain ⟨f, hfMem, hfUnval⟩ := hActive
    use f, hfMem
    simp only [Bool.and_eq_true]
    constructor
    · exact hfUnval
    · simp only [List.all_eq_true] at h
      exact h f hfMem
  · -- needsCase → isActive
    intro hNeeds
    simp only [needsCase, List.any_eq_true] at hNeeds
    simp only [isActive, List.any_eq_true]
    obtain ⟨f, hfMem, hfCond⟩ := hNeeds
    simp only [Bool.and_eq_true] at hfCond
    exact ⟨f, hfMem, hfCond.1⟩

-- ============================================================================
-- Part 12: Active Goal (for Agree with Activity)
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
    1. Probe c-commands goal
    2. Probe has unvalued feature
    3. Goal has matching valued feature
    4. Goal is ACTIVE (has some unvalued feature) -/
def validAgreeWithActivity (a : AgreeRelation) : Prop :=
  validAgree a ∧
  isActive a.goalFeatures = true

-- ============================================================================
-- Part 13: Multiple Agree
-- ============================================================================

/-
## Multiple Agree (Hiraiwa 2001, 2005)

In some languages/constructions, a single probe can agree with multiple goals
simultaneously. This is called "Multiple Agree."

Examples:
- Japanese honorification (verb agrees with subject AND object)
- Multiple wh-fronting in Slavic languages
- Long-distance agreement in Icelandic

The key constraint: all goals must be in the probe's c-command domain,
and there's no intervener with the relevant feature.
-/

/-- Multiple Agree: a probe agreeing with a list of goals -/
structure MultipleAgree where
  probe : SyntacticObject
  probeFeatures : FeatureBundle
  goals : List (SyntacticObject × FeatureBundle)
  feature : FeatureVal
  -- All goals must have the relevant valued feature
  goalsHaveFeature : goals.all (λ ⟨_, gf⟩ => hasValuedFeature gf feature)
  deriving Repr

/-- Is Multiple Agree valid? Each goal must be c-commanded by probe -/
def MultipleAgree.isValid (ma : MultipleAgree) : Prop :=
  hasUnvaluedFeature ma.probeFeatures ma.feature = true ∧
  ∀ (g : SyntacticObject × FeatureBundle), g ∈ ma.goals →
    cCommands ma.probe g.1

/-- Apply Multiple Agree: value probe's feature, mark all goals -/
def applyMultipleAgree (ma : MultipleAgree) : Option FeatureBundle :=
  -- Get the valued feature from the first goal
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
-- Part 14: Case Filter
-- ============================================================================

/-
## The Case Filter

Every DP must receive Case. In Minimalist terms:
- Every DP has [uCase] (unvalued Case feature)
- [uCase] must be valued by Agree with a Case-assigning head
- Failure to value [uCase] causes the derivation to crash

Case assigners:
- T assigns nominative to its specifier (subject)
- v assigns accusative to its complement (object)
- P assigns oblique to its complement
-/

/-- A DP's features (with unvalued Case) -/
structure DPFeatures where
  phi : List PhiFeature      -- Person, number, gender
  caseFeature : GramFeature  -- The Case feature (valued or unvalued)
  deriving Repr

/-- Create DP features with unvalued Case -/
def DPFeatures.withUnvaluedCase (phi : List PhiFeature) : DPFeatures :=
  ⟨phi, .unvalued (.case .obl)⟩

/-- Create DP features with valued Case -/
def DPFeatures.withCase (phi : List PhiFeature) (c : CaseVal) : DPFeatures :=
  ⟨phi, .valued (.case c)⟩

/-- Does a DP satisfy the Case Filter? (has valued Case) -/
def satisfiesCaseFilter (dp : DPFeatures) : Bool :=
  dp.caseFeature.isValued

/-- Convert DPFeatures to a FeatureBundle -/
def DPFeatures.toBundle (dp : DPFeatures) : FeatureBundle :=
  dp.phi.map (λ p => .valued (.phi p)) ++ [dp.caseFeature]

/-- The Case Filter: a derivation converges only if all DPs have valued Case

    This is stated as: for all DPs in the structure, their Case feature
    must be valued. -/
def caseFilterHolds (dps : List DPFeatures) : Bool :=
  dps.all satisfiesCaseFilter

/-- If Case Filter fails, there exists a DP without Case -/
theorem case_filter_necessary (dps : List DPFeatures) :
    caseFilterHolds dps = false → ∃ dp ∈ dps, satisfiesCaseFilter dp = false := by
  intro h
  induction dps with
  | nil => simp [caseFilterHolds] at h
  | cons hd tl ih =>
    simp only [caseFilterHolds, List.all_cons, Bool.and_eq_false_iff] at h
    cases h with
    | inl hHd =>
      use hd
      simp only [List.mem_cons, true_or, true_and]
      exact hHd
    | inr hTl =>
      obtain ⟨dp, hdp, hsat⟩ := ih hTl
      use dp
      simp only [List.mem_cons]
      exact ⟨Or.inr hdp, hsat⟩

/-- A well-formed derivation satisfies the Case Filter -/
theorem case_filter_at_interfaces (dps : List DPFeatures)
    (hWF : caseFilterHolds dps = true) :
    ∀ dp ∈ dps, satisfiesCaseFilter dp = true := by
  intro dp hdp
  induction dps with
  | nil => simp at hdp
  | cons hd tl ih =>
    simp only [caseFilterHolds, List.all_cons, Bool.and_eq_true] at hWF
    rcases List.mem_cons.mp hdp with heq | hmem
    · rw [heq]; exact hWF.1
    · exact ih hWF.2 hmem

-- ============================================================================
-- Part 15: Defective Intervention
-- ============================================================================

/-
## Defective Intervention (Chomsky 2000)

An element X is a DEFECTIVE INTERVENER if:
1. It has some features that match the probe
2. But it's INACTIVE (all features valued)

Defective interveners block Agree even though they can't participate in it.

Example: In raising constructions, PRO is a defective intervener:
  "John seems [PRO to be happy]"
  - T probes for φ-features
  - PRO has φ but is inactive (no Case)
  - But PRO is DEFECTIVE, so it doesn't block Agree with "John"

Wait, this is backwards. Let me reconsider:
Actually, defective intervention is when an INACTIVE element still blocks:
  "*There seems a man to be here"
  - "a man" intervenes between T and "there" for EPP
  - But "a man" has unvalued Case, so it SHOULD be active

The real defective intervention is:
  - An element that MATCHES but can't be the goal
  - e.g., expletive "there" matches for φ but doesn't have full φ-features
-/

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

/-- Does X defectively intervene between probe and goal?

    X defectively intervenes if:
    - X is between probe and goal (c-command wise)
    - X has matching features
    - X is defective (can't be a full goal) -/
def defectivelyIntervenes (probe x goal : SyntacticObject)
    (xDef : DefectiveElement) (ftype : FeatureVal) : Prop :=
  cCommands probe x ∧
  cCommands x goal ∧
  xDef.so = x ∧
  xDef.isDeficient = true ∧
  -- X has a matching feature
  (xDef.features.any λ f => featuresMatch f (.unvalued ftype)) = true

end Minimalism
