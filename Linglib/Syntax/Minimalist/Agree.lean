import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Minimalist.Phase
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Syntax.Minimalist.Probe.Transmission

/-!
# Agree (Minimalist Feature Checking)


Formalization of Agree following [chomsky-2000] and [adger-2003].

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
feature. [deal-2024] and [keine-2019] argue for richer conditions:
- **Feature match**: the standard case
- **Head encounter**: probe is satisfied by encountering a head of a
  particular category (e.g., Infl's probe stopped by transitive Voice)
- **Disjunctive**: probe is satisfied by ANY of several conditions

This captures e.g. Mam's Infl probe, which has satisfaction condition
[SAT: φ or Voice_TR] — it stops when it finds either matching
φ-features OR transitive Voice, whichever comes first.

-/

namespace Minimalist

open Features.Prominence

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
  FeatureType.all.any λ t => (li.features t).isUnvalued

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
  SO.cCommandsIn root a.probe a.goal

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

-- "Closest matching goal, no intervener" is the canonical list engine
-- `Probe.search` (`Probe/Basic.lean`, `search_eq_some_iff_closest`); the
-- tree-native `closestGoal`/`closestGoalWith`/`intervenes` reinventions
-- (zero consumers) were retired. `SyntacticObject` is a commutative magma
-- with no canonical c-command linearization, so the tree↔list bridge is
-- not definitional; `closestGoalB` below is the decidable tree presentation.

/-- Decidable tree presentation of `Probe.search`-locality
    (`Probe.search_eq_some_iff_closest`, `pred` playing `Probe.vis`):
    `goal` is `pred`-matching and c-commanded by `probe`, with no
    `pred`-matching node c-commanded by `probe` c-commanding `goal`. -/
def closestGoalB (root probe goal : SyntacticObject)
    (pred : SyntacticObject → Bool) : Bool :=
  decide (SO.cCommandsIn root probe goal) &&
  pred goal &&
  (! @decide (∃ x ∈ root.subtrees,
    x ≠ goal ∧ pred x = true ∧
    SO.cCommandsIn root probe x ∧ SO.cCommandsIn root x goal)
    Multiset.decidableExistsMultiset)

-- ============================================================================
-- § 3c: Horizons ([keine-2019])
-- ============================================================================

/-- Per-vertex horizon predicate: leaf with category = horizonCat. -/
private def isHorizonLeafFor (horizonCat : Cat) (n : SyntacticObject) : Prop :=
  match SO.getLIToken n with
  | some tok => tok.item.outerCat = horizonCat
  | none => False

instance (horizonCat : Cat) (n : SyntacticObject) :
    Decidable (isHorizonLeafFor horizonCat n) := by
  unfold isHorizonLeafFor
  cases SO.getLIToken n <;> infer_instance

/-- Is `target` behind a horizon of category `horizonCat` relative to
    `probe` in tree `root`?

    A leaf head `n` of category `horizonCat` creates a horizon: its
    c-command domain is opaque to the probe. `target` is behind the
    horizon iff there exists a leaf `n` with category `horizonCat`
    such that:
    1. `probe` c-commands `n` (n is in probe's search domain)
    2. `n` c-commands `target` (target is in n's opaque domain)

    This captures [keine-2019]'s horizon mechanism: the probe
    cannot see past a head of the horizon category. Elements that
    are c-commanded by the horizon head are invisible to the probe.

    Example: N° is a horizon for wh-probes ([aissen-polian-2025]).
    In `[DP D° [PossP Psr N°]]`, N° c-commands Psr (they are sisters),
    so wh-probes on C° cannot reach Psr. But D° is a sister of PossP,
    NOT c-commanded by N°, so the whole DP remains visible for
    pied-piping. -/
def behindHorizonB (root probe target : SyntacticObject)
    (horizonCat : Cat) : Bool :=
  @decide (∃ n ∈ root.subtrees,
    isHorizonLeafFor horizonCat n ∧
    SO.cCommandsIn root n target ∧
    SO.cCommandsIn root probe n)
    Multiset.decidableExistsMultiset

-- ============================================================================
-- § 4: Feature Valuation
-- ============================================================================

/-- Apply Agree: value the probe's feature from the goal.
    Matching is by *dimension* (`ftype.dimension`), so a probe with
    `[uPerson:_]` is valued by a goal with `[Person:3rd]` — the placeholder
    value is irrelevant. If the goal has a valued feature at the dimension and
    the probe's slot there is unvalued, the probe's slot is set to that value. -/
def applyAgree (probeFeats goalFeats : FeatureBundle) (ftype : FeatureVal) :
    Option FeatureBundle :=
  match getValuedFeature goalFeats ftype with
  | none => none
  | some v =>
    some <| if (probeFeats ftype.dimension).isUnvalued
            then Function.update probeFeats ftype.dimension (.valued v)
            else probeFeats

-- ============================================================================
-- § 5: Common Agree Configurations
-- ============================================================================

/-- T-Agree: T probes for φ-features on subject DP

    T has [uφ], subject DP has [φ] → T gets valued φ.
    The `.third` value on person probes is a conventional placeholder —
    `sameType` ignores the specific `Person` value, matching any
    `.person _` against any `.person _`. -/
structure TAgree where
  tHead : SyntacticObject
  subject : SyntacticObject
  tFeatures : FeatureBundle
  subjFeatures : FeatureBundle
  -- T has unvalued phi
  t_has_uphi : hasUnvaluedFeature tFeatures (.phi (.person .third)) = true ∨
               hasUnvaluedFeature tFeatures (.phi (.number .singular)) = true
  -- Subject has valued phi
  subj_has_phi : hasValuedFeature subjFeatures (.phi (.person .third)) = true ∨
                 hasValuedFeature subjFeatures (.phi (.number .singular)) = true

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
  match fb .epp with
  | .valued b => b
  | .unvalued => true
  | .absent => false

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
  .ofGramFeatures [.unvalued (.q false), .valued (.epp true)]

/-- Embedded C features: [uQ] only (satisfied by wh-movement) -/
def embeddedCFeatures : FeatureBundle :=
  .ofGramFeatures [.unvalued (.q false)]

/-- Matrix C triggers T-to-C -/
theorem matrix_triggers_t_to_c : tToCTriggered matrixCFeatures = true := rfl

/-- Embedded C does not trigger T-to-C -/
theorem embedded_no_t_to_c : tToCTriggered embeddedCFeatures = false := rfl

-- ============================================================================
-- § 8: Activity Condition ([chomsky-2000], 2001)
-- ============================================================================

/-- Is a feature bundle active? (has at least one unvalued feature)

    An element is active iff it has at least one unvalued feature.
    Typically, DPs are active when they have unvalued Case. -/
def isActive (fb : FeatureBundle) : Bool :=
  FeatureType.all.any λ t => (fb t).isUnvalued

/-- An element needs Case (has unvalued Case feature) -/
def needsCase (fb : FeatureBundle) : Bool :=
  (fb .case).isUnvalued

/-- An element has valued Case -/
def hasCase (fb : FeatureBundle) : Bool :=
  (fb .case).isValued

/-- Activity is typically determined by Case:
    A DP is active iff it lacks Case

    When a feature bundle contains only Case features, the bundle is active
    (has unvalued features) iff it needs Case (has unvalued Case). -/
theorem activity_via_case (fb : FeatureBundle)
    (h : ∀ t, t ≠ .case → fb t = .absent) :
    isActive fb ↔ needsCase fb := by
  unfold isActive needsCase
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨t, _, hUnval⟩
    by_cases ht : t = .case
    · exact ht ▸ hUnval
    · rw [h t ht] at hUnval; simp [Features.FeatureSlot.isUnvalued] at hUnval
  · intro hNeeds
    exact ⟨.case, by decide, hNeeds⟩

-- ============================================================================
-- § 9: Active Goal (for Agree with Activity)
-- ============================================================================

/-- A goal that satisfies the Activity Condition -/
structure ActiveGoal where
  goal : SyntacticObject
  goalFeatures : FeatureBundle
  isActive : isActive goalFeatures = true

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

-- Defective intervention ([chomsky-2000]) is a visible-but-inactive
-- closest goal absorbing the probe (`Probe.agree_eq_none_of_inactive`).
-- The former `MultipleAgree`/`DefectiveElement` reinventions (zero
-- consumers) were retired. Hiraiwa's Multiple Agree (simultaneous
-- valuation of *all* matching goals) is a transmission operation the
-- search-only `Probe` API does not model — see `Probe/Basic.lean`'s
-- scope note.

-- ============================================================================
-- § 12: Phase-Bounded Agree
-- ============================================================================

/-- Valid Agree with Phase Impenetrability Condition.

    Agree is blocked if the goal is frozen in a phase interior
    (`Phase.Impenetrable`, MCB eq 1.14.3). The `strength` parameter is
    **load-bearing**: `strong`/`weak` apply the PIC block, while
    `linearizationBound` ([sande-clem-dabkowski-2026]) drops it (locality is then
    enforced by Cyclic Linearization, not phasehood). -/
def validAgreeWithPIC (strength : PICStrength) (phases : List Phase)
    (rel : AgreeRelation) (root : SyntacticObject) : Prop :=
  validAgree rel root ∧
    match strength with
    | .linearizationBound => True
    | .strong | .weak => ¬∃ ph ∈ phases, ph.Impenetrable rel.goal

/-- PIC-bounded Agree with Activity Condition.

    The full Agree constraint: probe c-commands goal, feature matching holds,
    goal is active, AND no intervening phase boundary blocks the relation.
    See `validAgreeWithPIC` for the role of `strength`. -/
def fullAgree (strength : PICStrength) (phases : List Phase)
    (rel : AgreeRelation) (root : SyntacticObject) : Prop :=
  validAgreeWithActivity rel root ∧
    match strength with
    | .linearizationBound => True
    | .strong | .weak => ¬∃ ph ∈ phases, ph.Impenetrable rel.goal

-- ============================================================================
-- § 13: Clause-Typing Agree Configurations
-- ============================================================================

/-- Fin-Agree: Fin probes for [±finite] on its complement (TP). -/
def finAgreeFeatures (isFinite : Bool) : FeatureBundle :=
  .ofGramFeatures [.unvalued (.finite isFinite)]

/-- Force-Fin-Agree: Force/C probes for clause-type features on Fin. -/
def forceFinAgreeFeatures (isFactive : Bool) : FeatureBundle :=
  .ofGramFeatures [.unvalued (.factive isFactive)]

/-- Neg-Agree: Neg probes for [±neg], licensing sentential negation. -/
def negAgreeFeatures : FeatureBundle :=
  .ofGramFeatures [.unvalued (.neg true)]

/-- Rel-Agree: Rel probes for [±rel], licensing relative clause formation. -/
def relAgreeFeatures : FeatureBundle :=
  .ofGramFeatures [.unvalued (.rel true)]

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
-- § N: `applyAgree` as a Probe transmission (retire into the Probe API)
-- ============================================================================

/-- The φ-probe: relativized search ([bejar-rezac-2003]/[preminger-2014]) for a
    goal bearing a valued `ftype` feature. -/
def phiProbe (ftype : FeatureVal) : Probe FeatureBundle :=
  Probe.ofVis (fun gf => (getValuedFeature gf ftype).isSome)

/-- **`applyAgree` is the φ goal→probe transmission.** A φ-Agree is
    `Probe.transmit` of the φ-probe with the valuation `applyAgree`: search the
    goal sequence for a `ftype`-bearing goal, then value the probe's features
    from it. This recognizes the standalone `applyAgree` as the transmission
    step of the unified Agree operation (`Probe/Transmission.lean`), rather than
    a parallel mechanism. (The probe→goal direction — dependent case — and a
    full clause's worth of valuations are *folds* of `transmit`s: the
    composition axis, not a single transmit.) -/
theorem applyAgree_is_phi_transmit (probeFeats : FeatureBundle) (ftype : FeatureVal)
    {goals : List FeatureBundle} {gf : FeatureBundle}
    (h : (phiProbe ftype).search goals = some gf) :
    (phiProbe ftype).transmit (fun g pf => (applyAgree pf g ftype).getD pf)
        probeFeats goals
      = (applyAgree probeFeats gf ftype).getD probeFeats := by
  unfold phiProbe at h ⊢
  exact Probe.transmit_ofVis_eq_of_search h

end Minimalist
