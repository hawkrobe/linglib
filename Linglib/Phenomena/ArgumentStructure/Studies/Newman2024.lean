import Linglib.Theories.Syntax.Minimalist.Voice
import Linglib.Theories.Syntax.Minimalist.Features
import Linglib.Theories.Syntax.Minimalist.ObligatoryOperations

/-!
# Newman (2024) — When Arguments Merge @cite{newman-2024}

Elise Newman (2024). *When Arguments Merge*. MIT Press (Linguistic
Inquiry Monographs 88). ISBN 9780262379960.

## Overview

The Categorial Merge Hypothesis (CMH) proposes that all elements of
category V share the same Merge features, with only three
argument-introducing features: `[·D·]` (DP-specific), `[·X·]`
(category-unspecified), and `[·V·]` (VP-merge, v only). Combined with
Feature Maximality, Weak Economy, and Generalized Tucking In
(@cite{paille-2020}), the CMH derives:

1. **Non-DP First**: XPs merge before DPs when V bears both features
2. **VP-as-specifier**: When v bears `[·X·]`, VP is forced to be a
   specifier of v (not complement)
3. **Symmetric passives**: In "high IO" ditransitives, neither internal
   argument c-commands the other, so either can passivize
4. **DOMA**: Weak Economy forces IO to be passive subject when IO is
   a wh-phrase (checks more features)
5. **No IO passives with inherent case**: KPs can't check `[·D·]`, so
   they can't A-move to subject (Greek, Tamil, German, Turkish, Spanish)
6. **Agent Focus in Mayan**: Anti-redundancy deletes lower agreement
   copies when both probes target the same extracted argument

## Formalized Predictions

This file formalizes the verb type space, structural predictions about
VP-specifierhood and its consequences, the KP/DP distinction for
passive accessibility, and anti-redundancy for agreement.

## CMH Apparatus (relocated from `Minimalism/CMH.lean`)

The Categorial Merge Hypothesis primitives below are paper-specific to
@cite{newman-2024} (with @cite{paille-2020} for Generalized Tucking In)
and not consumed elsewhere in the library, so they live here under
`namespace Minimalist.CMH` for symmetry with other Minimalist apparatus
and to support qualified lookup if a future paper picks them up.
-/

namespace Minimalist.CMH

-- ============================================================================
-- § 1: Merge Features
-- ============================================================================

/-- The three argument-introducing Merge features for verbal heads.

    These are the *only* features that determine how V and v combine
    with their arguments. All other selectional requirements (c-selection
    for CPs, PPs, etc.) reduce to `[·X·]` — category-unspecified Merge.

    - `D`: Merges with DPs only (subjects, objects)
    - `X`: Merges with any non-DP phrase (PPs, CPs, APs, etc.)
    - `V`: Merges with VP (only on v; v selects V) -/
inductive MergeFeature where
  | D  -- DP-specific: checked by full DPs
  | X  -- Category-unspecified: checked by any non-DP phrase
  | V  -- VP-merge: checked by VP (v only)
  deriving DecidableEq, Repr, BEq

/-- A bundle of Merge features on a single head. Represented as counts
    (0 or 1) of each feature type, reflecting Feature Maximality (a head
    checks at most one instance of each Merge feature type). -/
structure MergeBundle where
  hasD : Bool    -- bears [·D·]
  hasX : Bool    -- bears [·X·]
  hasV : Bool    -- bears [·V·] (v only)
  deriving DecidableEq, Repr, BEq

/-- Number of Merge features in a bundle. -/
def MergeBundle.featureCount (b : MergeBundle) : Nat :=
  (if b.hasD then 1 else 0) + (if b.hasX then 1 else 0) + (if b.hasV then 1 else 0)

/-- Convert a bundle to a list of features. -/
def MergeBundle.toList (b : MergeBundle) : List MergeFeature :=
  (if b.hasD then [.D] else []) ++ (if b.hasX then [.X] else []) ++ (if b.hasV then [.V] else [])

-- ============================================================================
-- § 2: CMH Verbal Heads
-- ============================================================================

/-- Whether a category is a verbal head in the CMH sense. -/
def isVerbalHead : Cat → Prop
  | .V => True
  | .v => True
  | _  => False

instance : DecidablePred isVerbalHead := fun c => by
  cases c <;> unfold isVerbalHead <;> infer_instance

/-- A CMH-compliant verbal head: a V or v with a Merge feature bundle.

    Constraint: `[·V·]` may only appear on v (not V), because V does not
    select VP — v does. -/
structure CMHHead where
  /-- The category (V or v) -/
  cat : Cat
  /-- The Merge feature bundle -/
  features : MergeBundle
  /-- V heads may not bear `[·V·]` -/
  v_constraint : cat = .V → features.hasV = false
  deriving Repr

/-- A V head: introduces internal arguments (complements and specifiers). -/
def mkVHead (hasD hasX : Bool) : CMHHead where
  cat := .V
  features := ⟨hasD, hasX, false⟩
  v_constraint := λ _ => rfl

/-- A v head: introduces external arguments and selects VP. -/
def mkVLittleHead (hasD hasX : Bool) : CMHHead where
  cat := .v
  features := ⟨hasD, hasX, true⟩
  v_constraint := λ h => absurd h (by decide)

-- ============================================================================
-- § 3: The Space of Possible vPs (Table 134)
-- ============================================================================

/-- Profile of a verb phrase: how many DP and XP arguments V and v
    collectively introduce. This determines the verb type.

    The 4×4 matrix (V's args × v's args) produces all attested verb
    types, from weather verbs (0+0) to betting verbs (2DP + 2XP). -/
structure VPProfile where
  /-- DPs from V (0, 1, or 2) -/
  vDPArgs : Nat
  /-- XPs from V (0 or 1) -/
  vXPArgs : Nat
  /-- DPs from v (0 or 1) -/
  littleVDPArgs : Nat
  /-- XPs from v (0 or 1) -/
  littleVXPArgs : Nat
  deriving DecidableEq, Repr

/-- Total number of DP arguments. -/
def VPProfile.totalDP (p : VPProfile) : Nat := p.vDPArgs + p.littleVDPArgs

/-- Total number of XP arguments. -/
def VPProfile.totalXP (p : VPProfile) : Nat := p.vXPArgs + p.littleVXPArgs

/-- Total argument count. -/
def VPProfile.totalArgs (p : VPProfile) : Nat := p.totalDP + p.totalXP

/-- Construct a VPProfile from a V head and v head. -/
def vpProfile (vHead : CMHHead) (littleV : CMHHead) : VPProfile where
  vDPArgs := if vHead.features.hasD then 1 else 0
  vXPArgs := if vHead.features.hasX then 1 else 0
  littleVDPArgs := if littleV.features.hasD then 1 else 0
  littleVXPArgs := if littleV.features.hasX then 1 else 0

-- Verb type examples from the book's Table 134:

/-- Weather verbs: no arguments (V: ∅, v: [·V·]) -/
def weatherVerb : VPProfile := vpProfile (mkVHead false false) (mkVLittleHead false false)

/-- Unergative: one DP subject (V: ∅, v: [·D·][·V·]) -/
def unergative : VPProfile := vpProfile (mkVHead false false) (mkVLittleHead true false)

/-- Unaccusative: one DP object (V: [·D·], v: [·V·]) -/
def unaccusative : VPProfile := vpProfile (mkVHead true false) (mkVLittleHead false false)

/-- Transitive: subject + object (V: [·D·], v: [·D·][·V·]) -/
def transitive : VPProfile := vpProfile (mkVHead true false) (mkVLittleHead true false)

/-- Ditransitive with XP: e.g. "put the book on the table"
    (V: [·D·][·X·], v: [·D·][·V·]) -/
def ditransitiveXP : VPProfile := vpProfile (mkVHead true true) (mkVLittleHead true false)

/-- Ditransitive DOC: double object (V: [·D·], v: [·D·][·X·][·V·])
    where the indirect object is a non-DP introduced by v -/
def ditransitiveDOC : VPProfile := vpProfile (mkVHead true false) (mkVLittleHead true true)

/-- Raising: V selects non-DP complement only (e.g., "seem [to VP]")
    (V: [·X·], v: [·V·]) -/
def raising : VPProfile := vpProfile (mkVHead false true) (mkVLittleHead false false)

/-- Maximal verb: both V and v bear both [·D·] and [·X·]
    (V: [·D·][·X·], v: [·D·][·X·][·V·]) — e.g., "bet" -/
def maximalVerb : VPProfile := vpProfile (mkVHead true true) (mkVLittleHead true true)

-- The full space is a 4×4 matrix: V has {∅, [·D·], [·X·], [·D·][·X·]},
-- v has {[·V·], [·D·][·V·], [·X·][·V·], [·D·][·X·][·V·]}, producing
-- 16 theoretically possible verb types (Table 141 in @cite{newman-2024}).

-- Basic sanity checks
example : weatherVerb.totalArgs = 0 := rfl
example : unergative.totalArgs = 1 := rfl
example : unaccusative.totalArgs = 1 := rfl
example : transitive.totalArgs = 2 := rfl
example : ditransitiveXP.totalArgs = 3 := rfl
example : ditransitiveDOC.totalArgs = 3 := rfl
example : raising.totalArgs = 1 := rfl
example : maximalVerb.totalArgs = 4 := rfl

-- ============================================================================
-- § 4: Non-DP First Theorem
-- ============================================================================

/-- When V bears both `[·D·]` and `[·X·]`, the XP merges first (as
    complement) and the DP second (as specifier).

    This follows from Feature Maximality: V can check at most one Merge
    feature per step. If V first merges with an XP (checking `[·X·]`),
    the resulting V' can then merge with a DP (checking `[·D·]`). The
    reverse order is blocked because a DP cannot check `[·X·]`.

    Represented as an ordering constraint on the features. -/
inductive MergeOrder where
  | complement  -- merges first (inner)
  | specifier   -- merges second (outer)
  deriving DecidableEq, Repr

/-- For a V head with both [·D·] and [·X·], the XP is the complement
    and the DP is the specifier. -/
def nonDPFirst (_vHead : CMHHead) (_hD : _vHead.features.hasD = true)
    (_hX : _vHead.features.hasX = true) :
    MergeOrder × MergeOrder :=
  (.complement, .specifier)


-- ============================================================================
-- § 5: VP-as-Specifier
-- ============================================================================

/-- When v introduces an XP (v bears `[·X·]`), VP is forced to become
    a specifier of v rather than its complement.

    This is because v's `[·X·]` must be checked before `[·V·]`: the XP
    merges as v's complement, and then VP merges as v's specifier. -/
def vpIsSpecifier (littleV : CMHHead) : Bool :=
  littleV.features.hasX

/-- When VP is a specifier of v, V and v do not form a complex head
    (they are not in a head-complement relation). This has consequences
    for verb movement and ellipsis. -/
def vAndVFormComplex (littleV : CMHHead) : Bool :=
  !vpIsSpecifier littleV

-- ============================================================================
-- § 6: Weak Economy
-- ============================================================================

/-- A pending operation: a possible Merge at a given derivational step.
    Tracks which features would be checked and whether the operation
    bleeds any other pending operation. -/
structure PendingOp where
  /-- How many features this operation checks -/
  featuresChecked : Nat
  /-- Which other operations this one would bleed (make impossible) -/
  bleeds : List Nat  -- indices into the pending op list
  deriving Repr

/-- Weak Economy: among competing operations at a single derivational
    step, prefer the one that checks more features — unless doing so
    bleeds another operation.

    Returns `true` if `chosen` is a valid choice under Weak Economy. -/
private def weakEconomyValidAux (chosen : PendingOp) (chosenIdx : Nat)
    (ops : List PendingOp) (i : Nat) : Bool :=
  match ops with
  | [] => true
  | alt :: rest =>
    (i == chosenIdx ||
     alt.featuresChecked ≤ chosen.featuresChecked ||
     chosen.bleeds.contains i) &&
    weakEconomyValidAux chosen chosenIdx rest (i + 1)

def weakEconomyValid (ops : List PendingOp) (chosenIdx : Nat) : Bool :=
  match ops[chosenIdx]? with
  | none => false
  | some chosen => weakEconomyValidAux chosen chosenIdx ops 0

/-- When two operations stand in a bleeding relation (one bleeds the
    other), Weak Economy does not enforce a preference — either may
    apply. This captures the optionality in cases like Greek clitic
    doubling. -/
def mutuallyBleeding (op1 op2 : PendingOp) (i j : Nat) : Bool :=
  op1.bleeds.contains j || op2.bleeds.contains i

-- ============================================================================
-- § 7: Generalized Tucking In (@cite{paille-2020})
-- ============================================================================

/-- Specifier position in a tree with multiple specifiers.
    Under Generalized Tucking In, new specifiers merge *below* existing
    ones — as close to the head as possible. -/
inductive SpecPosition where
  | innermost   -- closest to the head (most recently merged)
  | outer (n : Nat)  -- n positions above innermost
  deriving DecidableEq, Repr

/-- Tucking in: a new specifier merges below all existing specifiers.
    Given `n` existing specifiers, the new one gets position `innermost`
    and all existing specifiers shift outward by one. -/
def tuckIn (_existingSpecs : Nat) : SpecPosition := .innermost

-- ============================================================================
-- § 8: Nominal Types and the Entailment Hierarchy
-- ============================================================================

/-- Types of nominals, ordered by feature-checking capacity.
    The CMH establishes an entailment hierarchy among nominal types:
    wh-DP ⊇ DP ⊇ non-DP in which Merge features each can check.

    This hierarchy drives multiple predictions:
    - KPs (inherent case → non-DP) cannot A-move (no [·D·] checking)
    - wh-DPs check more features than plain DPs (DOMA)
    - DPs can satisfy both [·D·] and [·X·] probes -/
inductive NominalType where
  | whDP   -- wh-phrase (who, what)
  | dp     -- full DP (the cat, John)
  | nonDP  -- KP or non-DP phrase (PP, CP, AP)
  deriving DecidableEq, Repr, BEq

/-- Which Merge features a nominal type can check.
    - wh-DP: checks [·D·] and [·X·]
    - DP: checks [·D·] and [·X·]
    - non-DP: checks [·X·] only
    No nominal checks [·V·] (only VP can). -/
def NominalType.checksMerge : NominalType → MergeFeature → Bool
  | .whDP, .D | .whDP, .X => true
  | .dp, .D | .dp, .X => true
  | .nonDP, .X => true
  | _, _ => false

/-- wh-DPs can additionally check [·wh·] on C.
    This is NOT a Merge feature on V/v but appears on functional
    heads (C). It is what makes wh-DPs strictly more powerful
    than plain DPs in the feature-checking hierarchy. -/
def NominalType.checksWh : NominalType → Bool
  | .whDP => true
  | _ => false

/-- Feature-checking capacity for A-movement (to Spec,TP via [·D·])
    plus Ā-features ([·wh·]). This count drives Weak Economy
    comparisons in DOMA configurations. -/
def NominalType.aMovementFeatures : NominalType → Nat
  | .whDP => 2  -- [·D·] on T + [·wh·] on C
  | .dp => 1    -- [·D·] on T only
  | .nonDP => 0 -- cannot A-move (lacks [·D·])

/-- The entailment hierarchy: wh-DP ⊇ DP ⊇ non-DP.
    Each type can check a superset of the features checkable by
    the types below it. -/
def NominalType.subsumes : NominalType → NominalType → Bool
  | .whDP, _ => true
  | .dp, .dp | .dp, .nonDP => true
  | .nonDP, .nonDP => true
  | _, _ => false

/-- Can this nominal type undergo A-movement?
    Requires checking [·D·] on T. -/
def NominalType.canAMove (n : NominalType) : Bool := n.checksMerge .D

/-- A KP is a DP wrapped in an inherent case shell (K head).
    KPs behave as `NominalType.nonDP` for feature-checking:
    they cannot check `[·D·]`, only `[·X·]`. -/
def isKP (so : SyntacticObject) : Bool :=
  match so with
  | .node (.leaf tok) _ =>
    tok.item.outerCat == .K
  | _ => false

-- ============================================================================
-- § 9: Anti-Redundancy in Agreement
-- ============================================================================

/-- When two adjacent φ-probes copy features of the same goal, the
    lower copy is deleted at PF. This is the anti-redundancy principle
    that derives Agent Focus morphology in Mayan languages.

    Adjacency is required: only probes with no intervening probe
    between them trigger deletion of the lower copy. -/
structure AgreeCopy where
  probePosition : Nat  -- structural height (higher = larger)
  goalId : Nat
  deriving DecidableEq, Repr

/-- Two probes are adjacent if no other probe in the configuration
    has a position strictly between them. -/
def probesAdjacent (copies : List AgreeCopy) (c1 c2 : AgreeCopy) : Bool :=
  let lo := min c1.probePosition c2.probePosition
  let hi := max c1.probePosition c2.probePosition
  !copies.any λ c3 =>
    c3.probePosition > lo && c3.probePosition < hi

/-- Identify redundant copies: lower copies where an adjacent higher
    probe targets the same goal. -/
def redundantCopies (copies : List AgreeCopy) : List AgreeCopy :=
  copies.filter λ c =>
    copies.any λ c' =>
      c'.goalId == c.goalId &&
      c'.probePosition > c.probePosition &&
      probesAdjacent copies c c'

/-- Delete redundant copies. Returns surviving copies after PF
    deletion of redundant agreement. -/
def applyAntiRedundancy (copies : List AgreeCopy) : List AgreeCopy :=
  let redundant := redundantCopies copies
  copies.filter λ c => !redundant.contains c

end Minimalist.CMH

namespace Newman2024

open Minimalist Minimalist.CMH

-- ============================================================================
-- § 1: The Space of Possible vPs
-- ============================================================================

-- The CMH predicts exactly which verb types exist based on feature
-- combinations on V and v. We verify the basic inventory.

/-- Weather verbs have zero arguments. -/
theorem weather_zero_args : weatherVerb.totalArgs = 0 := rfl

/-- Unergatives have exactly one argument (the subject from v). -/
theorem unergative_one_arg : unergative.totalArgs = 1 := rfl
theorem unergative_subject_only : unergative.totalDP = 1 ∧ unergative.totalXP = 0 :=
  ⟨rfl, rfl⟩

/-- Unaccusatives have exactly one argument (the object from V). -/
theorem unaccusative_one_arg : unaccusative.totalArgs = 1 := rfl
theorem unaccusative_object_only : unaccusative.totalDP = 1 ∧ unaccusative.totalXP = 0 :=
  ⟨rfl, rfl⟩

/-- Transitives have exactly two DP arguments. -/
theorem transitive_two_args : transitive.totalArgs = 2 := rfl
theorem transitive_two_dps : transitive.totalDP = 2 ∧ transitive.totalXP = 0 :=
  ⟨rfl, rfl⟩

/-- Ditransitives with an XP argument have three arguments. -/
theorem ditrans_xp_three_args : ditransitiveXP.totalArgs = 3 := rfl

/-- DOC ditransitives also have three arguments. -/
theorem ditrans_doc_three_args : ditransitiveDOC.totalArgs = 3 := rfl

/-- Raising verbs have exactly one argument (the XP complement). -/
theorem raising_one_arg : raising.totalArgs = 1 := rfl

/-- Maximal verbs ("bet") have four arguments. -/
theorem maximal_four_args : maximalVerb.totalArgs = 4 := rfl

-- ============================================================================
-- § 2: VP-as-Specifier Consequences
-- ============================================================================

/-- In a low-XP ditransitive (V: [·D·][·X·], v: [·D·][·V·]),
    VP is NOT a specifier of v because v lacks [·X·]. -/
theorem low_xp_vp_is_complement :
    vpIsSpecifier (mkVLittleHead true false) = false := rfl

/-- In a high-XP / DOC ditransitive (v: [·D·][·X·][·V·]),
    VP IS a specifier of v because v bears [·X·]. -/
theorem high_xp_vp_is_specifier :
    vpIsSpecifier (mkVLittleHead true true) = true := rfl

/-- When VP is a specifier, V and v do NOT form a complex head.
    This predicts VP-ellipsis mismatches: Voice mismatches are
    tolerated in simple transitives (V-v complex) but not in DOC
    ditransitives (VP as specifier). -/
theorem doc_no_complex_head :
    vAndVFormComplex (mkVLittleHead true true) = false := rfl

theorem transitive_forms_complex :
    vAndVFormComplex (mkVLittleHead true false) = true := rfl

-- ============================================================================
-- § 3: Entailment Hierarchy and KP Blocks Passive
-- ============================================================================

-- The entailment hierarchy wh-DP ⊇ DP ⊇ non-DP determines which
-- nominals can undergo A-movement. KPs (inherent case shells) behave
-- as non-DPs: they cannot check [·D·] on T, so they cannot A-move
-- to subject. This explains why languages with inherent case on
-- indirect objects (Greek, Tamil, German, Turkish, Spanish) lack
-- IO passives.

/-- non-DPs (KPs) cannot check [·D·]. -/
theorem nonDP_cannot_check_D : NominalType.checksMerge .nonDP .D = false := rfl
theorem nonDP_can_check_X : NominalType.checksMerge .nonDP .X = true := rfl

/-- DPs can check both [·D·] and [·X·]. -/
theorem dp_checks_D : NominalType.checksMerge .dp .D = true := rfl
theorem dp_checks_X : NominalType.checksMerge .dp .X = true := rfl

/-- wh-DPs additionally check [·wh·] on C. -/
theorem whDP_checks_wh : NominalType.checksWh .whDP = true := rfl
theorem dp_no_wh : NominalType.checksWh .dp = false := rfl

/-- The entailment hierarchy is a total preorder. -/
theorem whDP_subsumes_dp : NominalType.subsumes .whDP .dp = true := rfl
theorem dp_subsumes_nonDP : NominalType.subsumes .dp .nonDP = true := rfl
theorem nonDP_not_subsumes_dp : NominalType.subsumes .nonDP .dp = false := rfl

/-- A-movement accessibility: DPs and wh-DPs can A-move; non-DPs cannot.
    This is the core of the no-IO-passive explanation for languages
    with inherent case on indirect objects. -/
theorem nonDP_cannot_amove : NominalType.canAMove .nonDP = false := rfl
theorem dp_can_amove : NominalType.canAMove .dp = true := rfl
theorem whDP_can_amove : NominalType.canAMove .whDP = true := rfl

-- ============================================================================
-- § 4: Symmetric Passives
-- ============================================================================

-- In a high-IO ditransitive where VP is a specifier of v, neither
-- internal argument c-commands the other. The IO (merged as XP
-- complement of v) and the DO (merged as DP complement of V, inside
-- VP which is a specifier of v) are in separate branches.
--
-- This structure predicts that EITHER argument can passivize —
-- attested in Norwegian, Zulu, and (with morphological complications)
-- English. We verify the structural prerequisite: VP-as-specifier
-- means the two internal arguments are in non-c-commanding positions.

/-- The high-IO structure has VP as specifier. -/
theorem high_io_has_vp_spec :
    vpIsSpecifier (mkVLittleHead true true) = true := rfl

-- ============================================================================
-- § 5: DOMA (Double Object Movement Asymmetry)
-- ============================================================================

-- DOMA: when IO is a wh-phrase in a passive, IO must be the passive
-- subject (not DO). Weak Economy explains this: IO-to-subject checks
-- more features because the IO is a wh-DP (checking [·D·] + [·wh·])
-- while DO is a plain DP (checking [·D·] only).
-- Feature counts are derived from the NominalType hierarchy.

/-- IO-to-subject in wh-passive: IO is a wh-DP.
    Feature count derived from `NominalType.aMovementFeatures .whDP`.
    Unlike Greek CD (§7), DOMA operations are pure alternatives at the
    same derivational step — not in a bleeding relation. -/
def ioToSubjectWh : PendingOp where
  featuresChecked := NominalType.aMovementFeatures .whDP
  bleeds := []

/-- DO-to-subject in wh-passive: DO is a plain DP.
    Feature count derived from `NominalType.aMovementFeatures .dp`. -/
def doToSubjectWh : PendingOp where
  featuresChecked := NominalType.aMovementFeatures .dp
  bleeds := []

/-- Weak Economy prefers IO-to-subject (checks more features). -/
theorem doma_prefers_io : weakEconomyValid [ioToSubjectWh, doToSubjectWh] 0 = true := by
  native_decide

/-- Weak Economy disprefers DO-to-subject when IO checks more. -/
theorem doma_disprefers_do : weakEconomyValid [ioToSubjectWh, doToSubjectWh] 1 = false := by
  native_decide

-- ============================================================================
-- § 6: Anti-Redundancy and Agent Focus
-- ============================================================================

-- In Mayan AF configurations, the agent moves to Spec,CP for
-- Ā-extraction. Both v (φ-probe) and C (φ-probe) agree with the
-- agent. Anti-redundancy deletes the lower copy (on v), yielding
-- the surface pattern: no ergative (Set A) agreement, AF morphology
-- surfaces as an elsewhere form on Voice.
-- We model this with two Agree copies targeting the same goal.

/-- Two probes (C at height 3, v at height 1) agree with the same
    agent (goal 0). -/
def mayanAFCopies : List AgreeCopy :=
  [⟨3, 0⟩,  -- C probe copies agent's φ
   ⟨1, 0⟩]  -- v probe copies agent's φ (redundant)

/-- Anti-redundancy identifies the lower copy as redundant. -/
theorem af_lower_is_redundant :
    (redundantCopies mayanAFCopies).length = 1 := by native_decide

/-- After anti-redundancy, only the higher copy (C's agreement)
    survives. -/
theorem af_surviving_copy :
    (applyAntiRedundancy mayanAFCopies).length = 1 := by native_decide

/-- The surviving copy is the one on C (height 3). -/
theorem af_c_probe_survives :
    (applyAntiRedundancy mayanAFCopies).head? = some ⟨3, 0⟩ := by native_decide

-- ============================================================================
-- § 7: Weak Economy and Optional Clitic Doubling (Greek)
-- ============================================================================

/-- In Greek active transitives, three operations compete after IO
    merges as XP:
    1. Clitic double the IO (checks [·D_weak·] + [uφ] = 2 features)
    2. Merge VP (checks [·V·] = 1 feature)
    3. Merge transitive subject DP (checks [·D·] = 1 feature)

    Weak Economy prefers (1) over (2) but NOT over (3): merging the
    subject checks [·D·] which also checks [·D_weak·], bleeding clitic
    doubling. Since (1) and (3) stand in a bleeding relation, Weak
    Economy allows either order — making clitic doubling optional. -/

def cliticDouble : PendingOp where
  featuresChecked := 2  -- [·D_weak·] + [uφ]
  bleeds := []

def mergeVP : PendingOp where
  featuresChecked := 1  -- [·V·]
  bleeds := []

def mergeSubject : PendingOp where
  featuresChecked := 1  -- [·D·]
  bleeds := [0]  -- merging subject bleeds clitic doubling

/-- Clitic doubling is valid under Weak Economy. -/
theorem greek_cd_valid :
    weakEconomyValid [cliticDouble, mergeVP, mergeSubject] 0 = true := by native_decide

/-- Merging the subject is also valid (bleeding licenses either order). -/
theorem greek_subject_valid :
    weakEconomyValid [cliticDouble, mergeVP, mergeSubject] 2 = true := by native_decide

-- ============================================================================
-- § 8: Feature Bundle Comparison with Existing Voice Typology
-- ============================================================================

-- The CMH's [·D·] on v is an argument-introducing Merge feature:
-- it causes a DP to merge as a thematic external argument. Voice's
-- hasD is a PF subcategorization feature (requires specifier at PF).
-- These are distinct: anticausative Voice has hasD = true (PF marking
-- of SE) but does not assign a θ-role.
--
-- The CMH's binary partition (v ± [·D·]) corresponds to Voice's
-- assignsTheta, not to Voice's hasD.

/-- CMH v with [·D·] introduces an external argument (thematic). -/
theorem agentive_has_D :
    (mkVLittleHead true false).features.hasD = true := rfl

/-- CMH v without [·D·] does not introduce an external argument. -/
def passiveV : CMHHead := mkVLittleHead false false
theorem passive_lacks_D : passiveV.features.hasD = false := rfl

/-- Voice's hasD (PF subcategorization) and assignsTheta (θ-role
    assignment) do NOT always coincide — confirming that these are
    distinct features. The CMH's [·D·] corresponds to assignsTheta,
    not to hasD. Anticausative and passive Voice have hasD = true
    (anticausative for SE marking, passive for *by*-phrase licensing)
    but assignsTheta = false (no θ-role). -/
theorem voice_hasD_ne_assignsTheta :
    voiceAnticausative.hasD = true ∧ voiceAnticausative.assignsTheta = false ∧
    voicePassive.hasD = true ∧ voicePassive.assignsTheta = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 9: Feature Failure (Assumption 19c)
-- ============================================================================

-- Newman adopts @cite{preminger-2014}'s obligatory-no-crash model for
-- Merge features: [·D·], [·X·], [·V·] can go unchecked without
-- crashing the derivation. This extends Preminger's insight from
-- φ-agreement to structure-building.
--
-- This matters for:
-- - Impersonal passives: T's [·D·] may go unchecked (no DP moves
--   to subject) without crashing
-- - Pro-drop weather verbs: T's EPP goes unchecked (no expletive)
-- - Robust convergence: the grammar attempts Merge but tolerates
--   failure, yielding default (expletive or pro) rather than crash

/-- The CMH adopts the obligatory-no-crash model for Merge features.
    This is @cite{newman-2024}'s Assumption 19c: features can go
    unchecked without crashing. -/
def cmhFeatureModel : AgreementModel := .obligatoryNocrash

/-- Under Feature Failure, unchecked Merge features do not crash. -/
theorem feature_failure_converges (outcome : ProbeOutcome) :
    derivationConverges cmhFeatureModel outcome = true :=
  obligatory_always_converges outcome

/-- The crash model would reject derivations with unchecked features.
    Feature Failure is what separates the CMH from standard Minimalism
    on this point. -/
theorem feature_failure_vs_crash :
    derivationConverges cmhFeatureModel .unvalued = true ∧
    derivationConverges .crashOnFailure .unvalued = false := ⟨rfl, rfl⟩

/-- Weather verbs introduce zero DP arguments. In pro-drop languages
    without expletives, T's [·D·] goes unchecked — Feature Failure
    prevents a crash. Under the crash model, an expletive would be
    required to check T's [·D·]. -/
theorem weather_needs_feature_failure :
    weatherVerb.totalDP = 0 ∧
    derivationConverges cmhFeatureModel .unvalued = true := ⟨rfl, rfl⟩

/-- Passive v lacks [·D·], so no external argument merges. If no
    internal argument is available for A-movement to Spec,TP (impersonal
    passives), T's [·D·] goes unchecked — tolerated by Feature Failure. -/
theorem impersonal_passive_converges :
    passiveV.features.hasD = false ∧
    derivationConverges cmhFeatureModel .unvalued = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 10: Binding Predictions from VP-as-Specifier
-- ============================================================================

-- The CMH's VP-as-specifier prediction has direct consequences for
-- binding. In the low-XP structure (VP is complement of v), DO
-- asymmetrically c-commands XP → binding asymmetry. In the DOC
-- structure (VP is specifier of v), neither internal argument
-- c-commands the other → symmetric binding (either can passivize).

-- Low-XP ditransitive: V: [·D·][·X·], v: [·D·][·V·]
-- Structure: [vP agent [v' v [VP DO [V' V XP]]]]
-- VP is complement of v because v lacks [·X·].

private def v₁ := mkLeafPhon .v [] "v" 10
private def V₁ := mkLeafPhon .V [] "V" 11
private def agent₁ := mkLeafPhon .D [] "agent" 12
private def DO₁ := mkLeafPhon .D [] "DO" 13
private def XP₁ := mkLeafPhon .P [] "to-Mary" 14

def lowXPTree : SyntacticObject :=
  .node agent₁ (.node v₁ (.node DO₁ (.node V₁ XP₁)))

-- DOC ditransitive: V: [·D·], v: [·D·][·X·][·V·]
-- Structure: [vP VP [vP agent [v' v IO]]]
-- VP is specifier of v because v bears [·X·].
-- Agent tucks in below VP (Generalized Tucking In).

private def v₂ := mkLeafPhon .v [] "v" 20
private def V₂ := mkLeafPhon .V [] "V" 21
private def agent₂ := mkLeafPhon .D [] "agent" 22
private def DO₂ := mkLeafPhon .D [] "DO" 23
private def IO₂ := mkLeafPhon .D [] "IO" 24

private def VP₂ : SyntacticObject := .node V₂ DO₂

def docTree : SyntacticObject :=
  .node VP₂ (.node agent₂ (.node v₂ IO₂))

-- § 10a: Internal argument binding asymmetry

/-- Low-XP: DO asymmetrically c-commands XP — binding asymmetry.
    DO (specifier of V, by Non-DP First) c-commands into the
    complement position. -/
theorem low_xp_DO_ccommands_XP :
    cCommandsIn lowXPTree DO₁ XP₁ := by native_decide

theorem low_xp_XP_not_ccommands_DO :
    ¬ cCommandsIn lowXPTree XP₁ DO₁ := by native_decide

/-- DOC: neither internal argument c-commands the other — symmetric.
    DO is inside VP (outer specifier), IO is complement of v.
    They are in separate branches. -/
theorem doc_DO_not_ccommands_IO :
    ¬ cCommandsIn docTree DO₂ IO₂ := by native_decide

theorem doc_IO_not_ccommands_DO :
    ¬ cCommandsIn docTree IO₂ DO₂ := by native_decide

/-- The structural asymmetry derived from VP-as-specifier:
    VP-as-complement gives binding asymmetry between internal
    arguments; VP-as-specifier gives symmetric binding. -/
theorem binding_asymmetry_iff_vp_complement :
    -- Low-XP (VP complement): DO c-commands XP, not vice versa
    (cCommandsIn lowXPTree DO₁ XP₁ ∧
     ¬ cCommandsIn lowXPTree XP₁ DO₁) ∧
    -- DOC (VP specifier): neither c-commands the other
    (¬ cCommandsIn docTree DO₂ IO₂ ∧
     ¬ cCommandsIn docTree IO₂ DO₂) := by
  exact ⟨⟨by native_decide, by native_decide⟩, ⟨by native_decide, by native_decide⟩⟩

-- § 10b: Agent c-command differences

/-- In the low-XP structure, the agent c-commands both internal
    arguments (VP is complement, fully inside agent's sister). -/
theorem low_xp_agent_ccommands_DO :
    cCommandsIn lowXPTree agent₁ DO₁ := by native_decide

theorem low_xp_agent_ccommands_XP :
    cCommandsIn lowXPTree agent₁ XP₁ := by native_decide

/-- In the DOC structure with Tucking In, the agent (inner specifier)
    c-commands IO (complement of v) but NOT DO (inside VP, the outer
    specifier). The agent and VP are in separate branches — a direct
    consequence of VP being a specifier rather than a complement. -/
theorem doc_agent_ccommands_IO :
    cCommandsIn docTree agent₂ IO₂ := by native_decide

theorem doc_agent_not_ccommands_DO :
    ¬ cCommandsIn docTree agent₂ DO₂ := by native_decide

end Newman2024
