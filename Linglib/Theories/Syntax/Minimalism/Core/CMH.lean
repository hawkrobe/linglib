import Linglib.Theories.Syntax.Minimalism.Core.Basic

/-!
# The Categorial Merge Hypothesis @cite{newman-2024}

Core definitions from @cite{newman-2024}'s *When Arguments Merge*
(MIT Press, Linguistic Inquiry Monographs 88). The Categorial Merge
Hypothesis (CMH) reduces argument structure to three Merge features
on verbal heads, deriving the space of possible verb phrases from a
minimal functional hierarchy of V and v.

## Key Claims

1. **Three Merge features**: `[·D·]` (DP-specific), `[·X·]` (category-
   unspecified, for non-DPs), `[·V·]` (VP-merge, only on v).
2. **Feature Maximality**: A head can check at most one instance of each
   Merge feature type per derivational step.
3. **Non-DP First Theorem**: When V bears both `[·D·]` and `[·X·]`,
   the non-DP (XP) must merge first (as complement), the DP second (as
   specifier). Derived from Feature Maximality.
4. **VP-as-specifier**: When v introduces an XP via `[·X·]`, V must
   merge with the XP first, forcing VP to become a specifier of v
   (rather than its complement).
5. **Weak Economy**: At each derivational step, if two operations are
   both possible and one checks more features, prefer it — unless
   doing so bleeds the other (makes it impossible).
6. **Generalized Tucking In** (@cite{paille-2020}): Specifiers merge as
   close to the head as possible, tucking under previously merged
   specifiers.

## Architectural Note

The CMH's bipartite functional hierarchy (just V + v) is a *competitor*
to the more articulated Voice/Appl/v decomposition in `Voice.lean` and
`Applicative.lean` (which follow @cite{pylkkanen-2008} and
@cite{cuervo-2003}). Both are representable in linglib. The CMH argues
that Voice and Appl are just v heads with particular feature bundles;
the articulated view treats them as structurally distinct projections.

-/

namespace Minimalism.CMH

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
def isVerbalHead : Cat → Bool
  | .V => true
  | .v => true
  | _  => false

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

end Minimalism.CMH
