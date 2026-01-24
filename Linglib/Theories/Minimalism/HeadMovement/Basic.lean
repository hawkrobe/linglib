/-
# Head Movement Types (Harizanov)

Formalization of the two types of syntactic head movement.

## The Core Distinction

Harizanov argues for two distinct types of head movement:

1. **Head-to-Specifier**: Moved head becomes MAXIMAL in derived position
   - Example: Bulgarian Long Head Movement
   - The target Y projects; X is a specifier

2. **Head-to-Head (Reprojection)**: Moved head stays MINIMAL in derived position
   - Example: Germanic V2 (V-to-T-to-C)
   - The mover X reprojects; requires complex LIs

Both violate the Head Movement Constraint (HMC), distinguishing them from
Amalgamation (a post-syntactic PF operation that respects HMC).

## References

- Harizanov, B. "Syntactic Head Movement", Sections 3-4
-/

import Linglib.Theories.Minimalism.Labeling

namespace Minimalism.Harizanov

-- ============================================================================
-- Part 1: Movement as Internal Merge
-- ============================================================================

/-- A movement operation tracks the mover, target, and result -/
structure Movement where
  /-- The element that moves -/
  mover : SyntacticObject
  /-- The target (landing site structure) -/
  target : SyntacticObject
  /-- The resulting structure after movement -/
  result : SyntacticObject
  /-- The mover must be contained in the target (Internal Merge) -/
  mover_in_target : contains target mover
  /-- The result is formed by merging mover and target -/
  is_merge : result = merge mover target

-- ============================================================================
-- Part 2: Head-to-Specifier Movement
-- ============================================================================

/-- Head-to-specifier movement: mover becomes maximal

    In head-to-spec, the moved head X:
    1. Was a head in base position (+min, -max)
    2. Becomes a phrase in derived position (+max)
    3. The target Y projects (X is a specifier of Y)

    Example: Bulgarian LHM where V moves to Spec-CP -/
structure HeadToSpecMovement extends Movement where
  /-- Mover was a head in the target (before extraction) -/
  mover_was_head : isHeadIn mover target
  /-- In the result, mover is maximal (a phrase) -/
  mover_is_maximal : isMaximalIn mover result
  /-- The target projects (mover is a specifier) -/
  target_projects : projectsIn target result

/-- Key property: head-to-spec yields a maximal element -/
theorem head_to_spec_yields_maximal (m : HeadToSpecMovement) :
    isPhraseIn m.mover m.result :=
  m.mover_is_maximal

/-- Head-to-spec: the target determines the label -/
theorem head_to_spec_target_labels (m : HeadToSpecMovement) :
    sameLabel m.target m.result := by
  obtain ⟨_, hsame⟩ := m.target_projects
  exact hsame

-- ============================================================================
-- Part 3: Head-to-Head Movement (Reprojection)
-- ============================================================================

/-- Head-to-head movement: mover reprojects (stays minimal)

    In head-to-head, the moved head X:
    1. Was a head in base position (+min, -max)
    2. Stays a head in derived position (+min, -max)
    3. X reprojects: X's label becomes the label of the result
    4. Requires X to be (or become) a complex LI

    Example: V-to-T movement where V reprojects within the T complex -/
structure HeadToHeadMovement extends Movement where
  /-- Mover was a head in the target -/
  mover_was_head : isHeadIn mover target
  /-- In the result, mover is still minimal (still a head) -/
  mover_is_minimal : isMinimalIn mover result
  /-- Mover is NOT maximal (it projects/reprojects) -/
  mover_not_maximal : ¬isMaximalIn mover result
  /-- The mover's LI is complex (or becomes complex) -/
  mover_is_complex : ∃ tok, mover.getLIToken = some tok ∧ tok.item.isComplex

/-- Key property: head-to-head yields a minimal element -/
theorem head_to_head_yields_minimal (m : HeadToHeadMovement) :
    isMinimalIn m.mover m.result :=
  m.mover_is_minimal

/-- Head-to-head: the mover determines the label (reprojection) -/
theorem head_to_head_mover_labels (m : HeadToHeadMovement) :
    ∃ z, containsOrEq m.result z ∧ projectsIn m.mover z := by
  -- The mover projects in the result (by not being maximal)
  -- This follows from the definition of non-maximality
  sorry  -- Requires more detailed projection tracking

-- ============================================================================
-- Part 4: Complex LI Formation
-- ============================================================================

/-- When X moves to Y via head-to-head, Y absorbs X's features

    The target becomes a complex LI: [Y-features, X-features]
    This is how reprojection works: Y's category extends with X's -/
def formComplexLI (target mover : LIToken) : LIToken :=
  ⟨target.item.combine mover.item, target.id⟩  -- Keep target's identity

/-- Complex LI enables reprojection: the outer features project -/
theorem complex_li_outer_projects (target mover : LIToken) :
    (formComplexLI target mover).item.outerCat = target.item.outerCat := by
  simp [formComplexLI, LexicalItem.combine, LexicalItem.outerCat]
  cases htf : target.item.features with
  | nil => exact absurd htf target.item.nonempty
  | cons h t => simp

-- ============================================================================
-- Part 5: Distinguishing Properties
-- ============================================================================

/-- Summary of the two movement types -/
structure MovementTypeComparison where
  /-- Head-to-spec: mover ends up maximal -/
  h2s_maximal : ∀ m : HeadToSpecMovement, isMaximalIn m.mover m.result
  /-- Head-to-head: mover stays minimal -/
  h2h_minimal : ∀ m : HeadToHeadMovement, isMinimalIn m.mover m.result
  /-- Head-to-spec: target projects -/
  h2s_target_projects : ∀ m : HeadToSpecMovement, projectsIn m.target m.result
  /-- Head-to-head: mover reprojects (via complex LI) -/
  h2h_mover_reprojects : ∀ m : HeadToHeadMovement, ¬isMaximalIn m.mover m.result

/-- The key diagnostic -/
def movementType (mover_max : Bool) : String :=
  if mover_max then "head-to-specifier" else "head-to-head"

-- ============================================================================
-- Part 6: Interpretive Consequences
-- ============================================================================

/-
## Interpretive Differences

**Head-to-head** creates a single complex predicate:
- V-to-T: The verb and tense form a single predicate
- Morphologically: Often shows fusion/incorporation

**Head-to-specifier** keeps predicates separate:
- Two independent predication relations
- No morphological fusion expected

This is captured by the complex LI structure: in head-to-head,
the features are in a single LI; in head-to-spec, they remain separate.
-/

/-- Head-to-head results in a single complex LI (single predicate) -/
def isSinglePredicate (m : HeadToHeadMovement) : Prop :=
  ∃ tok, m.result.getLIToken = some tok ∧ tok.item.isComplex

/-- Head-to-spec keeps predicates separate -/
def areSeparatePredicates (m : HeadToSpecMovement) : Prop :=
  ∃ tok₁ tok₂,
    m.mover.getLIToken = some tok₁ ∧
    m.target.getLIToken = some tok₂ ∧
    tok₁ ≠ tok₂

-- ============================================================================
-- Part 7: Locality Differences
-- ============================================================================

/-
## Locality

**Head-to-head** is phase-bound:
- Must be local (within a phase)
- Blocked by Phase Impenetrability Condition (PIC)

**Head-to-specifier** can be long-distance:
- Can cross phase boundaries
- Similar to phrasal A'-movement

This explains why V-to-T-to-C is always local (head-to-head),
while Bulgarian LHM can be long-distance (head-to-spec).
-/

/-- A movement is local iff it doesn't cross a phase boundary -/
def isLocal (m : Movement) (phaseHead : SyntacticObject) : Prop :=
  -- The mover must not be "too deep" inside the target
  -- Specifically: if a phase head intervenes, movement is blocked
  ¬(contains m.target phaseHead ∧ contains phaseHead m.mover)

/-- Head-to-head must be local (phase-bound) -/
axiom head_to_head_is_local :
  ∀ (m : HeadToHeadMovement) (phaseHead : SyntacticObject),
    isLocal m.toMovement phaseHead

-- Head-to-spec can be non-local (No axiom requiring locality - it's permitted to be long-distance)

end Minimalism.Harizanov
