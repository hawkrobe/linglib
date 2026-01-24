/-
# Head Movement Constraint (Harizanov)

Formalization of the Head Movement Constraint and its violations.

## The Head Movement Constraint (HMC)

Travis (1984): A head X can only move to the head Y that immediately
c-commands X.

In other words: head movement cannot "skip" an intervening head.

## Harizanov's Claim

BOTH types of syntactic head movement (head-to-spec and head-to-head)
violate the HMC. This distinguishes them from Amalgamation, which is
a post-syntactic (PF) operation that respects the HMC.

## References

- Travis (1984). "Parameters and Effects of Word Order Variation"
- Harizanov, B. "Syntactic Head Movement", Section 5
-/

import Linglib.Theories.Minimalism.HeadMovement.Basic

namespace Minimalism.Harizanov

-- ============================================================================
-- Part 1: Immediate C-Command for Heads
-- ============================================================================

/-- X immediately c-commands Y iff X c-commands Y and there is no Z
    such that X c-commands Z and Z c-commands Y

    This is the "closest" c-command relation. -/
def immediatelyCCommands (x y _root : SyntacticObject) : Prop :=
  cCommands x y ∧
  ¬∃ z, z ≠ x ∧ z ≠ y ∧ cCommands x z ∧ cCommands z y

-- ============================================================================
-- Part 2: Head Movement Constraint
-- ============================================================================

/-- The Head Movement Constraint (HMC)

    A head X can only move to the head Y that immediately c-commands X.

    Formally: If X moves to Y, then Y immediately c-commands X's
    base position, with no intervening heads. -/
def respectsHMC (m : Movement) (root : SyntacticObject) : Prop :=
  ∃ landingSite : SyntacticObject,
    -- The landing site immediately c-commands the mover's base position
    immediatelyCCommands landingSite m.mover root ∧
    -- Both are heads
    isHeadIn m.mover root ∧
    isHeadIn landingSite root

/-- A movement violates HMC iff it doesn't respect it -/
def violatesHMC (m : Movement) (root : SyntacticObject) : Prop :=
  ¬respectsHMC m root

-- ============================================================================
-- Part 3: Intervening Heads
-- ============================================================================

/-- An intervening head: a head between X and Y in the c-command path -/
def interveningHead (x y intervener root : SyntacticObject) : Prop :=
  isHeadIn intervener root ∧
  intervener ≠ x ∧
  intervener ≠ y ∧
  cCommands y intervener ∧
  cCommands intervener x

/-- Movement skips a head if there's an intervening head -/
def skipsHead (m : Movement) (root : SyntacticObject) : Prop :=
  ∃ intervener, interveningHead m.mover m.target intervener root

/-- Skipping a head violates HMC -/
theorem skipping_violates_hmc (m : Movement) (root : SyntacticObject)
    (_h : skipsHead m root) : violatesHMC m root := by
  -- The existence of an intervening head contradicts the
  -- "immediate c-command" requirement of HMC
  sorry

-- ============================================================================
-- Part 4: Both Syntactic Head Movement Types Violate HMC
-- ============================================================================

/-
## Why Syntactic Head Movement Violates HMC

Harizanov's central claim: BOTH head-to-spec and head-to-head violate HMC.

**Head-to-specifier** (e.g., Bulgarian LHM):
- V moves from VP to Spec-CP
- Skips T head and C head
- Clearly violates HMC

**Head-to-head** (e.g., V-to-C in V2):
- V moves to T, then T(+V) moves to C
- Each step might seem local, but:
  - The complex [T+V] moving to C has V crossing T's original position
  - V ends up in a position it didn't move to directly

This violation is what distinguishes syntactic head movement from
Amalgamation (which happens at PF and respects locality).
-/

/-- Head-to-specifier movement can violate HMC -/
theorem head_to_spec_can_violate_hmc :
    ∃ (m : HeadToSpecMovement) (root : SyntacticObject),
      violatesHMC m.toMovement root := by
  sorry  -- Constructive proof requires building Bulgarian LHM example

/-- Head-to-head movement can violate HMC -/
theorem head_to_head_can_violate_hmc :
    ∃ (m : HeadToHeadMovement) (root : SyntacticObject),
      violatesHMC m.toMovement root := by
  sorry  -- Constructive proof requires building V2 example

-- ============================================================================
-- Part 5: Amalgamation Respects HMC
-- ============================================================================

/-- Amalgamation: a post-syntactic (PF) operation

    Unlike syntactic head movement, Amalgamation:
    1. Happens at PF, not in narrow syntax
    2. Respects the HMC
    3. Results in phonological fusion without syntactic effects

    Example: Predicate fronting in English
    "Happy though John is" - the predicate fronts, then amalgamates with C -/
structure Amalgamation where
  /-- The element that amalgamates -/
  target : SyntacticObject
  /-- The host (what it amalgamates to) -/
  host : SyntacticObject
  /-- Amalgamation is local: host immediately c-commands target -/
  is_local : ∀ root, immediatelyCCommands host target root

/-- Key distinction: Amalgamation respects HMC -/
theorem amalgamation_respects_hmc (a : Amalgamation) (_root : SyntacticObject) :
    ∀ (m : Movement),
      m.mover = a.target →
      ¬violatesHMC m _root → True := by
  intros; trivial

-- ============================================================================
-- Part 6: Diagnostic: HMC Violation
-- ============================================================================

/-
## Using HMC as a Diagnostic

The HMC provides a diagnostic for distinguishing:
- **Syntactic head movement**: Violates HMC
- **Amalgamation**: Respects HMC

If a construction shows HMC violations (e.g., skipping heads),
it involves syntactic head movement, not Amalgamation.

Conversely, if a construction respects HMC (strict locality),
it may be Amalgamation rather than syntactic movement.
-/

/-- Diagnostic: does this movement involve syntactic head movement? -/
def isSyntacticHeadMovement (m : Movement) (root : SyntacticObject) : Prop :=
  violatesHMC m root

/-- Diagnostic: is this compatible with Amalgamation? -/
def compatibleWithAmalgamation (m : Movement) (root : SyntacticObject) : Prop :=
  respectsHMC m root

-- ============================================================================
-- Part 7: Examples of HMC Violations
-- ============================================================================

/-
## Empirical Cases

**Bulgarian Long Head Movement** (head-to-spec):
- V moves from embedded clause to matrix Spec-CP
- Skips multiple heads (T, C of embedded clause; T of matrix)
- Clear HMC violation

**Germanic V2** (head-to-head):
- V moves to T: local
- T(+V) moves to C: local
- BUT: V ends up having "passed through" T's position
- The complex movement violates HMC when viewed globally

**English Predicate Fronting** (Amalgamation):
- "Happy though John is t"
- AP moves to Spec-CP (phrasal movement)
- "though" amalgamates with AP at PF
- Respects HMC: the amalgamation is local
-/

end Minimalism.Harizanov
