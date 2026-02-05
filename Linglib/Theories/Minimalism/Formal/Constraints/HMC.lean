/-
# Head Movement Constraint (Harizanov)

Formalization of the Head Movement Constraint and its violations.

## The Head Movement Constraint (HMC)

Travis (1984): A head X can only move to the head Y that immediately
c-commands X.

In other words: head movement cannot "skip" an intervening head.

## Harizanov's Claim

Both types of syntactic head movement (head-to-spec and head-to-head)
violate the HMC. This distinguishes them from Amalgamation, which is
a post-syntactic (PF) operation that respects the HMC.

## References

- Travis (1984). "Parameters and Effects of Word Order Variation"
- Harizanov, B. "Syntactic Head Movement", Section 5
-/

import Linglib.Theories.Minimalism.Formal.HeadMovement.Basic

namespace Minimalism

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
-- Part 3: Head-to-Specifier Violates HMC
-- ============================================================================

/-
## Why Syntactic Head Movement Violates HMC

Harizanov's central claim: both head-to-spec and head-to-head violate HMC.

Head-to-specifier (e.g., Bulgarian LHM):
- V moves from VP to Spec-CP
- Skips T head and C head
- Clearly violates HMC

Head-to-head (e.g., V-to-C in V2):
- V moves to T, then T(+V) moves to C
- Each step might seem local, but:
  - The complex [T+V] moving to C has V crossing T's original position
  - V ends up in a position it didn't move to directly

This violation is what distinguishes syntactic head movement from
Amalgamation (which happens at PF and respects locality).
-/

/-- Head-to-specifier movement always violates HMC.

    From Harizanov (p.12, p.29): In head-to-specifier movement, the head X
    becomes a maximal projection in its derived position.

    This violates HMC because:
    - HMC requires `isHeadIn mover root`
    - `isHeadIn` requires `¬isMaximalIn mover root`
    - But head-to-spec movement is defined by `isMaximalIn mover result`
    - Therefore the mover is not a head in the result
    - Therefore HMC fails

    Any head-to-spec movement violates HMC, by the very definition of
    what head-to-spec movement is. -/
theorem head_to_spec_violates_hmc (m : HeadToSpecMovement) :
    violatesHMC m.toMovement m.result := by
  -- The mover is maximal in result (by definition of head-to-spec)
  -- But respectsHMC requires isHeadIn mover root
  -- And isHeadIn requires ¬isMaximalIn
  -- Contradiction.
  unfold violatesHMC respectsHMC
  intro ⟨_landingSite, _hImm, hMoverHead, _hLandingHead⟩
  -- hMoverHead : isHeadIn m.mover m.result
  -- But m.mover_is_maximal : isMaximalIn m.mover m.result
  unfold isHeadIn at hMoverHead
  obtain ⟨_hMin, hNotMax⟩ := hMoverHead
  exact hNotMax m.mover_is_maximal

-- ============================================================================
-- Part 4a: Position-Aware HMC Violation (for Multidominance)
-- ============================================================================

/-
## Position-Specific HMC Violation

The standard `head_to_spec_violates_hmc` uses global `isMaximalIn`.
In multidominant structures (copy theory), this fails because the mover
projects at its base position (in VP) even though it's maximal at its
derived position (Spec-CP).

The position-aware version captures Harizanov's insight that maximality
is evaluated at a specific position, not globally. The mover is maximal
"at its derived position" (p.29), which is sufficient to violate HMC.

HMC requires the mover to be a head at its landing site.
Being maximal at the landing site means not being a head there.
Position-specific maximality captures this correctly.
-/

/-- Position-aware HMC: a head must be non-maximal AT ITS POSITION -/
def respectsHMC_positional (m : Movement) (root : SyntacticObject) (pos : TreePos) : Prop :=
  ∃ landingSite : SyntacticObject,
    immediatelyCCommands landingSite m.mover root ∧
    isHeadIn m.mover root ∧
    isHeadIn landingSite root ∧
    -- Additionally: mover must not be maximal at this position
    ¬isMaximalAtPosition m.mover root pos

/-- Position-aware HMC violation -/
def violatesHMC_positional (m : Movement) (root : SyntacticObject) (pos : TreePos) : Prop :=
  ¬respectsHMC_positional m root pos

/-- Head-to-specifier movement (positional) violates HMC

    This version works correctly with multidominance:
    - The mover is maximal AT ITS DERIVED POSITION
    - This means it is not a head at that position
    - Therefore HMC fails for the derived position

    Unlike the global version, we don't need to claim global maximality. -/
theorem head_to_spec_violates_hmc_positional (m : HeadToSpecMovementPositional) :
    violatesHMC_positional m.toMovement m.result derivedSpecPosition := by
  unfold violatesHMC_positional respectsHMC_positional
  intro ⟨_landingSite, _hImm, _hMoverHead, _hLandingHead, hNotMax⟩
  -- hNotMax : ¬isMaximalAtPosition m.mover m.result derivedSpecPosition
  -- But m.mover_maximal_at_derived : isMaximalAtPosition m.mover m.result derivedSpecPosition
  exact hNotMax m.mover_maximal_at_derived

-- ============================================================================
-- Part 5: Amalgamation Respects HMC
-- ============================================================================

/-- Amalgamation: a post-syntactic (PF) operation

    Unlike syntactic head movement, Amalgamation:
    1. Happens at PF, not in narrow syntax
    2. Respects the HMC (is strictly local)
    3. Results in phonological fusion without syntactic effects

    From Harizanov (Section 3.3): Amalgamation "trades" the syntactic relation
    between a head X and the head Y of its complement for a PF relation of
    affixation. Since affixation requires adjacency, Amalgamation is strictly
    local and cannot skip intervening heads.

    Example: French V-to-T
    "Jean ne parlait pas français" - V amalgamates with T at PF -/
structure Amalgamation where
  /-- The element that amalgamates (the "target") -/
  target : SyntacticObject
  /-- The host (what it amalgamates to) -/
  host : SyntacticObject
  /-- Amalgamation is LOCAL: host immediately c-commands target.
      This is the defining property that distinguishes Amalgamation
      from syntactic head movement. -/
  is_local : ∀ root, immediatelyCCommands host target root

/-- Amalgamation cannot skip intervening elements.

    This formalizes Harizanov's claim (Section 3.3, p.15):
    "Amalgamation-based displacement obeys the Head Movement Constraint"

    The proof is immediate from the definition: Amalgamation requires
    `immediatelyCCommands host target root`, which by definition means
    there is NO z such that host c-commands z and z c-commands target.

    This is what distinguishes Amalgamation from syntactic head movement,
    which can skip intervening heads (as shown by Bulgarian LHM and V2). -/
theorem amalgamation_no_intervener (a : Amalgamation) (root : SyntacticObject) :
    ¬∃ z, z ≠ a.host ∧ z ≠ a.target ∧ cCommands a.host z ∧ cCommands z a.target := by
  have h := a.is_local root
  unfold immediatelyCCommands at h
  exact h.2

/-- If there's an intervening element, the displacement cannot be Amalgamation

    This provides a diagnostic: if we observe a head displacement that
    skips an intervening head, we know it must be syntactic movement,
    not Amalgamation.

    From Harizanov (Section 3.3): The properties of Amalgamation-based
    displacement "differ substantially from those of Internal Merge." -/
theorem intervener_rules_out_amalgamation
    (host target intervener root : SyntacticObject)
    (h_neq_host : intervener ≠ host)
    (h_neq_target : intervener ≠ target)
    (h_host_cmd : cCommands host intervener)
    (h_int_cmd : cCommands intervener target) :
    ¬∃ (a : Amalgamation), a.host = host ∧ a.target = target := by
  intro ⟨a, hHost, hTarget⟩
  have hLocal := a.is_local root
  unfold immediatelyCCommands at hLocal
  apply hLocal.2
  use intervener
  subst hHost hTarget
  exact ⟨h_neq_host, h_neq_target, h_host_cmd, h_int_cmd⟩

/-- Amalgamation respects locality (the host c-commands the target) -/
theorem amalgamation_host_ccommands_target (a : Amalgamation) (root : SyntacticObject) :
    cCommands a.host a.target := by
  have h := a.is_local root
  unfold immediatelyCCommands at h
  exact h.1

-- ============================================================================
-- Part 6: Diagnostic: HMC Violation
-- ============================================================================

/-
## Using HMC as a Diagnostic

The HMC provides a diagnostic for distinguishing:
- Syntactic head movement: Violates HMC
- Amalgamation: Respects HMC

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

Bulgarian Long Head Movement (head-to-spec):
- V moves from embedded clause to matrix Spec-CP
- Skips multiple heads (T, C of embedded clause; T of matrix)
- Clear HMC violation

Germanic V2 (head-to-head):
- V moves to T: local
- T(+V) moves to C: local
- V ends up having "passed through" T's position
- The complex movement violates HMC when viewed globally

English Predicate Fronting (Amalgamation):
- "Happy though John is t"
- AP moves to Spec-CP (phrasal movement)
- "though" amalgamates with AP at PF
- Respects HMC: the amalgamation is local
-/

end Minimalism
