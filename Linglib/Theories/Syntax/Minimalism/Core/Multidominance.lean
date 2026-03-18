import Linglib.Theories.Syntax.Minimalism.Core.Phase

/-!
# Multidominance
@cite{citko-2014}

Multiply dominated structures: syntactic objects shared between two
or more dominating nodes. A node is multiply dominated when it has
more than one mother — it is built once but structurally accessible
from multiple positions.

## Two PF Reduction Mechanisms

Natural languages have two independent ways to arrive at PF-reduced
representations (material interpreted but not pronounced):

- **Ellipsis**: material is built in full, then deleted at PF by an
  E-feature on a functional head (e.g., C^E deletes its TP complement).
- **Multidominance (MD)**: material is built only once and shared
  between two structural positions; pronounced at one only.

Both yield the same surface effect — PF reduction — but differ in
derivational cost. MD typically uses fewer Merge operations and fewer
lexical resources because the shared material is constructed once
rather than twice.

## Sharing Types

- **Non-bulk-sharing**: Individual functional heads (C, T) are multiply
  dominated, but the larger constituents containing them (CP, TP) are
  NOT shared. Each conjunct is a separate phrase.
- **Bulk-sharing**: An entire constituent (e.g., C') is multiply
  dominated. Both conjuncts share everything inside it.

## Representation

Since `SyntacticObject` is a tree (each node has exactly one parent),
multiply dominated nodes cannot be represented directly in the tree
type. Instead, we model MD as a property of COORDINATION structures:
a `SharedNode` records that a node occurring in two conjuncts is
structurally identical — built once and shared rather than duplicated.

## Connection to Position-Indexed Maximality

`Formal/HeadMovement/Basic.lean` defines position-indexed maximality
(`isMaximalAtPosition`) precisely to handle multidominance: the same
element can be maximal at its derived position (Spec) while projecting
at its base position (VP). The types here complement that treatment
by modeling the coordination-level sharing structure.
-/

namespace Minimalism

-- ============================================================================
-- § 1: PF Reduction Mechanisms
-- ============================================================================

/-- The two mechanisms of PF reduction.

    Both produce representations where material is interpreted but not
    pronounced. Economy governs the choice between them. -/
inductive PFReductionMechanism where
  /-- E-feature on a functional head triggers deletion of its complement
      at PF. The deleted material is built in full during the derivation. -/
  | ellipsis
  /-- A syntactic object is built once and shared between two dominating
      nodes. Pronounced at one position only. -/
  | multidominance
  deriving Repr, DecidableEq

-- ============================================================================
-- § 2: Sharing Types
-- ============================================================================

/-- How material is shared between conjuncts in an MD structure.

    The distinction is empirically motivated: coordinated wh-questions
    use non-bulk-sharing (individual heads shared), while coordinated
    sluices use bulk-sharing (entire C' shared). The two sharing types
    derive different syntactic and interpretive properties. -/
inductive SharingType where
  /-- Individual functional heads shared between conjuncts.
      Each conjunct remains a separate full phrase; only specific heads
      (e.g., C, T) are multiply dominated. -/
  | nonBulk
  /-- An entire constituent is shared between conjuncts.
      Both conjuncts dominate the same subtree, so they share all
      material inside it (C, TP, vP, VP, ...). -/
  | bulk
  deriving Repr, DecidableEq

-- ============================================================================
-- § 3: Shared Nodes
-- ============================================================================

/-- A node shared between two conjuncts in a coordination structure.

    The shared node is built once but is structurally accessible from
    both `parent1` and `parent2`. At PF, it is linearized once. -/
structure SharedNode where
  /-- The multiply dominated node -/
  node : SyntacticObject
  /-- Category of the shared node (if it has a label) -/
  category : Option Cat
  /-- The shared node is pronounced (has PF content) -/
  pronounced : Bool
  deriving Repr

-- ============================================================================
-- § 4: PF-Reduced Coordination
-- ============================================================================

/-- A coordination structure with PF reduction.

    Models a coordinate &P where material is either multiply dominated
    (shared between conjuncts) or elided by an E-feature. -/
structure PFReducedCoordination where
  /-- First conjunct -/
  conjunct1 : SyntacticObject
  /-- Second conjunct -/
  conjunct2 : SyntacticObject
  /-- PF reduction mechanism(s) used -/
  mechanisms : List PFReductionMechanism
  /-- Type of sharing (for MD structures) -/
  sharing : Option SharingType
  /-- Nodes that are shared or deleted -/
  sharedNodes : List SharedNode
  /-- PF output after reduction -/
  pfOutput : List String
  deriving Repr

/-- Does this coordination use multidominance? -/
def PFReducedCoordination.usesMD (c : PFReducedCoordination) : Bool :=
  c.mechanisms.any (· == .multidominance)

/-- Does this coordination use ellipsis? -/
def PFReducedCoordination.usesEllipsis (c : PFReducedCoordination) : Bool :=
  c.mechanisms.any (· == .ellipsis)

/-- Does this coordination use both MD and ellipsis? -/
def PFReducedCoordination.usesBoth (c : PFReducedCoordination) : Bool :=
  c.usesMD && c.usesEllipsis

-- ============================================================================
-- § 5: Multiple Wh-Fronting Parameter
-- ============================================================================

/-- The Multiple Wh-Fronting (MWF) parameter.

    Languages vary in whether multiple wh-specifiers at a phase edge
    are tolerable at PF:

    - **MWF languages** (e.g., Bulgarian, Romanian): a phase node with
      multiple wh-specifiers does NOT receive an asterisk at PF.
    - **Non-MWF languages** (e.g., English, German, Greek): a phase node
      with multiple wh-specifiers receives an asterisk, which is
      uninterpretable at PF, crashing the derivation.

    In non-MWF languages, structures with multiple wh-specifiers at a
    phase edge are only grammatical if the offending edge is deleted
    by ellipsis before PF interprets the asterisk. -/
structure MWFParameter where
  /-- Does this language allow multiple wh-fronting? -/
  allowsMWF : Bool
  deriving Repr, DecidableEq

/-- A phase edge has a MWF violation when it contains multiple
    wh-specifiers in a non-MWF language. -/
def mwfViolation (param : MWFParameter) (numWhSpecifiers : Nat) : Bool :=
  !param.allowsMWF && numWhSpecifiers > 1

/-- Ellipsis can repair a MWF violation by deleting the phase edge
    containing the offending multiple wh-specifiers. -/
def ellipsisRepairsMWF (param : MWFParameter) (numWhSpecs : Nat)
    (edgeDeleted : Bool) : Bool :=
  if mwfViolation param numWhSpecs then edgeDeleted
  else true

/-- No repair is needed if the language allows MWF. -/
theorem mwf_language_no_violation (param : MWFParameter)
    (h : param.allowsMWF = true) (n : Nat) :
    mwfViolation param n = false := by
  simp [mwfViolation, h]

/-- A single wh-specifier never causes a MWF violation. -/
theorem single_wh_no_violation (param : MWFParameter) :
    mwfViolation param 1 = false := by
  simp [mwfViolation]

/-- Zero wh-specifiers never cause a MWF violation. -/
theorem zero_wh_no_violation (param : MWFParameter) :
    mwfViolation param 0 = false := by
  simp [mwfViolation]

end Minimalism
