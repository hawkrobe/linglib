/-
# Containment Relations

Formalization of containment/dominance relations in Minimalist syntax.

## Key Definitions

- **Immediate Containment**: X immediately contains Y iff Y is a member of X
- **Containment (Dominance)**: Transitive closure of immediate containment
- **C-command**: Standard asymmetric relation for binding and locality

## References

- Chomsky, N. (1995). "The Minimalist Program"
- Adger, D. (2003). "Core Syntax", Chapter 3
-/

import Linglib.Theories.Minimalism.SyntacticObjects

namespace Minimalism

-- ============================================================================
-- Part 1: Immediate Containment (Definition 13)
-- ============================================================================

/-- X immediately contains Y iff Y is a member of X

    "X immediately contains Y iff X = {Y, Z} for some SO Z"

    Since our SOs are binary sets, this means Y is one of the
    two immediate daughters of X. -/
def immediatelyContains (x y : SyntacticObject) : Prop :=
  match x with
  | .leaf _ => False
  | .node a b => y = a ∨ y = b

/-- Decidable immediate containment -/
instance decImmediatelyContains (x y : SyntacticObject) :
    Decidable (immediatelyContains x y) := by
  unfold immediatelyContains
  cases x with
  | leaf _ => exact isFalse (λ h => h)
  | node a b =>
    cases h1 : decide (y = a) with
    | true =>
      simp at h1
      exact isTrue (Or.inl h1)
    | false =>
      simp at h1
      cases h2 : decide (y = b) with
      | true =>
        simp at h2
        exact isTrue (Or.inr h2)
      | false =>
        simp at h2
        exact isFalse (λ h => h.elim h1 h2)

-- ============================================================================
-- Part 2: Containment / Dominance (Definition 14)
-- ============================================================================

/-- Containment is the transitive closure of immediate containment

    "X contains Y iff X immediately contains Y or
    X immediately contains some SO Z such that Z contains Y"

    This is standard syntactic dominance. -/
inductive contains : SyntacticObject → SyntacticObject → Prop where
  | imm : ∀ x y, immediatelyContains x y → contains x y
  | trans : ∀ x y z, immediatelyContains x z → contains z y → contains x y

-- ============================================================================
-- Part 3: Properties of Containment
-- ============================================================================

/-- Immediate containment implies containment -/
theorem imm_implies_contains {x y : SyntacticObject}
    (h : immediatelyContains x y) : contains x y :=
  contains.imm x y h

/-- Containment is transitive -/
theorem contains_trans {x y z : SyntacticObject}
    (hxy : contains x y) (hyz : contains y z) : contains x z := by
  induction hxy with
  | imm x y himm =>
    exact contains.trans x z y himm hyz
  | trans x y w himm _ ih =>
    exact contains.trans x z w himm (ih hyz)

/-- Leaves contain nothing -/
theorem leaf_contains_nothing (tok : LIToken) (y : SyntacticObject) :
    ¬(contains (SyntacticObject.leaf tok) y) := by
  intro h
  cases h with
  | imm _ _ himm =>
    simp [immediatelyContains] at himm
  | trans _ _ z himm _ =>
    simp [immediatelyContains] at himm

-- ============================================================================
-- Part 3b: Well-Foundedness via nodeCount
-- ============================================================================

/-- Immediate containment strictly decreases nodeCount -/
theorem immediatelyContains_lt_nodeCount {x y : SyntacticObject}
    (h : immediatelyContains x y) : y.nodeCount < x.nodeCount := by
  cases x with
  | leaf _ => simp [immediatelyContains] at h
  | node a b =>
    simp only [immediatelyContains] at h
    simp only [SyntacticObject.nodeCount]
    rcases h with rfl | rfl
    · omega
    · omega

/-- Containment strictly decreases nodeCount -/
theorem contains_lt_nodeCount {x y : SyntacticObject}
    (h : contains x y) : y.nodeCount < x.nodeCount := by
  induction h with
  | imm x y himm =>
    exact immediatelyContains_lt_nodeCount himm
  | trans x y z himm _ ih =>
    have h1 := immediatelyContains_lt_nodeCount himm
    omega

/-- No element contains itself (containment is irreflexive) -/
theorem contains_irrefl (x : SyntacticObject) : ¬contains x x := by
  intro h
  have hlt := contains_lt_nodeCount h
  exact Nat.lt_irrefl _ hlt

-- ============================================================================
-- Part 4: Membership in Derivation
-- ============================================================================

/-- X is a term of Y iff X = Y or Y contains X

    "X is a term of SO Y iff X = Y or Y contains X"

    This is useful for stating when an element is "somewhere in" a structure -/
def isTermOf (x y : SyntacticObject) : Prop :=
  x = y ∨ contains y x

/-- Every SO is a term of itself -/
theorem self_is_term (x : SyntacticObject) : isTermOf x x :=
  Or.inl rfl

/-- If Y contains X, then X is a term of Y -/
theorem contained_is_term {x y : SyntacticObject} (h : contains y x) : isTermOf x y :=
  Or.inr h

-- ============================================================================
-- Part 5: Root and Reflexive Containment
-- ============================================================================

/-- Reflexive containment (useful for stating constraints) -/
def containsOrEq (x y : SyntacticObject) : Prop :=
  x = y ∨ contains x y

/-- Every SO reflexively contains itself -/
theorem refl_containsOrEq (x : SyntacticObject) : containsOrEq x x :=
  Or.inl rfl

/-- Reflexive containment is transitive -/
theorem containsOrEq_trans {x y z : SyntacticObject}
    (hxy : containsOrEq x y) (hyz : containsOrEq y z) : containsOrEq x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  · rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · exact Or.inr (contains_trans hxy hyz)

-- ============================================================================
-- Part 6: Sisters
-- ============================================================================

/-- X and Y are sisters iff they are immediately contained in the same SO

    "X and Y are sisters iff they are immediately contained in some SO Z" -/
def areSisters (x y : SyntacticObject) : Prop :=
  ∃ z, immediatelyContains z x ∧ immediatelyContains z y ∧ x ≠ y

/-- If a node has daughters a and b, they are sisters -/
theorem node_daughters_are_sisters (a b : SyntacticObject) (h : a ≠ b) :
    areSisters a b := by
  use .node a b
  constructor
  · simp [immediatelyContains]
  constructor
  · simp [immediatelyContains]
  · exact h

-- ============================================================================
-- Part 7: C-Command (Standard Definition)
-- ============================================================================

/-- X c-commands Y iff X's sister contains (or equals) Y

    Standard syntactic relation. X c-commands everything in its sister's
    projection. -/
def cCommands (x y : SyntacticObject) : Prop :=
  ∃ z, areSisters x z ∧ containsOrEq z y

/-- A node c-commands its sister -/
theorem ccommand_sister {x y : SyntacticObject} (h : areSisters x y) :
    cCommands x y :=
  ⟨y, h, Or.inl rfl⟩

-- C-command is not symmetric (in general)
-- This is expected: in {X, {Y, Z}}, X c-commands Y and Z,
-- but Y only c-commands Z (not X)

end Minimalism
