import Linglib.Theories.Semantics.PossibilitySemantics.Epistemic

/-!
# Lifting Construction: From Boolean Algebras to Epistemic Ortholattices
@cite{holliday-mandelkern-2024} Definition 5.1, Lemma 5.4

The lifting construction connects Kripke possible-world semantics to
possibility semantics. Given a Boolean algebra B (propositions over worlds),
the epistemic extension lifts it to an ortholattice whose elements are
pairs (A, I) with ∅ ≠ A ⊆ I ⊆ W:

- **A** (actuality set): worlds compatible with what has been *settled*
- **I** (information set): worlds compatible with what is *known*

Compatibility: (A,I) ◇ (A',I') iff A ∩ A' ≠ ∅ ∧ A ⊆ I' ∧ A' ⊆ I
Accessibility: (A,I) R (A',I') iff A ⊆ A' ∧ I' ⊆ I

For the 2-world model W = {0, 1} with V(p) = {0}, the five possibilities are:
- x₁ = ({0}, {0})     — knows p
- x₂ = ({0}, {0,1})   — settled p, doesn't know
- x₃ = ({0,1}, {0,1}) — full uncertainty
- x₄ = ({1}, {0,1})   — settled ¬p, doesn't know
- x₅ = ({1}, {1})     — knows ¬p

This file verifies that the epistemic scale's compatibility and accessibility
relations match the lifting construction, and derives truth conditions for
p, □p, ◇p in terms of world membership in A and I.
-/

namespace Semantics.PossibilitySemantics

-- ════════════════════════════════════════════════════
-- § 1. World Membership Functions
-- ════════════════════════════════════════════════════

/-- World 0 (the p-world) is in the actuality set A(x). -/
def worldlyA0 : Poss5 → Bool
  | .x1 | .x2 | .x3 => true
  | .x4 | .x5 => false

/-- World 1 (the ¬p-world) is in the actuality set A(x). -/
def worldlyA1 : Poss5 → Bool
  | .x3 | .x4 | .x5 => true
  | .x1 | .x2 => false

/-- World 0 is in the information set I(x). -/
def worldlyI0 : Poss5 → Bool
  | .x1 | .x2 | .x3 | .x4 => true
  | .x5 => false

/-- World 1 is in the information set I(x). -/
def worldlyI1 : Poss5 → Bool
  | .x2 | .x3 | .x4 | .x5 => true
  | .x1 => false

-- ════════════════════════════════════════════════════
-- § 2. Derived Relations
-- ════════════════════════════════════════════════════

/-- Compatibility derived from lifting: (A,I) ◇ (A',I') iff
    A ∩ A' ≠ ∅ ∧ A ⊆ I' ∧ A' ⊆ I.
    @cite{holliday-mandelkern-2024} Definition 5.1. -/
def liftedCompat (x y : Poss5) : Bool :=
  -- A ∩ A' ≠ ∅ (share at least one actual world)
  ((worldlyA0 x && worldlyA0 y) || (worldlyA1 x && worldlyA1 y)) &&
  -- A ⊆ I' (x's actual worlds are in y's information)
  ((!worldlyA0 x || worldlyI0 y) && (!worldlyA1 x || worldlyI1 y)) &&
  -- A' ⊆ I (y's actual worlds are in x's information)
  ((!worldlyA0 y || worldlyI0 x) && (!worldlyA1 y || worldlyI1 x))

/-- Accessibility derived from lifting: (A,I) R (A',I') iff
    A ⊆ A' ∧ I' ⊆ I (refining = expanding actuality, shrinking information).
    @cite{holliday-mandelkern-2024} Definition 5.1. -/
def liftedAccess (x y : Poss5) : Bool :=
  -- A ⊆ A' (y's actuality contains x's)
  ((!worldlyA0 x || worldlyA0 y) && (!worldlyA1 x || worldlyA1 y)) &&
  -- I' ⊆ I (y's information is contained in x's)
  ((!worldlyI0 y || worldlyI0 x) && (!worldlyI1 y || worldlyI1 x))

-- ════════════════════════════════════════════════════
-- § 3. Lifting Correctness
-- ════════════════════════════════════════════════════

/-- The epistemic scale's compatibility matches the lifting construction. -/
theorem compat_from_lifting (x y : Poss5) :
    epistemicScale.compat x y ↔ liftedCompat x y = true := by
  cases x <;> cases y <;> decide

/-- The epistemic scale's accessibility matches the lifting construction. -/
theorem access_from_lifting (x y : Poss5) :
    epistemicScale.access x y ↔ liftedAccess x y = true := by
  cases x <;> cases y <;> decide

-- ════════════════════════════════════════════════════
-- § 4. Truth from World Membership (Lemma 5.4)
-- ════════════════════════════════════════════════════

/-! @cite{holliday-mandelkern-2024} Lemma 5.4: truth at a possibility
    reduces to truth at worlds via the A and I sets.

    - propP x = true  iff  world 1 ∉ A(x)  (all actual worlds satisfy p)
    - □p x = true     iff  world 1 ∉ I(x)  (all information-accessible worlds satisfy p)
    - ◇p x = true     iff  world 0 ∈ A(x)  (some actual world satisfies p)
-/

/-- Truth from worlds: p holds at x iff the ¬p-world is not actual. -/
theorem boolean_truth_from_worlds (x : Poss5) :
    propP x ↔ worldlyA1 x = false := by
  cases x <;> decide

/-- Box truth from worlds: □p holds at x iff the ¬p-world is not
    information-accessible. -/
theorem box_truth_from_worlds (x : Poss5) :
    box epistemicScale propP x ↔ worldlyI1 x = false := by
  cases x <;> decide

/-- Diamond truth from worlds: ◇p holds at x iff the p-world is actual. -/
theorem diamond_truth_from_worlds (x : Poss5) :
    diamond epistemicScale propP x ↔ worldlyA0 x = true := by
  cases x <;> decide

end Semantics.PossibilitySemantics
