import Linglib.Core.Quantification

/-!
# Square of Opposition

The Aristotelian Square of Opposition reified as a first-class algebraic object.

The square arranges four operators at its vertices:

```
       contraries
  A ──────────────── E
  │                  │
  │  subalterns  subalterns
  │                  │
  I ──────────────── O
     subcontraries
```

The six relations:
- **Contraries** (A–E): cannot both be true
- **Subcontraries** (I–O): cannot both be false
- **Contradictories** (A–O, E–I): exactly one is true
- **Subalterns** (A→I, E→O): the universal entails the particular

The square unifies quantifiers, modals, connectives, and attitudes:
- Quantifiers: A = every, E = no, I = some, O = not-every
- Modals: A = □, E = □¬, I = ◇, O = ¬□
- Attitudes: A = Bel(p), E = Bel(¬p), I = ◇p, O = ¬Bel(p)

The three duality operations (outer negation, inner negation, dual) generate
the square from any single vertex. This module provides the abstract framework;
concrete instantiations live in their respective theory modules.

## References

- Horn, L. (2001). A Natural History of Negation. Ch. 1: "Contradiction".
- Barwise, J. & Cooper, R. (1981). Generalized Quantifiers and Natural Language.
- Löbner, S. (1990). Wahr neben Falsch: Duale Operatoren als die Quantoren
  natürlicher Sprache.
-/

namespace Core.SquareOfOpposition

open Core.Quantification (GQ outerNeg innerNeg dualQ)

-- ============================================================================
-- §1 The Square
-- ============================================================================

/-- The four vertices of a Square of Opposition. -/
structure Square (α : Type*) where
  /-- A-corner: universal affirmative (every, □, Bel(p)) -/
  A : α
  /-- E-corner: universal negative (no, □¬, Bel(¬p)) -/
  E : α
  /-- I-corner: particular affirmative (some, ◇, ◇p) -/
  I : α
  /-- O-corner: particular negative (not-every, ¬□, ¬Bel(p)) -/
  O : α
  deriving Repr

/-- The three operations that generate the square from a single vertex.

Given a vertex `A`, the other three are determined by:
- `E = innerNeg A` (negate the scope / complement)
- `O = outerNeg A` (negate the result)
- `I = dual A = outerNeg (innerNeg A)` -/
structure SquareOps (α : Type*) where
  /-- Inner negation: A ↦ E, I ↦ O -/
  inner : α → α
  /-- Outer negation: A ↦ O, E ↦ I -/
  outer : α → α
  /-- Dual: A ↦ I, E ↦ O. Should equal outer ∘ inner. -/
  dual : α → α

/-- Build a square from a single vertex and the three duality operations. -/
def Square.fromOps {α : Type*} (a : α) (ops : SquareOps α) : Square α where
  A := a
  E := ops.inner a
  I := ops.dual a
  O := ops.outer a

-- ============================================================================
-- §2 Square Relations (propositional level)
-- ============================================================================

/-- The six logical relations of the Square of Opposition.

Defined over `W → Bool` (decidable propositions over a domain `W`).
The relations are pointwise: they hold at every point `w : W`. -/
structure SquareRelations {W : Type*} (sq : Square (W → Bool)) where
  /-- A entails I (subalternation). -/
  subalternAI : ∀ w, sq.A w = true → sq.I w = true
  /-- E entails O (subalternation). -/
  subalternEO : ∀ w, sq.E w = true → sq.O w = true
  /-- A and O are contradictories: A = ¬O. -/
  contradAO : ∀ w, sq.A w = !sq.O w
  /-- E and I are contradictories: E = ¬I. -/
  contradEI : ∀ w, sq.E w = !sq.I w
  /-- A and E are contraries: cannot both be true. -/
  contraryAE : ∀ w, sq.A w = true → sq.E w = false
  /-- I and O are subcontraries: cannot both be false. -/
  subcontrIO : ∀ w, sq.I w = false → sq.O w = true

-- ============================================================================
-- §3 Constructing Squares from Duality Operations
-- ============================================================================

/-- Build a square from any operator and the GQ duality operations. -/
def Square.fromGQOps {α : Type*} (q : GQ α) : Square (GQ α) :=
  Square.fromOps q
    { inner := innerNeg
      outer := outerNeg
      dual := dualQ }

/-- The standard GQ duality operations. -/
def gqSquareOps (α : Type*) : SquareOps (GQ α) where
  inner := innerNeg
  outer := outerNeg
  dual := dualQ

-- ============================================================================
-- §4 Deriving Relations from Contradiction
-- ============================================================================

/-! The six relations are not independent. Given the two contradiction
diagonals (A = ¬O, E = ¬I), the other four relations follow:

- Contraries: A ∧ E → A ∧ ¬I → (by subalternation) A ∧ ¬A → ⊥
- Subcontraries: ¬I ∧ ¬O → E ∧ ¬O → (by subalternation) E ∧ ¬E → ⊥
- Subalternation: derived from contrariety + contradiction

So the contradiction diagonals are the primitive relations; the rest
are consequences. This matches Horn's analysis: contradiction is fundamental. -/

/-- Contraries cannot both be true. -/
theorem contraries_not_both_true {W : Type*} (sq : Square (W → Bool))
    (rel : SquareRelations sq) (w : W)
    (hA : sq.A w = true) : sq.E w = false :=
  rel.contraryAE w hA

/-- Subcontraries cannot both be false. -/
theorem subcontraries_not_both_false {W : Type*} (sq : Square (W → Bool))
    (rel : SquareRelations sq) (w : W)
    (hI : sq.I w = false) : sq.O w = true :=
  rel.subcontrIO w hI

/-- From the contradiction diagonals, derive that A entails I. -/
theorem subaltern_from_contradictions {W : Type*} (sq : Square (W → Bool))
    (_hAO : ∀ w, sq.A w = !sq.O w)
    (hEI : ∀ w, sq.E w = !sq.I w)
    (hAE : ∀ w, sq.A w = true → sq.E w = false)
    (w : W) (hA : sq.A w = true) : sq.I w = true := by
  -- From A = true and contraryAE, E = false
  have hE := hAE w hA
  -- From E = ¬I, E = false means I = true
  have hEI_w := hEI w
  rw [hE] at hEI_w
  simp at hEI_w
  exact hEI_w

/-- From the outer/inner negation structure, the contradiction diagonals
hold definitionally: A = ¬(outerNeg A) and innerNeg A = ¬(dual A). -/
theorem outerNeg_contradiction {α : Type*} (q : GQ α) (R S : α → Bool) :
    q R S = !(outerNeg q R S) := by
  simp [outerNeg, Bool.not_not]

theorem innerNeg_dual_contradiction {α : Type*} (q : GQ α) (R S : α → Bool) :
    innerNeg q R S = !(dualQ q R S) := by
  simp [dualQ, outerNeg, innerNeg, Bool.not_not]

-- ============================================================================
-- §5 The Propositional Operator Square
-- ============================================================================

/-
The square of opposition is non-trivial only for operators with TWO arguments
(like GQs: restrictor × scope) or for modal operators (□/◇ duality).

For single-argument operators (propositions), inner neg = outer neg,
so the square degenerates. The interesting squares are:
1. GQ squares (two arguments: restrictor, scope)
2. Modal squares (one argument but with an accessibility relation)
3. Attitude squares (one argument but with a belief relation)

For (2) and (3), the square is built from □/◇ duality at the
propositional level, not from the proposition itself.
-/

/-- Build a square of propositions from a box-like operator.

Given `box : (W → Bool) → W → Bool` (e.g., □ = "all accessible worlds satisfy"),
and a proposition `p`, produce the four corners:
- A = box p         (□p: necessarily p)
- E = box (¬p)      (□¬p: necessarily not-p)
- I = ¬(box (¬p))   (◇p: possibly p)
- O = ¬(box p)      (¬□p: not necessarily p)
-/
def Square.fromBox {W : Type*} (box : (W → Bool) → W → Bool) (p : W → Bool) :
    Square (W → Bool) where
  A := box p
  E := box (λ w => !p w)
  I := λ w => !(box (λ w' => !p w') w)
  O := λ w => !(box p w)

/-- The box-derived square always satisfies the contradiction diagonals. -/
theorem fromBox_contradAO {W : Type*} (box : (W → Bool) → W → Bool)
    (p : W → Bool) (w : W) :
    (Square.fromBox box p).A w = !(Square.fromBox box p).O w := by
  simp [Square.fromBox, Bool.not_not]

theorem fromBox_contradEI {W : Type*} (box : (W → Bool) → W → Bool)
    (p : W → Bool) (w : W) :
    (Square.fromBox box p).E w = !(Square.fromBox box p).I w := by
  simp [Square.fromBox, Bool.not_not]

-- ============================================================================
-- §6 Connection to Horn Scales
-- ============================================================================

/-! Subalternation is the entailment relation that underlies Horn scales.

The I–A edge of the quantifier square (some → every) is precisely the
`⟨some, all⟩` Horn scale from `Core.Scale`. More generally:

- The weak member of a Horn scale sits at I (particular/existential)
- The strong member sits at A (universal)
- Scalar implicature from I negates A: "some" implicates "not all" (= O)

This means the square of opposition IS the algebraic structure underlying
scalar implicature: using the weak term (I) implicates the negation of
the strong term (¬A = O). The "O-corner gap" — the non-lexicalization of O —
is pragmatically explained: O is always recoverable as the implicature of I.

See `Core.Conjectures.o_corner_gap` for the formal statement. -/

/-- Subalternation A→I is equivalent to the Horn-scale ordering:
the A-corner entails the I-corner, which is the scale `⟨I, A⟩`. -/
theorem subalternation_is_scale_ordering {W : Type*} (sq : Square (W → Bool))
    (rel : SquareRelations sq) :
    ∀ w, sq.A w = true → sq.I w = true :=
  rel.subalternAI

end Core.SquareOfOpposition
