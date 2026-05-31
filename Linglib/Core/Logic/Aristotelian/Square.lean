import Linglib.Core.Logic.Quantification
import Linglib.Core.Logic.Aristotelian.Basic

/-!
# Square of Opposition

@cite{barwise-cooper-1981} @cite{horn-2001}. The Aristotelian square reified as an
algebraic object: four corners `A`, `E`, `I`, `O` over a Boolean algebra, related
by contradiction (A–O, E–I), contrariety (A–E), subcontrariety (I–O), and
subalternation (A→I, E→O). Concrete instantiations (quantifiers, modals,
attitudes) live in their respective theory modules.
-/

namespace Aristotelian

open Core.Quantification (GQ outerNeg innerNeg dualQ)

/-! ### The Square -/

/-- The four vertices of a Square of Opposition. -/
structure Square (α : Type*) where
  /-- A-corner: universal affirmative (every, □, Bel p). -/
  A : α
  /-- E-corner: universal negative (no, □¬, Bel ¬p). -/
  E : α
  /-- I-corner: particular affirmative (some, ◇, ◇p). -/
  I : α
  /-- O-corner: particular negative (not-every, ¬□, ¬Bel p). -/
  O : α
  deriving Repr

/-- The three operations generating the square from one vertex: `E = inner A`,
`O = outer A`, `I = dual A = outer (inner A)`. -/
structure SquareOps (α : Type*) where
  /-- Inner negation: A ↦ E, I ↦ O. -/
  inner : α → α
  /-- Outer negation: A ↦ O, E ↦ I. -/
  outer : α → α
  /-- Dual: A ↦ I, E ↦ O (`= outer ∘ inner`). -/
  dual : α → α

/-- Build a square from a single vertex and the three duality operations. -/
def Square.fromOps {α : Type*} (a : α) (ops : SquareOps α) : Square α where
  A := a
  E := ops.inner a
  I := ops.dual a
  O := ops.outer a

/-! ### Square relations -/

/-- The six relations of the Square over a Boolean algebra. Contradiction
diagonals are the full `IsContradictory`; contrariety/subcontrariety give one
direction (`Disjoint`/`Codisjoint`); subalternations are non-strict (`≤`). The
bridges below recover `IsContrary`/`IsSubaltern` from the missing witness. -/
structure SquareRelations {α : Type*} [BooleanAlgebra α] (sq : Square α) where
  /-- A entails I. -/
  subalternAI : sq.A ≤ sq.I
  /-- E entails O. -/
  subalternEO : sq.E ≤ sq.O
  /-- A and O are contradictories. -/
  contradAO : IsContradictory sq.A sq.O
  /-- E and I are contradictories. -/
  contradEI : IsContradictory sq.E sq.I
  /-- A and E are contraries. -/
  contraryAE : Disjoint sq.A sq.E
  /-- I and O are subcontraries. -/
  subcontrIO : Codisjoint sq.I sq.O

/-! ### Constructing squares from duality operations -/

/-- Build a square from a generalized quantifier and the GQ duality operations. -/
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

/-! ### Bridges to the Aristotelian predicates -/

/-- Lift to `IsSubaltern sq.A sq.I` given strictness `sq.A ≠ sq.I`. -/
theorem SquareRelations.toSubalternAI {α : Type*} [BooleanAlgebra α] {sq : Square α}
    (rel : SquareRelations sq) (hne : sq.A ≠ sq.I) : IsSubaltern sq.A sq.I :=
  lt_of_le_of_ne rel.subalternAI hne

/-- Lift to `IsContrary sq.A sq.E` given non-exhaustion `sq.A ⊔ sq.E ≠ ⊤`. -/
theorem SquareRelations.toContraryAE {α : Type*} [BooleanAlgebra α] {sq : Square α}
    (rel : SquareRelations sq) (hne : sq.A ⊔ sq.E ≠ ⊤) : IsContrary sq.A sq.E :=
  ⟨rel.contraryAE, fun hc => hne (codisjoint_iff.mp hc)⟩

/-- The contradiction diagonal holds definitionally for the negation structure. -/
theorem outerNeg_contradiction {α : Type*} (q : GQ α) (R S : α → Prop) :
    q R S ↔ ¬ (outerNeg q R S) := by
  simp [outerNeg, Classical.not_not]

theorem innerNeg_dual_contradiction {α : Type*} (q : GQ α) (R S : α → Prop) :
    innerNeg q R S ↔ ¬ (dualQ q R S) := by
  simp [dualQ, outerNeg, innerNeg, Classical.not_not]

/-! ### The box-derived square -/

/-- The square of propositions from a box-like operator `box`: `A = box p`,
`E = box pᶜ`, `I = (box pᶜ)ᶜ`, `O = (box p)ᶜ`. -/
def Square.fromBox {α : Type*} [BooleanAlgebra α] (box : α → α) (p : α) :
    Square α where
  A := box p
  E := box pᶜ
  I := (box pᶜ)ᶜ
  O := (box p)ᶜ

theorem fromBox_contradAO {α : Type*} [BooleanAlgebra α] (box : α → α) (p : α) :
    (Square.fromBox box p).A = (Square.fromBox box p).Oᶜ := by
  simp [Square.fromBox]

theorem fromBox_contradEI {α : Type*} [BooleanAlgebra α] (box : α → α) (p : α) :
    (Square.fromBox box p).E = (Square.fromBox box p).Iᶜ := by
  simp [Square.fromBox]

/-! ### Connection to Horn scales -/

/-- Subalternation A→I is the Horn-scale ordering (the `⟨I, A⟩` scale): using the
weak term I scalar-implicates the negation of the strong term A (= O). -/
theorem subalternation_is_scale_ordering {α : Type*} [BooleanAlgebra α] (sq : Square α)
    (rel : SquareRelations sq) : sq.A ≤ sq.I :=
  rel.subalternAI

end Aristotelian
