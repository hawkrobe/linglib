import Linglib.Core.Logic.Aristotelian.Basic

/-!
# Square of Opposition

[barwise-cooper-1981] [horn-2001]. The Aristotelian square reified as an
algebraic object: four corners `A`, `E`, `I`, `O` over a Boolean algebra, related
by contradiction (A–O, E–I), contrariety (A–E), subcontrariety (I–O), and
subalternation (A→I, E→O). Concrete instantiations (quantifiers, modals,
attitudes) live in their respective theory modules.
-/

namespace Aristotelian

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

/-! ### Bridges to the Aristotelian predicates -/

/-- Lift to `IsSubaltern sq.A sq.I` given strictness `sq.A ≠ sq.I`. -/
theorem SquareRelations.toSubalternAI {α : Type*} [BooleanAlgebra α] {sq : Square α}
    (rel : SquareRelations sq) (hne : sq.A ≠ sq.I) : IsSubaltern sq.A sq.I :=
  lt_of_le_of_ne rel.subalternAI hne

/-- Lift to `IsContrary sq.A sq.E` given non-exhaustion `sq.A ⊔ sq.E ≠ ⊤`. -/
theorem SquareRelations.toContraryAE {α : Type*} [BooleanAlgebra α] {sq : Square α}
    (rel : SquareRelations sq) (hne : sq.A ⊔ sq.E ≠ ⊤) : IsContrary sq.A sq.E :=
  ⟨rel.contraryAE, fun hc => hne (codisjoint_iff.mp hc)⟩

end Aristotelian
