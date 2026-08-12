import Linglib.Core.Order.Aristotelian

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

/-! ### Square relations -/

variable {α : Type*} [BooleanAlgebra α]

/-- The six relations of the Square over a Boolean algebra. Contradiction
diagonals are the full `IsContradictory`; contrariety/subcontrariety give one
direction (`Disjoint`/`Codisjoint`); subalternations are non-strict (`≤`). The
bridges below recover `IsContrary`/`IsSubaltern` from the missing witness. -/
structure SquareRelations (sq : Square α) where
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

/-- The classical square: when the particulars are the complements of the
    opposite universals (`I = Eᶜ`, `O = Aᶜ`), the contradiction diagonals
    hold outright and the remaining relations are each equivalent to
    contrariety, so `Disjoint A E` yields the full square. Under the modern
    Boolean reading, contrariety is where existential import lives: it
    fails when the universals hold vacuously (empty subject term; modally,
    a dead-end world), and the discharging assumption — a non-empty term,
    seriality — enters through this hypothesis. -/
theorem SquareRelations.of_disjoint {sq : Square α}
    (hI : sq.I = sq.Eᶜ) (hO : sq.O = sq.Aᶜ) (h : Disjoint sq.A sq.E) :
    SquareRelations sq := by
  refine ⟨?_, ?_, ?_, ?_, h, ?_⟩
  · rw [hI]; exact le_compl_iff_disjoint_right.mpr h
  · rw [hO]; exact le_compl_iff_disjoint_right.mpr h.symm
  · rw [hO]; exact isCompl_compl
  · rw [hI]; exact isCompl_compl
  · rw [hI, hO, codisjoint_iff, ← compl_inf, disjoint_iff.mp h.symm, compl_bot]

/-! ### Bridges to the Aristotelian predicates -/

/-- Lift to `IsSubaltern sq.A sq.I` given strictness `sq.A ≠ sq.I`. -/
theorem SquareRelations.toSubalternAI {sq : Square α}
    (rel : SquareRelations sq) (hne : sq.A ≠ sq.I) : IsSubaltern sq.A sq.I :=
  lt_of_le_of_ne rel.subalternAI hne

/-- Lift to `IsContrary sq.A sq.E` given non-exhaustion `sq.A ⊔ sq.E ≠ ⊤`. -/
theorem SquareRelations.toContraryAE {sq : Square α}
    (rel : SquareRelations sq) (hne : sq.A ⊔ sq.E ≠ ⊤) : IsContrary sq.A sq.E :=
  ⟨rel.contraryAE, fun hc => hne (codisjoint_iff.mp hc)⟩

end Aristotelian
