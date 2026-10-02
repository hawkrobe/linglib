module

public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# The square of opposition

The square of opposition, in the form Horn surveys, has four corners `A`, `E`, `I`, `O` in a
Boolean algebra, related by contradiction (A–O, E–I), contrariety (A–E), subcontrariety (I–O)
and subalternation (A→I, E→O). Its instances for generalized quantifiers, after Barwise and
Cooper, and for modals live with those theories.

## References

* [barwise-cooper-1981]
* [horn-2001]
-/

@[expose] public section

namespace Aristotelian

/-! ### The square -/

/-- A square of opposition has four corners. -/
structure Square (α : Type*) where
  /-- `A` is the universal affirmative corner (*every*, `□p`, `Bel p`). -/
  A : α
  /-- `E` is the universal negative corner (*no*, `□¬p`, `Bel ¬p`). -/
  E : α
  /-- `I` is the particular affirmative corner (*some*, `◇p`). -/
  I : α
  /-- `O` is the particular negative corner (*not every*, `¬□p`, `¬Bel p`). -/
  O : α

/-! ### Square relations -/

variable {α : Type*} [BooleanAlgebra α] {sq : Square α}

/-- A square over a Boolean algebra satisfies the relations of the square when both diagonals
are contradictory and the universals cannot both hold. Subalternation and subcontrariety follow
(`subalternAI`, `subalternEO`, `subcontrIO`). -/
structure SquareRelations (sq : Square α) : Prop where
  /-- `A` and `O` are contradictories. -/
  contradAO : IsCompl sq.A sq.O
  /-- `E` and `I` are contradictories. -/
  contradEI : IsCompl sq.E sq.I
  /-- `A` and `E` cannot both hold. -/
  contraryAE : Disjoint sq.A sq.E

namespace SquareRelations

/-- `A` entails `I`. -/
theorem subalternAI (h : SquareRelations sq) : sq.A ≤ sq.I := by
  rw [h.contradEI.symm.eq_compl]
  exact le_compl_iff_disjoint_right.mpr h.contraryAE

/-- `E` entails `O`. -/
theorem subalternEO (h : SquareRelations sq) : sq.E ≤ sq.O := by
  rw [h.contradAO.symm.eq_compl]
  exact le_compl_iff_disjoint_right.mpr h.contraryAE.symm

/-- `I` and `O` cannot both fail. -/
theorem subcontrIO (h : SquareRelations sq) : Codisjoint sq.I sq.O := by
  rw [h.contradEI.symm.eq_compl, h.contradAO.symm.eq_compl, codisjoint_iff, ← compl_inf,
    disjoint_iff.mp h.contraryAE.symm, compl_bot]

/-- When the particulars are the complements of the opposite universals (`I = Eᶜ`, `O = Aᶜ`),
the diagonals are contradictory outright, so `Disjoint A E` gives the whole square. Under the
Boolean reading contrariety is where existential import lives. It fails when the universals
hold vacuously (an empty subject term, or modally a dead-end world), and the assumption ruling
that out, a non-empty term or seriality, enters through this hypothesis. -/
theorem of_disjoint (hI : sq.I = sq.Eᶜ) (hO : sq.O = sq.Aᶜ) (h : Disjoint sq.A sq.E) :
    SquareRelations sq :=
  ⟨hO ▸ isCompl_compl, hI ▸ isCompl_compl, h⟩

end SquareRelations

end Aristotelian
