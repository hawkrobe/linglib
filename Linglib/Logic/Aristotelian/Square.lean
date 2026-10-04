module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Tactic.DeriveFintype

/-!
# The square of opposition

The square of opposition, in the form Horn surveys, has four corners `A`, `E`, `I`, `O` in a
Boolean algebra, related by contradiction (A–O, E–I), contrariety (A–E), subcontrariety (I–O)
and subalternation (A→I, E→O). Its instances for generalized quantifiers, after Barwise and
Cooper, and for modals live with those theories.

A square with these relations divides its algebra into three pairwise contrary cells: `A`, `E`,
and between them the conjunction `I ⊓ O` of the two particulars. Horn traces this trichotomy to
De Morgan and to Jespersen's tripartition into *all*, *some* and *none*, whose middle term is
neither the I nor the O corner but their conjunction; modally the cells are the necessary, the
contingent and the impossible.

## Main definitions

* `Square`, `SquareRelations`: a square and the relations of the square.
* `Square.Cell`, `Square.cell`: the three cells of a square and the element at each.
* `Square.Cell.square`: the square on the cells, each corner the set of cells below it.

## Main results

* `SquareRelations.subalternAI`, `SquareRelations.subalternEO`, `SquareRelations.subcontrIO`:
  the remaining relations of the square.
* `SquareRelations.pairwise_disjoint_cell`, `SquareRelations.sup_cell`: the cells of a square
  are pairwise disjoint and join to `⊤`.
* `Square.Cell.squareRelations_square`, `Square.Cell.cell_square`: the square on the cells
  satisfies the relations, and its cells are the singletons.

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

namespace Square

/-- A cell of a square is the universal affirmative `A`, the conjunction `IO` of the two
particulars, or the universal negative `E`. -/
inductive Cell where
  | A
  | IO
  | E
  deriving DecidableEq, Repr, Fintype

variable {α : Type*} [BooleanAlgebra α]

/-- The element of a square at a cell. -/
def cell (sq : Square α) : Cell → α
  | .A => sq.A
  | .IO => sq.I ⊓ sq.O
  | .E => sq.E

/-- The square on the cells has as each corner the set of cells below it. -/
def Cell.square : Square (Finset Cell) := ⟨{.A}, {.E}, {.A, .IO}, {.IO, .E}⟩

/-- The cells of the square on the cells are the singletons. -/
theorem Cell.cell_square (c : Cell) : Cell.square.cell c = {c} := by
  cases c <;> decide

end Square

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

/-! ### The cells -/

/-- The middle cell is the complement of the join of the contraries. -/
theorem inf_IO_eq (h : SquareRelations sq) : sq.I ⊓ sq.O = (sq.A ⊔ sq.E)ᶜ := by
  rw [h.contradEI.symm.eq_compl, h.contradAO.symm.eq_compl, compl_sup, inf_comm]

open Function in
/-- The cells of a square are pairwise disjoint. -/
theorem pairwise_disjoint_cell (h : SquareRelations sq) : Pairwise (Disjoint on sq.cell) := by
  have hA : Disjoint sq.A (sq.I ⊓ sq.O) := by
    rw [h.inf_IO_eq]; exact disjoint_compl_right.mono_right (compl_le_compl le_sup_left)
  have hE : Disjoint sq.E (sq.I ⊓ sq.O) := by
    rw [h.inf_IO_eq]; exact disjoint_compl_right.mono_right (compl_le_compl le_sup_right)
  rintro (_ | _ | _) (_ | _ | _) hne <;> first
    | exact absurd rfl hne
    | simp only [onFun, Square.cell]
  exacts [hA, h.contraryAE, hA.symm, hE.symm, h.contraryAE.symm, hE]

/-- The cells of a square join to `⊤`. -/
theorem sup_cell (h : SquareRelations sq) : sq.cell .A ⊔ sq.cell .IO ⊔ sq.cell .E = ⊤ := by
  simp only [Square.cell]
  rw [h.inf_IO_eq, sup_right_comm, sup_compl_eq_top]

end SquareRelations

/-- The square on the cells satisfies the relations of the square. -/
theorem Square.Cell.squareRelations_square : SquareRelations Square.Cell.square :=
  .of_disjoint (by decide) (by decide) (by decide)

end Aristotelian
