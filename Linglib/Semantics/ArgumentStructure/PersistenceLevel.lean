import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Persistence levels ([grimm-2011] §2.2, Fig. 2)

Dowty's five Proto-Patient entailments are replaced by four persistence
dimensions — existential and qualitative persistence at the beginning and
end of the event. Logical dependencies (an entity that exists does so with
its qualities; nonexistence at a boundary erases them) leave exactly five
valid combinations, ordered by feature inclusion: a lattice with a creation
branch (`exPersEnd`) and an affectedness branch
(`exPersBeginning ≤ quPersBeginning`) rejoining at `totalPersistence`.
-/

namespace ArgumentStructure

/-- The five valid persistence levels (p.524–525, Fig. 2).

    Each level is a valid combination of four persistence dimensions:
    - ExPB: existential persistence (beginning) — entity exists before event
    - ExPE: existential persistence (end) — entity exists after event
    - QuPB: qualitative persistence (beginning) — qualities unchanged before
    - QuPE: qualitative persistence (end) — qualities unchanged after

    Constraints (ExPB→QuPB, QuPE→ExPE, etc.) reduce the 16 possible
    combinations to exactly 5. -/
inductive PersistenceLevel where
  /-- ∅ExPB, ∅ExPE, ∅QuPB, ∅QuPE — entity has no entailed existence.
      Arguments of *seek*, *want*; negated copulas. -/
  | totalNonPersistence
  /-- ∅ExPB, +ExPE, ∅QuPB, +QuPE — entity comes into existence.
      Objects of *build*, *invent*; subjects of *appear*. -/
  | exPersEnd
  /-- +ExPB, ∅ExPE, +QuPB, ∅QuPE — entity exists before, ceases to exist.
      Subjects of *die*, *evaporate*; objects of *destroy*, *ruin*. -/
  | exPersBeginning
  /-- +ExPB, +ExPE, +QuPB, ∅QuPE — entity persists but is qualitatively
      changed. Objects of transitive *move*, *dim*, *frighten*;
      intransitive subjects of *fall*. -/
  | quPersBeginning
  /-- +ExPB, +ExPE, +QuPB, +QuPE — entity persists unchanged throughout.
      Prototypical transitive subjects; unaffected objects of *see*, *cut at*. -/
  | totalPersistence
  deriving DecidableEq, Repr, Fintype

/-- Existential persistence at beginning (positive feature).
    Also serves as "entity exists at the beginning of the event." -/
def PersistenceLevel.exPersB : PersistenceLevel → Bool
  | .exPersBeginning | .quPersBeginning | .totalPersistence => true
  | _ => false

/-- Existential persistence at end (positive feature). -/
def PersistenceLevel.exPersE : PersistenceLevel → Bool
  | .exPersEnd | .quPersBeginning | .totalPersistence => true
  | _ => false

/-- Qualitative persistence at beginning (positive feature). -/
def PersistenceLevel.quPersB : PersistenceLevel → Bool
  | .exPersBeginning | .quPersBeginning | .totalPersistence => true
  | _ => false

/-- Qualitative persistence at end (positive feature). -/
def PersistenceLevel.quPersE : PersistenceLevel → Bool
  | .exPersEnd | .totalPersistence => true
  | _ => false

/-- Subset inclusion ordering on persistence features. -/
private def PersistenceLevel.leBool (a b : PersistenceLevel) : Bool :=
  (!a.exPersB || b.exPersB) && (!a.exPersE || b.exPersE) &&
  (!a.quPersB || b.quPersB) && (!a.quPersE || b.quPersE)

instance : PartialOrder PersistenceLevel where
  le a b := a.leBool b = true
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := PersistenceLevel) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (a.leBool b = true))

instance : OrderBot PersistenceLevel where
  bot := .totalNonPersistence
  bot_le := by decide

instance : OrderTop PersistenceLevel where
  top := .totalPersistence
  le_top := by decide

/-- Join on persistence levels. The 5 valid levels do not form a sublattice
    of the powerset on {ExPB, ExPE, QuPB, QuPE} — the join is the smallest
    valid level containing the union of features. -/
def PersistenceLevel.sup' (a b : PersistenceLevel) : PersistenceLevel :=
  match a, b with
  | .totalNonPersistence, x | x, .totalNonPersistence => x
  | .totalPersistence, _ | _, .totalPersistence => .totalPersistence
  | .exPersBeginning, .exPersBeginning => .exPersBeginning
  | .exPersEnd, .exPersEnd => .exPersEnd
  | .quPersBeginning, .quPersBeginning => .quPersBeginning
  | .exPersBeginning, .quPersBeginning
  | .quPersBeginning, .exPersBeginning => .quPersBeginning
  | .exPersBeginning, .exPersEnd
  | .exPersEnd, .exPersBeginning => .totalPersistence
  | .exPersEnd, .quPersBeginning
  | .quPersBeginning, .exPersEnd => .totalPersistence

/-- Meet on persistence levels. The largest valid level contained in the
    intersection of features. -/
def PersistenceLevel.inf' (a b : PersistenceLevel) : PersistenceLevel :=
  match a, b with
  | .totalPersistence, x | x, .totalPersistence => x
  | .totalNonPersistence, _ | _, .totalNonPersistence => .totalNonPersistence
  | .exPersBeginning, .exPersBeginning => .exPersBeginning
  | .exPersEnd, .exPersEnd => .exPersEnd
  | .quPersBeginning, .quPersBeginning => .quPersBeginning
  | .exPersBeginning, .quPersBeginning
  | .quPersBeginning, .exPersBeginning => .exPersBeginning
  | .exPersBeginning, .exPersEnd
  | .exPersEnd, .exPersBeginning => .totalNonPersistence
  | .exPersEnd, .quPersBeginning
  | .quPersBeginning, .exPersEnd => .totalNonPersistence

instance : Lattice PersistenceLevel where
  sup := PersistenceLevel.sup'
  inf := PersistenceLevel.inf'
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

end ArgumentStructure
