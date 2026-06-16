import Linglib.Semantics.Quantification.Syllogistic.Forms
import Linglib.Core.Logic.Aristotelian.Diagram

/-!
# AIEO Square as a Diagram instance

The four syllogistic forms `(syllAll, syllSome, syllSomeNot, syllNone)`
applied to a fixed `(X, Y)` term-predicate pair form a 4-corner Aristotelian
diagram (Square) over the model class `W = VennState`.

This file constructs the `Diagram (Fin 4)` instance and provides the
individual conditional Aristotelian relations. Some relations require the
restrictor `(s ∧ X)` to be non-empty (Aristotelian sortal restriction); these
are stated with explicit hypothesis or restricted to the non-degenerate
substate.

## Mapping

Following Demey & Smessaert (and the medieval ordering):

| Position | Aristotelian | Form          | Lean         |
|----------|--------------|---------------|--------------|
| 0        | A            | universal +   | `syllAll`    |
| 1        | E            | universal −   | `syllNone`   |
| 2        | I            | particular +  | `syllSome`   |
| 3        | O            | particular −  | `syllSomeNot`|

## Status

The Square is provided as a `Diagram` (the fragment `cornerForm`); its relations
are derived. The contradiction diagonals (A↔O, E↔I) hold unconditionally under the
modern (FOL) reading and are recorded as theorems (`aieoSquare_AO_contradictory`,
`aieoSquare_EI_contradictory`). The subalternations A→I, E→O are conditional on
existential import (`∃R`); the sortal-restricted Aristotelian variant where the full
Square holds is the natural follow-up (TODO).
-/

namespace Quantification.Syllogistic

open Aristotelian (Diagram IsContradictory isContradictory_iff_forall)

/-! ### Corner indexing -/

/-- Square corners in A/E/I/O order. -/
inductive Corner where
  | A | E | I | O
  deriving DecidableEq, Repr, Fintype

/-! ### The AIEO Square as a Diagram -/

/-- The four syllogistic forms applied to `(X, Y)`, indexed by `Corner`. -/
def cornerForm (X Y : Region → Bool) : Corner → VennState → Bool
  | .A => fun s => syllAll s X Y
  | .E => fun s => syllNone s X Y
  | .I => fun s => syllSome s X Y
  | .O => fun s => syllSomeNot s X Y

/-! ### Contradictory diagonal lemmas (modern reading, unconditional) -/

/-- `syllAll` and `syllSomeNot` are contradictories at every state: exactly
    one is true. The "no clash" half follows from extracting the `syllSomeNot`
    witness and applying `syllAll`'s universal; the "exhaustion" half is
    classical LEM on the existence of a Y-counterexample restrictor element. -/
theorem syllAll_contradictory_syllSomeNot (X Y : Region → Bool) :
    IsContradictory (fun s => syllAll s X Y) (fun s => syllSomeNot s X Y) := by
  rw [isContradictory_iff_forall]
  refine ⟨?_, ?_⟩
  · intro s ⟨hAll, hSomeNot⟩
    rw [syllAll_eq_true_iff] at hAll
    unfold syllSomeNot at hSomeNot
    rw [decide_eq_true_eq] at hSomeNot
    obtain ⟨r, hRX, hNotY⟩ := hSomeNot
    exact hNotY (hAll r hRX)
  · intro s
    by_cases h : ∀ r : Region, (s r = true ∧ X r = true) → Y r = true
    · left; unfold syllAll; exact decide_eq_true h
    · right
      unfold syllSomeNot
      apply decide_eq_true
      push Not at h
      obtain ⟨r, hRX, hNotY⟩ := h
      exact ⟨r, hRX, hNotY⟩

/-- `syllNone` and `syllSome` are contradictories at every state. Symmetric
    structure to `syllAll_contradictory_syllSomeNot`. -/
theorem syllNone_contradictory_syllSome (X Y : Region → Bool) :
    IsContradictory (fun s => syllNone s X Y) (fun s => syllSome s X Y) := by
  rw [isContradictory_iff_forall]
  refine ⟨?_, ?_⟩
  · intro s ⟨hNone, hSome⟩
    rw [syllNone_eq_true_iff] at hNone
    unfold syllSome at hSome
    rw [decide_eq_true_eq] at hSome
    obtain ⟨r, hRX, hY⟩ := hSome
    exact hNone r hRX hY
  · intro s
    by_cases h : ∀ r : Region, (s r = true ∧ X r = true) → ¬(Y r = true)
    · left; unfold syllNone; exact decide_eq_true h
    · right
      unfold syllSome
      apply decide_eq_true
      push Not at h
      obtain ⟨r, hRX, hY⟩ := h
      exact ⟨r, hRX, hY⟩

/-! ### The AIEO Square as a `Diagram` instance -/

/-- The AIEO Square as a `Diagram` over `Corner` corners — the fragment `cornerForm`. -/
noncomputable def aieoSquare (X Y : Region → Bool) : Diagram Corner (VennState → Bool) :=
  ⟨cornerForm X Y⟩

/-- A and O are contradictories in the AIEO Square (unconditional, modern reading). -/
theorem aieoSquare_AO_contradictory (X Y : Region → Bool) :
    IsContradictory ((aieoSquare X Y).φ .A) ((aieoSquare X Y).φ .O) :=
  syllAll_contradictory_syllSomeNot X Y

/-- E and I are contradictories in the AIEO Square (unconditional, modern reading). -/
theorem aieoSquare_EI_contradictory (X Y : Region → Bool) :
    IsContradictory ((aieoSquare X Y).φ .E) ((aieoSquare X Y).φ .I) :=
  syllNone_contradictory_syllSome X Y

end Quantification.Syllogistic
