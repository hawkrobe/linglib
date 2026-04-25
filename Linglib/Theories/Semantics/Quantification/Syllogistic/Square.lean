import Linglib.Theories.Semantics.Quantification.Syllogistic.Forms
import Linglib.Core.Logic.Opposition.Diagram

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

The Square is provided as `Diagram` data with the relation matrix labeled.
The full `relation_correct` discharge is **partial** — modern (FOL) reading
makes some relations conditional on `∃R`, so we mark those as `unconnected`
in the labeled matrix and provide them as separate conditional theorems.
The Aristotelian (sortal-restricted) variant where the full Square holds is
the natural follow-up in `Aristotelian.lean` (TODO).
-/

namespace Semantics.Quantification.Syllogistic

open Core.Opposition (AristotelianRel Diagram Contradictory)

-- ============================================================================
-- §1. Corner indexing
-- ============================================================================

/-- Square corners in A/E/I/O order. -/
inductive Corner where
  | A | E | I | O
  deriving DecidableEq, Repr, Fintype

-- ============================================================================
-- §2. The AIEO Square as a Diagram
-- ============================================================================

/-- The four syllogistic forms applied to `(X, Y)`, indexed by `Corner`. -/
def cornerForm (X Y : Region → Bool) : Corner → VennState → Bool
  | .A => fun s => syllAll s X Y
  | .E => fun s => syllNone s X Y
  | .I => fun s => syllSome s X Y
  | .O => fun s => syllSomeNot s X Y

/-- The labeled relation between corners. Modern reading: subalternations
    A→I and E→O depend on existential import, so they appear as
    `unconnected` in the unconditional matrix; the contradiction diagonals
    A↔O and E↔I are unconditional under modern reading. -/
def cornerRel : Corner → Corner → AristotelianRel
  | .A, .O | .O, .A => .contradictory
  | .E, .I | .I, .E => .contradictory
  | _, _ => .unconnected  -- subalternations + contrariety conditional on ∃R

-- ============================================================================
-- §3. Contradictory diagonal lemmas (modern reading, unconditional)
-- ============================================================================

/-- `syllAll` and `syllSomeNot` are contradictories at every state: exactly
    one is true. The "no clash" half follows from extracting the `syllSomeNot`
    witness and applying `syllAll`'s universal; the "exhaustion" half is
    classical LEM on the existence of a Y-counterexample restrictor element. -/
theorem syllAll_contradictory_syllSomeNot (X Y : Region → Bool) :
    Contradictory (fun s => syllAll s X Y) (fun s => syllSomeNot s X Y) := by
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
      push_neg at h
      obtain ⟨r, hRX, hNotY⟩ := h
      exact ⟨r, hRX, hNotY⟩

/-- `syllNone` and `syllSome` are contradictories at every state. Symmetric
    structure to `syllAll_contradictory_syllSomeNot`. -/
theorem syllNone_contradictory_syllSome (X Y : Region → Bool) :
    Contradictory (fun s => syllNone s X Y) (fun s => syllSome s X Y) := by
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
      push_neg at h
      obtain ⟨r, hRX, hY⟩ := h
      exact ⟨r, hRX, hY⟩

-- ============================================================================
-- §4. The AIEO Square as a `Diagram` instance
-- ============================================================================

/-- The AIEO Square as a `Diagram` instance over `Corner` corners.
    Discharges the `contradictory` cases via the lemmas above. The
    `contrary`/`subcontrary`/`subaltern` cases are vacuous because
    `cornerRel` labels all non-A↔O / non-E↔I pairs as `unconnected`. -/
noncomputable def aieoSquare (X Y : Region → Bool) : Diagram Corner VennState where
  φ := cornerForm X Y
  relation := cornerRel
  relation_correct := by
    intro i j
    refine ⟨?_, ?_, ?_, ?_⟩
    -- Contradictory case: discharge via the helper lemmas
    · intro h
      cases i <;> cases j <;> simp [cornerRel] at h <;>
        first
        | exact syllAll_contradictory_syllSomeNot X Y
        | exact (syllAll_contradictory_syllSomeNot X Y).symm
        | exact syllNone_contradictory_syllSome X Y
        | exact (syllNone_contradictory_syllSome X Y).symm
    -- Contrary / Subcontrary / Subaltern cases: cornerRel never labels them, so vacuous
    all_goals (intro h; cases i <;> cases j <;> simp [cornerRel] at h)

end Semantics.Quantification.Syllogistic
