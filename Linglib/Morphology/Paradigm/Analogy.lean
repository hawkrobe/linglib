import Linglib.Morphology.Paradigm.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Abel

/-!
# Proportional analogy

Word-and-paradigm morphology relates the forms of one lexeme to those of another by
**proportional analogy**, *cat : cats :: dog : dogs* ([blevins-2016]): the contrast between two
cells is the same for both lexemes. For forms in an additive group the contrast is a difference,
so a lexeme-indexed family of paradigms `p : L → Cell → F` is analogically regular when every
cell contrast is lexeme-independent; equivalently it decomposes as a lexeme part plus a cell part
(`isAnalogicallyRegular_iff_exists_add`), and the property is preserved by additive maps of the
form space (`IsAnalogicallyRegular.map`). Which families are regular is what a theory of
realization predicts: over imputed additive semantics a discriminative lexicon realises exactly
the regular ones (`Studies/HeitmeierChuangBaayen2026`).

## Main declarations

* `Morphology.IsAnalogicallyRegular` — every cell contrast of the family is lexeme-independent.
* `Morphology.isAnalogicallyRegular_iff_exists_add` — regular iff a lexeme part plus a cell
  part.

## References

* [J. P. Blevins, *Word and Paradigm Morphology* (2016)][blevins-2016]
-/

namespace Morphology

variable {L Cell F G : Type*} [AddCommGroup F] [AddCommGroup G]

/-- A lexeme-indexed family of paradigms is **analogically regular** when the form contrast
between any two cells is the same for every lexeme. -/
def IsAnalogicallyRegular (p : L → Cell → F) : Prop :=
  ∀ l l' c c', p l c - p l c' = p l' c - p l' c'

/-- A lexeme part plus a cell part is analogically regular. -/
theorem isAnalogicallyRegular_add (a : L → F) (b : Cell → F) :
    IsAnalogicallyRegular fun l c => a l + b c := fun _ _ _ _ => by dsimp only; abel

/-- Analogy is preserved by additive maps of the form space. -/
theorem IsAnalogicallyRegular.map {p : L → Cell → F} (h : IsAnalogicallyRegular p) (f : F →+ G) :
    IsAnalogicallyRegular fun l c => f (p l c) := fun l l' c c' => by
  rw [← map_sub, ← map_sub, h l l' c c']

/-- Analogy is additivity: a regular family is a lexeme part plus a cell part. -/
theorem isAnalogicallyRegular_iff_exists_add [Nonempty L] [Nonempty Cell] {p : L → Cell → F} :
    IsAnalogicallyRegular p ↔ ∃ (a : L → F) (b : Cell → F), ∀ l c, p l c = a l + b c := by
  refine ⟨fun h => ?_, fun ⟨a, b, hab⟩ => ?_⟩
  · obtain ⟨l₀⟩ := ‹Nonempty L›
    obtain ⟨c₀⟩ := ‹Nonempty Cell›
    refine ⟨fun l => p l c₀, fun c => p l₀ c - p l₀ c₀, fun l c => ?_⟩
    dsimp only
    rw [← h l l₀ c c₀]
    abel
  · have : p = fun l c => a l + b c := funext fun l => funext fun c => hab l c
    rw [this]
    exact isAnalogicallyRegular_add a b

end Morphology
