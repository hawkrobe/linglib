import Linglib.Morphology.Paradigm.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Abel

/-!
# Proportional analogy

Word-and-paradigm morphology relates the forms of one lexeme to those of another by
**proportional analogy**, *cat : cats :: dog : dogs* ([blevins-2016]): the operation taking the
form at one cell to the form at another is the same for every lexeme. Which operations count is a
parameter, affixation on strings or translation on vectors, so a lexeme-indexed family of
paradigms `p : L → Cell → F` is **analogical** under a class of operations when every pair of
cells is related by one operation of the class shared across lexemes (`IsAnalogical`). Analogy
under any class makes each cell's form identify the lexeme's whole paradigm, Ackerman and
Malouf's vocabular clarity (`ParadigmSystem.isVocabularClear_of_isAnalogical` in
`Complexity.lean`). For forms in an additive group and translations as the operations, the cell
contrast is a difference and the family is **analogically regular** (`IsAnalogicallyRegular`):
every contrast is lexeme-independent, equivalently the family is a lexeme part plus a cell part
(`isAnalogicallyRegular_iff_exists_add`), and the property is preserved by additive maps of the
form space (`IsAnalogicallyRegular.map`). This is the case a discriminative lexicon realises
exactly (`Studies/HeitmeierChuangBaayen2026`).

## Main declarations

* `Morphology.IsAnalogical ops p` — every pair of cells is related by one operation of `ops`,
  the same for every lexeme.
* `Morphology.IsAnalogicallyRegular p` — analogy under the translations of an additive group;
  `isAnalogicallyRegular_iff` is its difference form.
* `Morphology.isAnalogicallyRegular_iff_exists_add` — regular iff a lexeme part plus a cell
  part.

## References

* [J. P. Blevins, *Word and Paradigm Morphology* (2016)][blevins-2016]
-/

namespace Morphology

variable {L Cell F G : Type*}

/-- A lexeme-indexed family of paradigms is **analogical** under a class of operations on forms
when every pair of cells is related by one operation of the class, the same for every lexeme. -/
def IsAnalogical (ops : Set (F → F)) (p : L → Cell → F) : Prop :=
  ∀ c c', ∃ g ∈ ops, ∀ l, p l c' = g (p l c)

section AddCommGroup

variable [AddCommGroup F] [AddCommGroup G]

/-- Analogy under translations: the form contrast between any two cells is the same for every
lexeme. -/
def IsAnalogicallyRegular (p : L → Cell → F) : Prop :=
  IsAnalogical (Set.range fun v : F => (· + v)) p

/-- The difference form of analogical regularity. -/
theorem isAnalogicallyRegular_iff {p : L → Cell → F} :
    IsAnalogicallyRegular p ↔ ∀ l l' c c', p l c - p l c' = p l' c - p l' c' := by
  constructor
  · intro h l l' c c'
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := h c c'
    dsimp only at hv
    rw [hv l, hv l']
    abel
  · intro h c c'
    rcases isEmpty_or_nonempty L with hL | ⟨⟨l₀⟩⟩
    · exact ⟨_, ⟨0, rfl⟩, fun l => (hL.false l).elim⟩
    · refine ⟨_, ⟨p l₀ c' - p l₀ c, rfl⟩, fun l => ?_⟩
      show p l c' = p l c + (p l₀ c' - p l₀ c)
      rw [← h l l₀ c' c]
      abel

/-- A lexeme part plus a cell part is analogically regular. -/
theorem isAnalogicallyRegular_add (a : L → F) (b : Cell → F) :
    IsAnalogicallyRegular fun l c => a l + b c :=
  isAnalogicallyRegular_iff.2 fun _ _ _ _ => by abel

/-- Analogical regularity is preserved by additive maps of the form space. -/
theorem IsAnalogicallyRegular.map {p : L → Cell → F} (h : IsAnalogicallyRegular p) (f : F →+ G) :
    IsAnalogicallyRegular fun l c => f (p l c) :=
  isAnalogicallyRegular_iff.2 fun l l' c c' => by
    rw [← map_sub, ← map_sub, isAnalogicallyRegular_iff.1 h l l' c c']

/-- Analogical regularity is additivity: a regular family is a lexeme part plus a cell part. -/
theorem isAnalogicallyRegular_iff_exists_add [Nonempty L] [Nonempty Cell] {p : L → Cell → F} :
    IsAnalogicallyRegular p ↔ ∃ (a : L → F) (b : Cell → F), ∀ l c, p l c = a l + b c := by
  refine ⟨fun h => ?_, fun ⟨a, b, hab⟩ => ?_⟩
  · obtain ⟨l₀⟩ := ‹Nonempty L›
    obtain ⟨c₀⟩ := ‹Nonempty Cell›
    refine ⟨fun l => p l c₀, fun c => p l₀ c - p l₀ c₀, fun l c => ?_⟩
    dsimp only
    rw [← isAnalogicallyRegular_iff.1 h l l₀ c c₀]
    abel
  · have : p = fun l c => a l + b c := funext fun l => funext fun c => hab l c
    rw [this]
    exact isAnalogicallyRegular_add a b

end AddCommGroup

end Morphology
