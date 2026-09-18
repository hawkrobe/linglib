import Linglib.Morphology.Realization
import Linglib.Morphology.Paradigm.Analogy
import Linglib.Processing.DiscriminativeLexicon.Coding

/-!
# The discriminative lexicon as a realization

This file presents a linear discriminative lexicon as a `Morphology.Realization`, so that it
stands beside Distributed Morphology, Paradigm Function Morphology and nanosyntax on the same
paradigm data.

A linear lexicon realizes a lexeme at a paradigm cell as the form its production map predicts
from the cell's meaning. Which meaning is used is the speaker's choice in Table 12.7 of
Heitmeier, Chuang and Baayen, either an empirical embedding of the word or a meaning
constructed from the lexeme's vector and the inflectional function's vector (`imputed`), the
meaning of *walked* as the meaning of *walk* plus a past-tense vector. Either way the
realization is total and univalent. The model itself posits no stems or exponents; its lexeme
and inflectional function are semantic primitives, and the realization interface is linglib's
comparison device rather than the theory's ontology. Over imputed semantics the form table is
analogically regular by construction (`Morphology.IsAnalogicallyRegular`), which
`Studies/HeitmeierChuangBaayen2026` turns into an equivalence; over word-specific embeddings
it need not be.

## Main definitions

* `Linear.paradigm D s`: the model's form table over a meaning assignment `s`.
* `Linear.realization D s`: the same table as a `Morphology.Realization`.

## Main results

* `Linear.realization_isTotal`, `Linear.realization_isUnivalent`: the realization is total and
  univalent.
* `Linear.isAnalogicallyRegular_paradigm_imputed`: over imputed semantics the table is
  analogically regular.

## References

* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

namespace DiscriminativeLexicon.Linear

open Morphology

variable {n d : ℕ} {L Cell : Type*} (D : Linear ℝ (FormVec n) (MeaningVec d))
  (s : L → Cell → MeaningVec d)

/-- The form table of a linear lexicon over a meaning assignment lists the production map's
prediction at the meaning of each lexeme at each cell. -/
def paradigm (l : L) (c : Cell) : FormVec n := D.production (s l c)

@[simp] theorem paradigm_apply (l : L) (c : Cell) : D.paradigm s l c = D.production (s l c) := rfl

/-- A linear lexicon is a `Morphology.Realization` in which a lexeme at a cell is realised by the
one form the production map predicts. -/
def realization : Realization L Cell (FormVec n) := ⟨fun l c => {D.paradigm s l c}⟩

@[simp] theorem realization_realize (l : L) (c : Cell) :
    (D.realization s).realize l c = {D.paradigm s l c} := rfl

theorem realization_isTotal : (D.realization s).IsTotal := fun _ _ => Finset.singleton_nonempty _

theorem realization_isUnivalent : (D.realization s).IsUnivalent := fun _ _ =>
  (Finset.card_singleton _).le

/-- Over imputed semantics the form table is analogically regular, since the form shift of a
cell is lexeme-independent. -/
theorem isAnalogicallyRegular_paradigm_imputed (σ : L → MeaningVec d) (ε : Cell → MeaningVec d) :
    IsAnalogicallyRegular (D.paradigm (imputed σ ε)) := by
  have : D.paradigm (imputed σ ε) = fun l c => D.production.toAddMonoidHom (σ l + ε c) :=
    funext fun l => funext fun c => by simp
  rw [this]
  exact (isAnalogicallyRegular_add σ ε).map _

end DiscriminativeLexicon.Linear
