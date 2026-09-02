import Linglib.Morphology.Realization
import Linglib.Morphology.Paradigm.Analogy
import Linglib.Processing.DiscriminativeLexicon.Coding

/-!
# The discriminative lexicon as a realization

A linear DLM realises a lexeme at a paradigm cell as the form its production map predicts from
the cell's meaning. Which meaning is the speaker's choice ([heitmeier-chuang-baayen-2026]
Table 12.7): an empirical embedding of the word, or a meaning constructed from the lexeme's vector
and the inflectional function's vector (`imputed`), the meaning of *walked* as the meaning of
*walk* plus a past-tense vector. Either way, on the shared `Morphology.Realization` interface this
is a total, univalent realization, which puts the model beside Distributed Morphology, Paradigm
Function Morphology and nanosyntax on the same paradigm data. The model itself posits no stems or
exponents (Box 1.3); its lexeme and inflectional function are semantic primitives (ch. 5), and the
interface is linglib's comparison device, not the theory's ontology. Over imputed semantics the
form table is analogically regular by construction (`Morphology.IsAnalogicallyRegular`), which
`Studies/HeitmeierChuangBaayen2026` turns into an iff; over word-specific embeddings it need not
be.

## Main declarations

* `DiscriminativeLexicon.Linear.paradigm D s` — the model's form table over a meaning
  assignment `s` to lexemes at cells.
* `DiscriminativeLexicon.Linear.realization D s` — the same as a `Morphology.Realization`,
  total and univalent.
* `DiscriminativeLexicon.Linear.isAnalogicallyRegular_paradigm_imputed` — over imputed
  semantics the table is analogically regular.

## References

* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

namespace DiscriminativeLexicon.Linear

open Morphology

variable {n d : ℕ} {L Cell : Type*} (D : Linear ℝ (FormVec n) (MeaningVec d))
  (s : L → Cell → MeaningVec d)

/-- The form table of a linear DLM over a meaning assignment: the production map at the meaning
of each lexeme at each cell. -/
def paradigm (l : L) (c : Cell) : FormVec n := D.production (s l c)

@[simp] theorem paradigm_apply (l : L) (c : Cell) : D.paradigm s l c = D.production (s l c) := rfl

/-- A linear DLM as a `Morphology.Realization`: a lexeme at a cell is realised by the one form the
production map predicts. -/
def realization : Realization L Cell (FormVec n) := ⟨fun l c => {D.paradigm s l c}⟩

@[simp] theorem realization_realize (l : L) (c : Cell) :
    (D.realization s).realize l c = {D.paradigm s l c} := rfl

theorem realization_isTotal : (D.realization s).IsTotal := fun _ _ => Finset.singleton_nonempty _

theorem realization_isUnivalent : (D.realization s).IsUnivalent := fun _ _ =>
  (Finset.card_singleton _).le

/-- Over imputed semantics the form table is analogically regular: the form shift of a cell is
lexeme-independent. -/
theorem isAnalogicallyRegular_paradigm_imputed (σ : L → MeaningVec d) (ε : Cell → MeaningVec d) :
    IsAnalogicallyRegular (D.paradigm (imputed σ ε)) := by
  have : D.paradigm (imputed σ ε) = fun l c => D.production.toAddMonoidHom (σ l + ε c) :=
    funext fun l => funext fun c => by simp
  rw [this]
  exact (isAnalogicallyRegular_add σ ε).map _

end DiscriminativeLexicon.Linear
