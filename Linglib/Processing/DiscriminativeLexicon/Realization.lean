import Linglib.Morphology.Realization
import Linglib.Morphology.Paradigm.Analogy
import Linglib.Processing.DiscriminativeLexicon.Coding

/-!
# The discriminative lexicon as a realization

A linear DLM with imputed lexeme and cell vectors realises a lexeme at a paradigm cell as the
form its production map predicts from the conceptualized meaning: the constructed meaning-to-form
route of [heitmeier-chuang-baayen-2026] (Table 12.7), where the meaning of *walked* is the meaning
of *walk* plus a past-tense vector and `G` maps it to the form. On the shared
`Morphology.Realization` interface this is a total, univalent realization, which puts the model
beside Distributed Morphology, Paradigm Function Morphology and nanosyntax on the same paradigm
data. The model itself posits no stems or exponents (Box 1.3), so the interface is linglib's
comparison device, not the theory's ontology. Its form table is analogically regular by
construction (`Morphology.IsAnalogicallyRegular`), which `Studies/HeitmeierChuangBaayen2026`
turns into an iff.

## Main declarations

* `DiscriminativeLexicon.Linear.paradigm D σ ε` — the model's form table over imputed vectors.
* `DiscriminativeLexicon.Linear.realization D σ ε` — the same as a `Morphology.Realization`,
  total and univalent.
* `DiscriminativeLexicon.Linear.isAnalogicallyRegular_paradigm` — the table is analogically
  regular.

## References

* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

namespace DiscriminativeLexicon.Linear

open Morphology

variable {n d : ℕ} {L Cell : Type*} (D : Linear ℝ (FormVec n) (MeaningVec d))
  (σ : L → MeaningVec d) (ε : Cell → MeaningVec d)

/-- The form table of a linear DLM over imputed lexeme and cell vectors: the production map at the
conceptualized meaning of each cell. -/
def paradigm (l : L) (c : Cell) : FormVec n :=
  D.production (conceptualize (Sum.elim σ ε) {Sum.inl l, Sum.inr c})

@[simp] theorem paradigm_apply (l : L) (c : Cell) :
    D.paradigm σ ε l c = D.production (σ l + ε c) := by
  simp [paradigm]

/-- A linear DLM as a `Morphology.Realization`: a lexeme at a cell is realised by the one form the
production map predicts. -/
def realization : Realization L Cell (FormVec n) := ⟨fun l c => {D.paradigm σ ε l c}⟩

@[simp] theorem realization_realize (l : L) (c : Cell) :
    (D.realization σ ε).realize l c = {D.paradigm σ ε l c} := rfl

theorem realization_isTotal : (D.realization σ ε).IsTotal := fun _ _ => Finset.singleton_nonempty _

theorem realization_isUnivalent : (D.realization σ ε).IsUnivalent := fun _ _ =>
  (Finset.card_singleton _).le

/-- The form table of a linear DLM over additive semantics is analogically regular: the form shift
of a cell is lexeme-independent. -/
theorem isAnalogicallyRegular_paradigm : IsAnalogicallyRegular (D.paradigm σ ε) := by
  have : D.paradigm σ ε = fun l c => D.production.toAddMonoidHom (σ l + ε c) :=
    funext fun l => funext fun c => by simp
  rw [this]
  exact (isAnalogicallyRegular_add σ ε).map _

end DiscriminativeLexicon.Linear
