import Linglib.Core.LinearAlgebra.LinearIndependent
import Linglib.Fragments.English.Verbs
import Linglib.Processing.DiscriminativeLexicon.Realization
import Linglib.Processing.DiscriminativeLexicon.Training

/-!
# Heitmeier, Chuang and Baayen (2026): The Discriminative Lexicon

This file formalizes the book's relation between linearity and regularity. Its linear
production maps handle inflectional systems with irregular forms: trained on empirical
embeddings, the English past-tense model produces 94% of the regular and 74% of the irregular
training verbs (§12.9). Meanings can instead be constructed, the meaning of *walked* as the
meaning of *walk* plus a past-tense vector (Table 12.7; conceptualization is vector addition,
(5.3)). Regularizing meanings this way gives "a reasonable approximation of a truly regular
system, and for such a system, linear mappings appear to work quite well" (§16.6, Table 16.2),
but when held-out verbs' meanings are built from the comprehended base form plus a past-tense
vector, "none of the irregular verbs was produced correctly" (§12.9).

The file states why in word-and-paradigm terms. Over imputed semantics, a lexeme vector plus an
inflectional-function vector, the form table of a linear map satisfies proportional analogy by
construction (`Morphology.IsAnalogicallyRegular`). So a table violating analogy is the paradigm
of no linear lexicon and forces positive training loss, and when the lexeme and function
vectors are jointly independent a table is the paradigm of some linear lexicon exactly when it
is analogically regular. Over word-specific embeddings, by contrast, any table is the paradigm
of some linear lexicon as soon as the embeddings are linearly independent, which fills the
irregular-linear cell of Table 16.2. The English past tense at the book's letter-trigram coding
(§12.9) is the irregular table, *walk, walked* against *go, went*, with the forms taken from
the English fragment.

## Main results

* `not_exists_paradigm_eq_of_not_regular`, `pos_weightedLoss_of_not_regular`: an irregular
  table is the paradigm of no linear lexicon over imputed semantics, and training on it leaves
  positive loss.
* `exists_paradigm_imputed_eq_iff`: over jointly independent lexeme and function vectors, a
  table is the paradigm of some linear lexicon iff it is analogically regular.
* `exists_paradigm_eq_of_linearIndependent`: over linearly independent word-specific
  embeddings, every table is the paradigm of some linear lexicon.
* `pastTense_not_regular`: *walk, walked, go, went* violates proportional analogy.

## References

* [heitmeier-chuang-baayen-2026]
-/

namespace HeitmeierChuangBaayen2026

open DiscriminativeLexicon Morphology Matrix

variable {d n : ℕ} {Lexeme Cell : Type*}

/-! ### Imputed semantics -/

variable (σ : Lexeme → MeaningVec d) (ε : Cell → MeaningVec d)

/-- A table violating proportional analogy is the paradigm of no linear lexicon over imputed
semantics, so irregular forms cannot be produced from constructed meanings (§12.9). -/
theorem not_exists_paradigm_eq_of_not_regular {f : Lexeme → Cell → FormVec n}
    (hf : ¬ IsAnalogicallyRegular f) :
    ¬ ∃ D : Linear ℝ (FormVec n) (MeaningVec d), D.paradigm (imputed σ ε) = f := by
  rintro ⟨D, rfl⟩
  exact hf (D.isAnalogicallyRegular_paradigm_imputed σ ε)

/-! ### Interpolation -/

/-- Over word-specific, linearly independent embeddings any form table is the paradigm of some
linear lexicon, irregulars included, which is the irregular-linear cell of Table 16.2 and the
English past tense on empirical embeddings (§12.9). -/
theorem exists_paradigm_eq_of_linearIndependent {s : Lexeme → Cell → MeaningVec d}
    (hs : LinearIndependent ℝ (Function.uncurry s)) (f : Lexeme → Cell → FormVec n) :
    ∃ D : Linear ℝ (FormVec n) (MeaningVec d), D.paradigm s = f :=
  let ⟨G, hG⟩ := hs.exists_linearMap_apply_eq (Function.uncurry f)
  ⟨⟨0, G⟩, funext fun l ↦ funext fun c ↦ hG (l, c)⟩

/-- When the lexeme and inflectional-function vectors are jointly linearly independent, a table
is the paradigm of some linear lexicon over imputed semantics iff it is analogically regular,
so for a regularized system linearity and regularity are the same constraint (§16.6). -/
theorem exists_paradigm_imputed_eq_iff [Nonempty Lexeme] [Nonempty Cell]
    (hind : LinearIndependent ℝ (Sum.elim σ ε)) (f : Lexeme → Cell → FormVec n) :
    (∃ D : Linear ℝ (FormVec n) (MeaningVec d), D.paradigm (imputed σ ε) = f) ↔
      IsAnalogicallyRegular f := by
  refine ⟨fun ⟨D, hD⟩ ↦ hD ▸ D.isAnalogicallyRegular_paradigm_imputed σ ε, fun hreg ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := isAnalogicallyRegular_iff_exists_add.1 hreg
  obtain ⟨G, hG⟩ := hind.exists_linearMap_apply_eq (Sum.elim a b)
  refine ⟨⟨0, G⟩, funext fun l ↦ funext fun c ↦ ?_⟩
  have hσ : G (σ l) = a l := hG (Sum.inl l)
  have hε : G (ε c) = b c := hG (Sum.inr c)
  simp [hσ, hε, hab]

/-! ### Training on a paradigm -/

variable [Fintype Lexeme] [Fintype Cell]

/-- A paradigm is a training experience whose semantic matrix holds the imputed meanings and
whose form matrix holds the form table, one row per lexeme and cell. -/
noncomputable def paradigmExperience (f : Lexeme → Cell → FormVec n) :
    TrainingExperience (Fintype.card (Lexeme × Cell)) n d :=
  let e := (Fintype.equivFin (Lexeme × Cell)).symm
  ⟨of (Function.uncurry (imputed σ ε) ∘ e), of (Function.uncurry f ∘ e)⟩

/-- Irregularity forces positive training loss, since no mapping matrix fits a suppletive
paradigm exactly and so every trained matrix carries residual error. -/
theorem pos_weightedLoss_of_not_regular {f : Lexeme → Cell → FormVec n}
    (hf : ¬ IsAnalogicallyRegular f) {q : FrequencyVector (Fintype.card (Lexeme × Cell))}
    (hq : ∀ i, 0 < q i) (G : Matrix (Fin d) (Fin n) ℝ) :
    0 < weightedLoss (paradigmExperience σ ε f) q G := by
  refine lt_of_le_of_ne (weightedLoss_nonneg _ _ _) (Ne.symm fun h0 ↦ ?_)
  have hint := (weightedLoss_eq_zero_iff _ _ _ hq).1 h0
  refine not_exists_paradigm_eq_of_not_regular σ ε hf
    ⟨⟨0, toLin' Gᵀ⟩, funext fun l ↦ funext fun c ↦ funext fun j ↦ ?_⟩
  have h := congrFun (congrFun hint ((Fintype.equivFin (Lexeme × Cell)) (l, c))) j
  simpa [paradigmExperience, Linear.paradigm, toLin'_apply, mulVec_transpose, mul_apply,
    vecMul, dotProduct] using h

/-! ### The English past tense -/

/-- The two verbs of the book's contrast, regular *walk* and suppletive *go*, are the English
fragment's entries. -/
def verb : Fin 2 → English.Verb := ![English.walk, English.go]

/-- *walk* is the first verb. -/
abbrev walk : Fin 2 := 0

/-- *go* is the second verb. -/
abbrev go : Fin 2 := 1

/-- The base and past cells of the fragment's verb paradigm are the two cells of the table. -/
def cell : Fin 2 → English.Verb.Cell := ![.base, .past]

/-- The base cell is the first cell. -/
abbrev base : Fin 2 := 0

/-- The past cell is the second cell. -/
abbrev past : Fin 2 := 1

/-- The letter-trigram cue inventory of the four forms; §12.9 codes forms as letter trigrams. -/
def trigram : Fin 13 → Augmented Char :=
  ![[none, some 'w', some 'a'], [some 'w', some 'a', some 'l'], [some 'a', some 'l', some 'k'],
    [some 'l', some 'k', none], [some 'l', some 'k', some 'e'], [some 'k', some 'e', some 'd'],
    [some 'e', some 'd', none], [none, some 'g', some 'o'], [some 'g', some 'o', none],
    [none, some 'w', some 'e'], [some 'w', some 'e', some 'n'], [some 'e', some 'n', some 't'],
    [some 'n', some 't', none]]

/-- The past-tense form table at the trigram coding takes each verb's form at each cell from
the fragment. -/
def pastTense (v c : Fin 2) : FormVec 13 :=
  cueVector 3 trigram ((verb v).realize (cell c)).toList

/-- Only *walked* carries the cue `ed#`. -/
private theorem mem_cues_iff (v c : Fin 2) :
    trigram 6 ∈ cues 3 ((verb v).realize (cell c)).toList ↔ v = walk ∧ c = past := by
  revert v c; decide +kernel

/-- The English past tense violates proportional analogy, since *walked* adds the cue `ed#` to
*walk* while *went* adds nothing to *go*. So no linear lexicon produces it from constructed
meanings (`not_exists_paradigm_eq_of_not_regular`), while independent embeddings realise it
(`exists_paradigm_eq_of_linearIndependent`), as in §12.9. -/
theorem pastTense_not_regular : ¬ IsAnalogicallyRegular pastTense := fun h ↦ by
  have := congrFun (isAnalogicallyRegular_iff.1 h walk go past base) 6
  simp [pastTense, cueVector, multiHot, mem_cues_iff] at this

end HeitmeierChuangBaayen2026
