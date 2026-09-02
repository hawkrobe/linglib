import Linglib.Processing.DiscriminativeLexicon.Realization
import Linglib.Processing.DiscriminativeLexicon.Training
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Heitmeier, Chuang and Baayen 2026: linearity and regularity

The book's linear production maps handle inflectional systems with irregular forms: trained on
empirical embeddings, its English past-tense model produces 94% of the regular and 74% of the
irregular training verbs (§12.9). Meanings can instead be *constructed*, the meaning of *walked*
as the meaning of *walk* plus a past-tense vector (Table 12.7; conceptualization is vector
addition, eq. 5.3, §16.3), which regularizes a system into "a reasonable approximation of a truly
regular system, and for such a system, linear mappings appear to work quite well" (§16.6,
Table 16.2); but with the meanings of held-out verbs reconstructed this way, "none of the
irregular verbs was produced correctly" (§12.9). This file states why, in word-and-paradigm
terms (`Morphology.IsAnalogicallyRegular`), on the `Morphology.Realization` interface
(`DiscriminativeLexicon.Linear.paradigm`). Over imputed semantics, a lexeme vector plus an
inflectional-function vector (`imputed`; §16.6 says "imputed embeddings for stems and exponents"),
a linear map's form table satisfies proportional analogy by construction, so a table violating
analogy is the paradigm of no linear DLM and forces positive training loss, and when the lexeme
and function vectors are jointly independent a table is the paradigm of some linear DLM iff it is
analogically regular. Over word-specific embeddings, by contrast, any table is the paradigm of
some linear DLM as soon as the embeddings are linearly independent, which fills the
irregular-linear cell of Table 16.2. The English past tense at the book's letter-trigram coding
(§12.9, `cueVector`) is the irregular table: *walk, walked* against *go, went*.

## Main results

* `not_exists_paradigm_eq_of_not_regular`, `pos_weightedLoss_of_not_regular`: an irregular
  table is the paradigm of no linear DLM over imputed semantics and forces positive loss.
* `exists_paradigm_imputed_eq_iff`: over jointly independent lexeme and function vectors, a
  table is the paradigm of some linear DLM iff it is analogically regular.
* `exists_paradigm_eq_of_linearIndependent`: over independent word-specific embeddings every
  table is the paradigm of some linear DLM.
* `pastTense_not_regular`: *walk, walked, go, went* violates analogy.

## References

* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

namespace HeitmeierChuangBaayen2026

open DiscriminativeLexicon Morphology

variable {d n : ℕ} {Lexeme Cell : Type*}

/-! ### Imputed semantics -/

variable (σ : Lexeme → MeaningVec d) (ε : Cell → MeaningVec d)

/-- A table violating proportional analogy is the paradigm of no linear DLM over imputed
semantics: irregular forms cannot be produced from constructed meanings (§12.9). -/
theorem not_exists_paradigm_eq_of_not_regular {f : Lexeme → Cell → FormVec n}
    (hf : ¬ IsAnalogicallyRegular f) :
    ¬ ∃ D : Linear ℝ (FormVec n) (MeaningVec d), D.paradigm (imputed σ ε) = f := by
  rintro ⟨D, rfl⟩
  exact hf (D.isAnalogicallyRegular_paradigm_imputed σ ε)

/-! ### Interpolation -/

/-- A linearly independent family of meanings can be sent anywhere by a linear map. -/
theorem exists_linear_of_linearIndependent {ι : Type*} {v : ι → MeaningVec d}
    (hv : LinearIndependent ℝ v) (w : ι → FormVec n) :
    ∃ G : MeaningVec d →ₗ[ℝ] FormVec n, ∀ i, G (v i) = w i := by
  obtain ⟨G, hG⟩ := LinearMap.exists_extend ((Module.Basis.span hv).constr ℝ w)
  refine ⟨G, fun i => ?_⟩
  have h := LinearMap.congr_fun hG (Module.Basis.span hv i)
  rwa [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.constr_basis,
    Module.Basis.span_apply] at h

/-- Over word-specific, linearly independent embeddings any form table is the paradigm of some
linear DLM, irregulars included: the irregular-linear cell of Table 16.2, the English past tense
on empirical embeddings (§12.9). -/
theorem exists_paradigm_eq_of_linearIndependent {s : Lexeme → Cell → MeaningVec d}
    (hs : LinearIndependent ℝ (Function.uncurry s)) (f : Lexeme → Cell → FormVec n) :
    ∃ D : Linear ℝ (FormVec n) (MeaningVec d), D.paradigm s = f :=
  let ⟨G, hG⟩ := exists_linear_of_linearIndependent hs (Function.uncurry f)
  ⟨⟨0, G⟩, funext fun l => funext fun c => hG (l, c)⟩

/-- When the lexeme and inflectional-function vectors are jointly linearly independent, a table
is the paradigm of some linear DLM over imputed semantics **iff** it is analogically regular: for
a regularized system, linearity and regularity are the same constraint (§16.6). -/
theorem exists_paradigm_imputed_eq_iff [Nonempty Lexeme] [Nonempty Cell]
    (hind : LinearIndependent ℝ (Sum.elim σ ε)) (f : Lexeme → Cell → FormVec n) :
    (∃ D : Linear ℝ (FormVec n) (MeaningVec d), D.paradigm (imputed σ ε) = f) ↔
      IsAnalogicallyRegular f := by
  refine ⟨fun ⟨D, hD⟩ => hD ▸ D.isAnalogicallyRegular_paradigm_imputed σ ε, fun hreg => ?_⟩
  obtain ⟨a, b, hab⟩ := isAnalogicallyRegular_iff_exists_add.1 hreg
  obtain ⟨G, hG⟩ := exists_linear_of_linearIndependent hind (Sum.elim a b)
  refine ⟨⟨0, G⟩, funext fun l => funext fun c => ?_⟩
  have hσ : G (σ l) = a l := hG (Sum.inl l)
  have hε : G (ε c) = b c := hG (Sum.inr c)
  simp [hσ, hε, hab]

/-! ### The English past tense -/

/-- The letters of *walk, walked, go, went*. -/
inductive Letter
  | w | a | l | k | e | d | g | o | n | t
  deriving DecidableEq

/-- A regular and a suppletive verb. -/
inductive Verb
  | walk | go

/-- The base and past cells. -/
inductive Tense
  | base | past

/-- The orthographic forms. -/
def form : Verb → Tense → List Letter
  | .walk, .base => [.w, .a, .l, .k]
  | .walk, .past => [.w, .a, .l, .k, .e, .d]
  | .go, .base => [.g, .o]
  | .go, .past => [.w, .e, .n, .t]

/-- The letter-trigram cue inventory of the four forms (§12.9 codes forms as letter trigrams). -/
def trigram : Fin 13 → Augmented Letter :=
  ![[none, some .w, some .a], [some .w, some .a, some .l], [some .a, some .l, some .k],
    [some .l, some .k, none], [some .l, some .k, some .e], [some .k, some .e, some .d],
    [some .e, some .d, none], [none, some .g, some .o], [some .g, some .o, none],
    [none, some .w, some .e], [some .w, some .e, some .n], [some .e, some .n, some .t],
    [some .n, some .t, none]]

/-- The past-tense form table at the trigram coding. -/
def pastTense (v : Verb) (t : Tense) : FormVec 13 := cueVector 3 trigram (form v t)

/-- The English past tense violates proportional analogy: *walked* adds the cue `ed#` to *walk*,
*went* adds nothing to *go*. So no linear DLM produces it from constructed meanings
(`not_exists_paradigm_eq_of_not_regular`), while independent embeddings realise it
(`exists_paradigm_eq_of_linearIndependent`), as in §12.9. -/
theorem pastTense_not_regular : ¬ IsAnalogicallyRegular pastTense := fun h => by
  have := congrFun (isAnalogicallyRegular_iff.1 h .walk .go .past .base) 6
  simp +decide [pastTense, cueVector, multiHot] at this

/-! ### Training on a paradigm -/

variable [Fintype Lexeme] [Fintype Cell]

/-- The paradigm as a training experience: imputed semantics as the semantic matrix, the form
table as the form matrix. -/
noncomputable def paradigmExperience (f : Lexeme → Cell → FormVec n) :
    TrainingExperience (Fintype.card (Lexeme × Cell)) n d where
  S := Matrix.of fun i => imputed σ ε ((Fintype.equivFin (Lexeme × Cell)).symm i).1
    ((Fintype.equivFin (Lexeme × Cell)).symm i).2
  C := Matrix.of fun i => f ((Fintype.equivFin (Lexeme × Cell)).symm i).1
    ((Fintype.equivFin (Lexeme × Cell)).symm i).2

open Matrix in
/-- Irregularity forces positive training loss: no mapping matrix fits a suppletive paradigm
exactly, so every trained matrix carries residual error. -/
theorem pos_weightedLoss_of_not_regular {f : Lexeme → Cell → FormVec n}
    (hf : ¬ IsAnalogicallyRegular f) {q : FrequencyVector (Fintype.card (Lexeme × Cell))}
    (hq : ∀ i, 0 < q i) (G : Matrix (Fin d) (Fin n) ℝ) :
    0 < weightedLoss (paradigmExperience σ ε f) q G := by
  refine lt_of_le_of_ne (weightedLoss_nonneg _ _ _) (Ne.symm fun h0 => ?_)
  have hint := (weightedLoss_eq_zero_iff _ _ _ hq).1 h0
  refine not_exists_paradigm_eq_of_not_regular σ ε hf
    ⟨⟨0, Matrix.toLin' Gᵀ⟩, funext fun l => funext fun c => funext fun j => ?_⟩
  have h := congrFun (congrFun hint ((Fintype.equivFin (Lexeme × Cell)) (l, c))) j
  simpa [paradigmExperience, Linear.paradigm, Matrix.toLin'_apply, Matrix.mulVec_transpose,
    Matrix.mul_apply, Matrix.vecMul, dotProduct] using h

end HeitmeierChuangBaayen2026
