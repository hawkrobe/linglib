import Linglib.Processing.Lexical.Discriminative.Coding
import Linglib.Processing.Lexical.Discriminative.Training
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
irregular verbs was produced correctly" (§12.9). This file states why. Over additive semantics a
linear map's form table satisfies proportional analogy by construction, so a table violating
analogy has no linear interpolant and forces positive training loss, and when stem and exponent
vectors are jointly independent linear realisability is exactly analogy. Over word-specific
embeddings, by contrast, any table is linearly realisable as soon as the embeddings are linearly
independent, which fills the irregular-linear cell of Table 16.2. The English past tense at the
book's letter-trigram coding (§12.9, `cueVector`) is the irregular table: *walk, walked* against
*go, went*.

## Main results

* `not_exists_linear_of_not_regular`, `pos_weightedLoss_of_not_regular`: an irregular table has
  no linear interpolant over additive semantics and forces positive loss.
* `exists_linear_iff_isAnalogicallyRegular`: over jointly independent stem and exponent vectors,
  linear realisability is analogy.
* `exists_linear_of_linearIndependent_words`: over independent word-specific embeddings every
  table is linearly realisable.
* `pastTense_not_regular`: *walk, walked, go, went* violates analogy.

## References

* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

namespace HeitmeierChuangBaayen2026

open Processing.Lexical.Discriminative

variable {d n : ℕ} {Stem Cell : Type*}

/-- A paradigm's form table satisfies **proportional analogy** if the form contrast between two
cells is the same for every stem (*cat : cats :: dog : dogs*). -/
def IsAnalogicallyRegular (f : Stem → Cell → FormVec n) : Prop :=
  ∀ st st' c c', f st c - f st c' = f st' c - f st' c'

/-! ### Additive semantics -/

variable (σ : Stem → MeaningVec d) (ε : Cell → MeaningVec d)

/-- Conceptualizing a paradigm cell from its stem and cell primitives is the imputed additive
semantics (eq. 5.3, Table 12.7). -/
@[simp] theorem conceptualize_pair (st : Stem) (c : Cell) :
    conceptualize (Sum.elim σ ε) {Sum.inl st, Sum.inr c} = σ st + ε c := by
  simp

/-- Every linear map's paradigm table over additive semantics is analogically regular: the form
shift of an exponent is stem-independent. -/
theorem isAnalogicallyRegular_comp (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    IsAnalogicallyRegular fun st c => G (σ st + ε c) := fun st st' c c' => by
  simp only [map_add]
  abel

/-- A table violating proportional analogy has no linear interpolant over additive semantics:
irregular forms cannot be produced from constructed meanings (§12.9). -/
theorem not_exists_linear_of_not_regular {f : Stem → Cell → FormVec n}
    (hf : ¬ IsAnalogicallyRegular f) :
    ¬ ∃ G : MeaningVec d →ₗ[ℝ] FormVec n, ∀ st c, G (σ st + ε c) = f st c := by
  rintro ⟨G, hG⟩
  exact hf (by simpa only [hG] using isAnalogicallyRegular_comp σ ε G)

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

/-- Over word-specific, linearly independent embeddings any form table is linearly realisable,
irregulars included: the irregular-linear cell of Table 16.2, the English past tense on empirical
embeddings (§12.9). -/
theorem exists_linear_of_linearIndependent_words {s : Stem → Cell → MeaningVec d}
    (hs : LinearIndependent ℝ (Function.uncurry s)) (f : Stem → Cell → FormVec n) :
    ∃ G : MeaningVec d →ₗ[ℝ] FormVec n, ∀ st c, G (s st c) = f st c :=
  let ⟨G, hG⟩ := exists_linear_of_linearIndependent hs (Function.uncurry f)
  ⟨G, fun st c => hG (st, c)⟩

/-- When stem and exponent vectors are jointly linearly independent, a paradigm table is linearly
realisable over additive semantics **iff** it is analogically regular: for a regularized system,
linearity and regularity are the same constraint (§16.6). -/
theorem exists_linear_iff_isAnalogicallyRegular [Nonempty Stem] [Nonempty Cell]
    (hind : LinearIndependent ℝ (Sum.elim σ ε)) (f : Stem → Cell → FormVec n) :
    (∃ G : MeaningVec d →ₗ[ℝ] FormVec n, ∀ st c, G (σ st + ε c) = f st c) ↔
      IsAnalogicallyRegular f := by
  refine ⟨fun ⟨G, hG⟩ => by simpa only [hG] using isAnalogicallyRegular_comp σ ε G,
    fun hreg => ?_⟩
  obtain ⟨st₀⟩ := ‹Nonempty Stem›
  obtain ⟨c₀⟩ := ‹Nonempty Cell›
  obtain ⟨G, hG⟩ := exists_linear_of_linearIndependent hind
    (Sum.elim (fun st => f st c₀) fun c => f st₀ c - f st₀ c₀)
  refine ⟨G, fun st c => ?_⟩
  have hσ : G (σ st) = f st c₀ := hG (Sum.inl st)
  have hε : G (ε c) = f st₀ c - f st₀ c₀ := hG (Sum.inr c)
  rw [map_add, hσ, hε, ← hreg st st₀ c c₀]
  abel

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
*went* adds nothing to *go*. So no linear map produces it from constructed meanings
(`not_exists_linear_of_not_regular`), while independent embeddings realise it
(`exists_linear_of_linearIndependent_words`), as in §12.9. -/
theorem pastTense_not_regular : ¬ IsAnalogicallyRegular pastTense := fun h => by
  have := congrFun (h .walk .go .past .base) 6
  simp +decide [pastTense, cueVector, multiHot] at this

/-! ### Training on a paradigm -/

variable [Fintype Stem] [Fintype Cell]

/-- The paradigm as a training experience: conceptualized additive semantics as the meanings,
the form table as the targets. -/
noncomputable def paradigmExperience (f : Stem → Cell → FormVec n) :
    TrainingExperience (Fintype.card (Stem × Cell)) n d where
  meanings i := conceptualize (Sum.elim σ ε)
    {Sum.inl ((Fintype.equivFin (Stem × Cell)).symm i).1,
      Sum.inr ((Fintype.equivFin (Stem × Cell)).symm i).2}
  forms i := f ((Fintype.equivFin (Stem × Cell)).symm i).1
    ((Fintype.equivFin (Stem × Cell)).symm i).2

/-- Irregularity forces positive training loss: no linear map fits a suppletive paradigm exactly,
so every ERM solution carries residual error. -/
theorem pos_weightedLoss_of_not_regular {f : Stem → Cell → FormVec n}
    (hf : ¬ IsAnalogicallyRegular f) {q : FrequencyVector (Fintype.card (Stem × Cell))}
    (hq : ∀ i, 0 < q i) (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    0 < weightedLoss (paradigmExperience σ ε f) q G := by
  refine lt_of_le_of_ne (weightedLoss_nonneg _ _ _) (Ne.symm fun h0 => ?_)
  have hint := (weightedLoss_eq_zero_iff _ _ _ hq).1 h0
  refine not_exists_linear_of_not_regular σ ε hf ⟨G, fun st c => ?_⟩
  have h := hint ((Fintype.equivFin (Stem × Cell)) (st, c))
  simpa [paradigmExperience] using h

end HeitmeierChuangBaayen2026
