module

public import Linglib.Processing.DiscriminativeLexicon.Training

/-!
# Chuang, Bell, Tseng and Baayen (2026): Word-specific tonal realizations in Mandarin

The pitch contour of a Mandarin disyllabic word is usually taken to realize the lexical tones of
its syllables under constraints such as intonation, coarticulation and speech rate. Chuang, Bell,
Tseng and Baayen add the token's meaning in context as a further determinant. On the 3,778
rise–fall (T2–T4) tokens of 51 word types in Fon's corpus of spontaneous Taiwan Mandarin, a
generalized additive model with a by-word smooth beats the segmental controls combined (§2.6). A
discriminative lexicon trained on pairs of 50-sample normalized contours (§3.2) and
768-dimensional contextualized embeddings (§3.1) predicts word type from contour and contour from
embedding an order of magnitude above chance (§3.3–3.4).

The contour that the linear production map produces from a word's centroid embedding closely
resembles the average of that word's training contours (Fig. 18), and the centroid of all tokens
produces the unmodulated rise–fall contour (§3.4.2). The paper reads this as isomorphy between
the space of contours and the space of embeddings, against the dual articulation it attributes
to Martinet (§4). The file accordingly works on continuous f0 vectors rather than on discrete
tones.

## Main statements

* `ChuangEtAl2026.comprehension_comp_production_ne_id`: no linear map takes the fifty-dimensional
  contour space onto the 768-dimensional embedding space, so no comprehension map inverts
  production.
* `ChuangEtAl2026.production_centroid_eq_of_decodable`: a least-squares-trained production map
  sends the centroid of a word type's embeddings to the average of its training contours
  whenever membership in the word type is a linear functional of the embeddings.
* `ChuangEtAl2026.production_centroid_univ_eq`: the centroid of all tokens produces the
  grand-mean training contour.

## Implementation notes

* A word type is the set of tokens carrying its corpus label (§1, §2.2). Linear decodability
  idealizes the distinct word-type regions of Fig. 14.
* The additive models, the nearest-neighbour accuracies and the residual network ResLDL are not
  represented.

## References

* [Y.-Y. Chuang, M. J. Bell, Y.-H. Tseng and R. H. Baayen, *Word-specific tonal
  realizations in Mandarin* (2026)][chuang-bell-tseng-baayen-2026]
* [R. H. Baayen, Y.-Y. Chuang, E. Shafaei-Bajestan and J. P. Blevins, *The discriminative
  lexicon* (2019)][baayen-2019]
* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
* [J. Fon, *A preliminary construction of Taiwan Southern Min spontaneous speech corpus*
  (2004)][fon-2004]
-/

@[expose] public section

namespace ChuangEtAl2026

open DiscriminativeLexicon Finset

/-- The fifty f0 values sampled per token at equally spaced points of normalized time
(§3.2). -/
abbrev TaiwanMandarinPitchSampleCount : ℕ := 50

/-- The dimension of CKIP's GPT-2 character vectors (§3.1). -/
abbrev CKIPGPT2HiddenDim : ℕ := 768

/-- A pitch contour consists of the fifty samples, centered by the token's mean and scaled by its
range (§3.2), so it is a shape rather than a pitch or an amplitude. -/
abbrev PitchContour : Type := FormVec TaiwanMandarinPitchSampleCount

/-- A contextualized embedding is the mean of the GPT-2 vectors of a token's two characters given
the preceding context, the current utterance up to the token and the one before it (§3.1). -/
abbrev ContextualEmbedding : Type := MeaningVec CKIPGPT2HiddenDim

/-- The paper's DLM consists of linear comprehension and production maps between pitch contours
and contextualized embeddings (§3.3–3.4). -/
abbrev TaiwanMandarinRFDLM : Type :=
  Linear ℝ PitchContour ContextualEmbedding

variable (D : TaiwanMandarinRFDLM)

/-! ### Comprehension from fifty dimensions (§3.3) -/

/-- No linear map takes the fifty-dimensional contour space onto the 768-dimensional embedding
space, the paper's ground for finding ResLDL's comprehension advantage over LDL unsurprising
(§3.3.2, fn. 29). -/
theorem comprehension_not_surjective : ¬ Function.Surjective D.comprehension := fun h ↦ by
  simpa [CKIPGPT2HiddenDim, TaiwanMandarinPitchSampleCount] using
    LinearMap.finrank_le_finrank_of_surjective (f := D.comprehension) h

/-- Points of a cube projected onto a plane cannot be recovered from the projection, the picture
of fn. 29, so no comprehension network inverts production. -/
theorem comprehension_comp_production_ne_id :
    D.comprehension ∘ₗ D.production ≠ LinearMap.id := fun h ↦
  comprehension_not_surjective D <| Function.Surjective.of_comp (g := D.production) <| by
    rw [← LinearMap.coe_comp, h]; exact Function.surjective_id

/-! ### Word-centroid contours (§3.4) -/

variable {D} {m : ℕ} {W : Type*} [DecidableEq W]
  {data : TrainingExperience m TaiwanMandarinPitchSampleCount CKIPGPT2HiddenDim}

/-- A word type being the set of tokens carrying its corpus label (§1, §2.2), a
least-squares-trained production map sends the centroid of its embeddings to the average of
its training contours whenever membership in it is a linear functional of the embeddings. The
paper reports the match as remarkable similarity (Fig. 18), Fig. 14's distinct word-type regions
being its evidence for the hypothesis. -/
theorem production_centroid_eq_of_decodable (hD : D.IsELTrainedOn data) (word : Fin m → W)
    {w : W} (hw : ∃ i, word i = w) {ℓ : ContextualEmbedding →ₗ[ℝ] ℝ}
    (hℓ : ∀ i, ℓ (data.S i) = if word i = w then 1 else 0) :
    D.production ((univ.filter (word · = w)).centroid ℝ data.S.row) =
      (univ.filter (word · = w)).centroid ℝ data.C.row :=
  hD.production_centroid_eq_of_decodable (by simpa [filter_nonempty_iff] using hw)
    (by simpa using hℓ)

/-- The centroid of all tokens' embeddings, which the paper reads as the meaning of the
unmodulated rise–fall contour (§3.4.2, Fig. 1), produces the grand-mean training contour when
some linear functional is constant on the training embeddings. -/
theorem production_centroid_univ_eq [NeZero m] (hD : D.IsELTrainedOn data)
    {ℓ : ContextualEmbedding →ₗ[ℝ] ℝ} (hℓ : ∀ i, ℓ (data.S i) = 1) :
    D.production (univ.centroid ℝ data.S.row) = univ.centroid ℝ data.C.row :=
  hD.production_centroid_eq_of_decodable ⟨0, mem_univ 0⟩ (by simpa using hℓ)

end ChuangEtAl2026
