import Linglib.Processing.DiscriminativeLexicon.Training

/-!
# Chuang, Bell, Tseng and Baayen 2026: Word-specific tonal realizations in Mandarin

The pitch contour of a Mandarin disyllabic word is taken to realize the lexical tones of its
syllables under voluntary constraints (intonation, focus) and involuntary ones (coarticulation,
speech rate, segmental makeup); the paper adds the token's meaning in context as a fourth
co-determinant, in four predictions tested on the 3,778 rise–fall (T2–T4) tokens of 51 word
types in a corpus of spontaneous Taiwan Mandarin ([fon-2004]). A generalized additive model of
the f0 contour with a by-word factor smooth beats the six segment-related controls combined, in
AIC and in cross-validated error (§2.6), and a sense smooth beats the word smooth on the senses
with enough tokens (§2.7). A Discriminative Lexicon Model ([baayen-2019],
[heitmeier-chuang-baayen-2026]) trained on token pairs of 50-sample min–max-normalized
contours (§3.2) and 768-dimensional CKIP GPT-2 contextualized embeddings (§3.1) predicts word
type from contour and contour from embedding an order of magnitude above chance, the production
direction being fully linear (§3.3–3.4); the contour the linear production network produces
from a word's centroid embedding matches the average of that word's training contours and the
word GAM's contour for it (Fig. 18), and the grand centroid of all tokens produces the
unmodulated rise–fall contour. The discussion (§4) reads the match as isomorphy between the
form space of contours and the meaning space of embeddings, against the dual-articulation axiom
the paper attributes to Martinet, and takes tonal patterns, like every lexical representation,
to be unstored: the connection weights of the two networks carry all form–meaning knowledge.
The file accordingly lives on continuous f0 vectors rather than on the discrete-tone substrate
(`Phonology/Tone/`), whose categories §4 contests.

`PitchContour`, `ContextualEmbedding` and `TaiwanMandarinRFDLM` instantiate the substrate's
`DiscriminativeLexicon.Linear` at the paper's carriers. Fn. 29's remark that no linear map
takes the fifty-dimensional contour space onto the 768-dimensional embedding space is
`comprehension_not_surjective`, so no comprehension network inverts production
(`comprehension_comp_production_ne_id`). Fig. 18's match is
`production_centroid_eq_of_decodable`: a word type being the set of tokens carrying its corpus
label (§1, §2.2), the normal equations send the centroid of its embeddings exactly to the
average of its training contours whenever membership in it is a linear functional of the
embeddings, the idealization of Fig. 14's distinct word-type regions (the substrate's
`Linear.IsELTrainedOn.production_centroid_eq_of_decodable`); `production_centroid_univ_eq` is
the grand-centroid case. The GAM fits, the nearest-neighbour accuracies and the residual network
ResLDL are not represented.

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

namespace ChuangEtAl2026

open DiscriminativeLexicon Finset

/-- The fifty f0 values sampled per token at equally spaced points of normalized time
(§3.2). -/
abbrev TaiwanMandarinPitchSampleCount : ℕ := 50

/-- The dimension of CKIP's GPT-2 character vectors (§3.1). -/
abbrev CKIPGPT2HiddenDim : ℕ := 768

/-- A pitch contour: the fifty samples, centered by the token's mean and scaled by its range
(§3.2), so a shape rather than a pitch or an amplitude. -/
abbrev PitchContour : Type := FormVec TaiwanMandarinPitchSampleCount

/-- A contextualized embedding: the mean of the GPT-2 vectors of a token's two characters given
the preceding context, the current utterance up to the token and the one before it (§3.1). -/
abbrev ContextualEmbedding : Type := MeaningVec CKIPGPT2HiddenDim

/-- The paper's DLM: linear comprehension and production maps between the two carriers
(§3.3–3.4). -/
abbrev TaiwanMandarinRFDLM : Type :=
  Linear ℝ PitchContour ContextualEmbedding

variable (D : TaiwanMandarinRFDLM)

/-! ### Comprehension from fifty dimensions (§3.3) -/

/-- Fn. 29: no linear map takes the fifty-dimensional contour space onto the 768-dimensional
embedding space, the paper's ground for finding ResLDL's comprehension advantage over LDL
unsurprising (§3.3.2). -/
theorem comprehension_not_surjective : ¬ Function.Surjective D.comprehension := fun h => by
  simpa [CKIPGPT2HiddenDim, TaiwanMandarinPitchSampleCount] using
    LinearMap.finrank_le_finrank_of_surjective (f := D.comprehension) h

/-- Fn. 29's picture: points of a cube projected onto a plane cannot be recovered from the
projection, so no comprehension network inverts production. -/
theorem comprehension_comp_production_ne_id :
    D.comprehension ∘ₗ D.production ≠ LinearMap.id := fun h =>
  comprehension_not_surjective D <| Function.Surjective.of_comp (g := D.production) <| by
    rw [← LinearMap.coe_comp, h]; exact Function.surjective_id

/-! ### Word-centroid contours (§3.4) -/

variable {D} {m : ℕ} {W : Type*} [DecidableEq W]
  {data : TrainingExperience m TaiwanMandarinPitchSampleCount CKIPGPT2HiddenDim}

/-- Fig. 18: a word type being the set of tokens carrying its corpus label (§1, §2.2), a
least-squares-trained production map sends the centroid of its embeddings to the average of
its training contours whenever membership in it is a linear functional of the embeddings. The
paper reports the match as remarkable similarity, Fig. 14's distinct word-type regions being
its evidence for the hypothesis. -/
theorem production_centroid_eq_of_decodable (hD : D.IsELTrainedOn data) (word : Fin m → W)
    {w : W} (hw : ∃ i, word i = w) {ℓ : ContextualEmbedding →ₗ[ℝ] ℝ}
    (hℓ : ∀ i, ℓ (data.S i) = if word i = w then 1 else 0) :
    D.production ((univ.filter (word · = w)).centroid ℝ data.S) =
      (univ.filter (word · = w)).centroid ℝ data.C :=
  hD.production_centroid_eq_of_decodable (by simpa [filter_nonempty_iff] using hw)
    (by simpa using hℓ)

/-- §3.4.2: the grand centroid of all tokens' embeddings, which the paper reads as the meaning
of the unmodulated rise–fall contour (Fig. 1), produces the grand-mean training contour when
some linear functional is constant on the training embeddings. -/
theorem production_centroid_univ_eq [NeZero m] (hD : D.IsELTrainedOn data)
    {ℓ : ContextualEmbedding →ₗ[ℝ] ℝ} (hℓ : ∀ i, ℓ (data.S i) = 1) :
    D.production (univ.centroid ℝ data.S) = univ.centroid ℝ data.C :=
  hD.production_centroid_eq_of_decodable ⟨0, mem_univ 0⟩ (by simpa using hℓ)

end ChuangEtAl2026
