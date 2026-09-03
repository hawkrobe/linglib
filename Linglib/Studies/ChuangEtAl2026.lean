import Linglib.Processing.DiscriminativeLexicon.Training

/-!
# Chuang, Bell, Tseng & Baayen 2026: Word-specific tonal realizations in Mandarin

Mandarin disyllabic words with the rise–fall tonal pattern (T2 followed by T4) in
spontaneous Taiwan Mandarin speech: 3,778 tokens across 51 word types
([chuang-bell-tseng-baayen-2026]). Standard accounts attribute variation in tonal
realization to lexical tone, voluntary intonation/focus, and involuntary
articulatory constraints; the paper adds a fourth co-determiner — word meaning —
via four predictions:

1. **Word type predicts f0 above segmental controls** (§2.6.1–2.6.2, Figs. 4, 6):
   adding a by-word factor smooth to the baseline GAM of the f0 contour drops AIC
   by 6,795 units, beating all six segment-related controls combined (vowel
   height, onset type, rhyme structure, each on both syllables) by 1,857 units;
   the word model also wins the cross-validated SSE comparison.
2. **Sense further refines word** (§2.7.1, Figs. 10–11): on the subset with ≥ 14
   tokens per sense (3,458 tokens, 65 senses, 48 word types), a sense factor
   smooth (−6,443 AIC) beats the word smooth (−6,078) by 365 units — e.g. the
   four senses of *bu2yao4* have visibly distinct contours — though the two
   models' cross-validated SSE medians stay similar (§2.7.2, Fig. 12: most types
   are represented by a single sense).
3. **f0 → meaning** (§3.3, Fig. 16): a comprehension net from token pitch
   contours to contextualized embeddings reaches ~30% (linear LDL) / ~50%
   (ResLDL) test accuracy at nearest-neighbour word-type matching, against a
   ~3.5% permutation baseline.
4. **meaning → f0** (§3.4, Figs. 17–18): the reverse production net reaches ~40%
   test accuracy, with linear and nonlinear models on par — the meaning-to-form
   mapping is dominantly linear — and LDL contours predicted from word-centroid
   embeddings match the word GAM's per-word contours: the paper's headline
   form–meaning isomorphy.

The discussion (§4) draws the consequences: word meaning co-determines phonetic
realization; the pitch-contour form space and the embedding meaning space are
measurably isomorphic, against the dual-articulation axiom (the paper cites
Martinet 1965) of form and meaning as orthogonal components of grammar; and
nothing is stored — neither tonal patterns nor any other lexical representations
("neither abstract underlying representations nor exemplars") — the DLM's
connection weights carry all form–meaning knowledge. This file accordingly lives
on continuous f0 vectors, not the discrete-tone substrate (`Phonology/Tone/`,
`Autosegmental.FloatingForm`): bridging the two would presuppose the
discretization of tonal categories that §4 contests.

The GAM and DLM fit results above are empirical findings, recorded in prose per
the Processing scope. The Lean content instantiates the DLM substrate
(`Processing/DiscriminativeLexicon/`, [baayen-2019]
[heitmeier-chuang-baayen-2026]) at the paper's carriers and derives the two
structural claims the paper makes about its linear networks. Fn. 29's dimension
argument: a linear comprehension map from fifty-sample contours reaches at most a
fifty-dimensional subspace of the embedding space (`comprehension_not_surjective`),
so no comprehension network undoes the production network
(`comprehension_comp_production_ne_id`). Fig. 18's word-centroid contours: the
paper reports the LDL contour produced from a word's centroid embedding as
remarkably similar to the average of that word's training contours, and reads the
match as form–meaning isomorphy; least squares makes it exact whenever word-type
membership is a linear functional of the embeddings — the idealization of Fig. 14's
distinct word-type regions — because the normal equations force fitted and observed
forms to agree on every linearly decodable average
(`production_centroid_eq_of_decodable`, over the substrate's
`Linear.IsELTrainedOn.production_centroid_eq_of_decodable`). The grand centroid of
all tokens, which the paper reads as the meaning of the unmodulated rise–fall
contour, maps to the grand-mean training contour under the same hypothesis for the
whole data set (`production_centroid_univ_eq`). The substrate's
`Linear.norm_production_sub_le` is the quantitative form of §4's isomorphy claim:
embeddings within `ε` of each other produce contours within `‖production‖ * ε`.

## Main results

* `PitchContour` / `ContextualEmbedding` / `TaiwanMandarinRFDLM` — the paper's
  carriers: 50-sample min–max-normalized pitch shapes (§3.2) and 768-dim CKIP
  GPT-2 contextualized embeddings (§3.1)
* `comprehension_not_surjective`, `comprehension_comp_production_ne_id` — fn. 29:
  a linear map from 50-dimensional pitch space cannot reach all of the
  768-dimensional embedding space, so no comprehension map inverts production
* `production_centroid_eq_of_decodable` — Fig. 18: a trained LDL production net
  sends a word type's centroid embedding to the average of its training contours
  whenever word-type membership is linearly decodable from the embeddings
* `production_centroid_univ_eq` — §3.4.2: the grand centroid of all tokens maps
  to the grand-mean contour

## References

* [Y.-Y. Chuang, M. J. Bell, Y.-H. Tseng, R. H. Baayen, *Word-specific tonal
  realizations in Mandarin* (2026)][chuang-bell-tseng-baayen-2026]
* [R. H. Baayen, Y.-Y. Chuang, E. Shafaei-Bajestan, J. P. Blevins, *The
  discriminative lexicon* (2019)][baayen-2019]
* [M. Heitmeier, Y.-Y. Chuang, R. H. Baayen, *The Discriminative Lexicon:
  Theory, Implementation in the Julia Package JudiLing, and Applications*
  (2026)][heitmeier-chuang-baayen-2026]
-/

namespace ChuangEtAl2026

open DiscriminativeLexicon Finset

/-- The paper samples 50 evenly-spaced f0 values per token from the GAM-smoothed
contour (§3.2). -/
abbrev TaiwanMandarinPitchSampleCount : ℕ := 50

/-- CKIP's GPT-2 for traditional Chinese encodes each character as a
768-dimensional vector (§3.1). -/
abbrev CKIPGPT2HiddenDim : ℕ := 768

/-- A pitch contour: 50 f0 samples on normalized time [0, 1], centered and
scaled per token (§3.2's min–max normalization) — pitch **shape**, not absolute
pitch or amplitude. -/
abbrev PitchContour : Type := FormVec TaiwanMandarinPitchSampleCount

/-- A contextualized embedding: the 768-dim CKIP GPT-2 vector for a token given
its preceding context — the current utterance up to the token plus the utterance
before it (§3.1). Tokens of one word type carry distinct, context-specific
embeddings. -/
abbrev ContextualEmbedding : Type := MeaningVec CKIPGPT2HiddenDim

/-- The paper's DLM instantiation for Taiwan Mandarin rise–fall disyllables. -/
abbrev TaiwanMandarinRFDLM : Type :=
  Linear ℝ PitchContour ContextualEmbedding

variable (D : TaiwanMandarinRFDLM)

/-! ### Comprehension from fifty dimensions (§3.3) -/

/-- **Fn. 29** (§3.3): "it is impossible to map a lower-dimensional space into a
higher-dimensional space with a linear mapping without losing information" — any
linear comprehension map from 50-sample pitch contours reaches at most a
50-dimensional subspace of the 768-dimensional embedding space, the paper's
ground for finding ResLDL's comprehension advantage over LDL "unsurprising". -/
theorem comprehension_not_surjective : ¬ Function.Surjective D.comprehension := fun h => by
  simpa [CKIPGPT2HiddenDim, TaiwanMandarinPitchSampleCount] using
    LinearMap.finrank_le_finrank_of_surjective (f := D.comprehension) h

/-- Fn. 29's picture: points of a cube projected onto a plane cannot be recovered
from the projection. No comprehension network undoes the production network — the
round trip through pitch space is never the identity on embeddings. -/
theorem comprehension_comp_production_ne_id :
    D.comprehension ∘ₗ D.production ≠ LinearMap.id := fun h =>
  comprehension_not_surjective D <| Function.Surjective.of_comp (g := D.production) <| by
    rw [← LinearMap.coe_comp, h]; exact Function.surjective_id

/-! ### Word-centroid contours (§3.4) -/

variable {D} {m : ℕ} {W : Type*} [DecidableEq W]
  {data : TrainingExperience m TaiwanMandarinPitchSampleCount CKIPGPT2HiddenDim}

/-- **Fig. 18** (§3.4): a word type is the set of tokens carrying the corpus's word
label (§1, §2.2); the paper maps the centroid of a word's contextualized
embeddings through the LDL production network and finds the result remarkably
similar to the average of the word's training contours. Least squares makes the
match exact whenever membership in the word type is a linear functional of the
embeddings — the idealization of Fig. 14's distinct word-type regions. -/
theorem production_centroid_eq_of_decodable (hD : D.IsELTrainedOn data) (word : Fin m → W)
    {w : W} (hw : ∃ i, word i = w) {ℓ : ContextualEmbedding →ₗ[ℝ] ℝ}
    (hℓ : ∀ i, ℓ (data.S i) = if word i = w then 1 else 0) :
    D.production ((univ.filter (word · = w)).centroid ℝ data.S) =
      (univ.filter (word · = w)).centroid ℝ data.C :=
  hD.production_centroid_eq_of_decodable (by simpa [filter_nonempty_iff] using hw)
    (by simpa using hℓ)

/-- **The grand centroid** (§3.4.2): the contour produced from the centroid of all
tokens' embeddings resembles the unmodulated rise–fall contour (Fig. 1), so the
paper reads that centroid as the contour's "meaning". If some linear functional
is constant on every training embedding, the produced contour is exactly the
grand-mean training contour. -/
theorem production_centroid_univ_eq [NeZero m] (hD : D.IsELTrainedOn data)
    {ℓ : ContextualEmbedding →ₗ[ℝ] ℝ} (hℓ : ∀ i, ℓ (data.S i) = 1) :
    D.production (univ.centroid ℝ data.S) = univ.centroid ℝ data.C :=
  hD.production_centroid_eq_of_decodable ⟨0, mem_univ 0⟩ (by simpa using hℓ)

end ChuangEtAl2026
