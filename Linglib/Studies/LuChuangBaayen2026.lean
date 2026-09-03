import Linglib.Processing.DiscriminativeLexicon.Training
import Linglib.Studies.ChuangEtAl2026

/-!
# Lu, Chuang and Baayen 2026: tonal realization in spontaneous Taiwan Mandarin

[lu-chuang-baayen-2026] survey the f0 contours of disyllabic words across all 20 tone patterns
of Taiwan Mandarin, a lexical tone followed by a lexical or neutral tone (Table 1), in
[fon-2004]'s corpus of spontaneous speech. In generalized additive mixed models, word and sense
outweigh tone pattern as predictors of the contour (§3.4). Following
[chuang-bell-tseng-baayen-2026], a linear mapping from 768-dimensional GPT-2 contextualized
embeddings to 100-sample normalized pitch contours, fitted by least squares on the training
tokens (§4.3, the method of [gahl-baayen-2024]), predicts held-out tokens' contours above
chance, and the centroid embedding of each tone pattern maps to a contour close to the GAMM
contour of that pattern (§4.4, Fig. 9): the average pitch contours correspond to average
embeddings (§4.5). The discussion (§5) meets the tone-sandhi objection empirically, T3-T3 and
T2-T3 being neutralized in Taiwan Mandarin ([lu-chuang-baayen-2024]) so that T3-T3 words can
simply be reclassified, and theoretically: the model predicts forms from meanings, never forms
from forms, and the tone-pattern contours emerge without the model being told the patterns.
The lab-speech contours of [xu-1997] match the predicted ones for several patterns (Fig. 11).

This file instantiates the DLM at the paper's carriers and states the model-side half of the
centroid claim at them. Linearity alone sends a centroid to the mean of the predicted contours
(`LinearMap.map_centroid`); training does better: whenever membership in a set of training
tokens is a linear functional of the embeddings, the least-squares map sends that set's
centroid exactly to the mean of its target contours (`production_centroid_eq_of_decodable`,
the substrate's `Linear.IsELTrainedOn.production_centroid_eq_of_decodable`, shared with
[chuang-bell-tseng-baayen-2026]'s Fig. 18). The paper's centroids weight word types equally
rather than tokens (§4.4) and Fig. 9 compares against GAMM contours, so the match it reports
is approximate; the theorem states what least squares guarantees when a tone pattern is
linearly recoverable from meaning. The GAMM fits and the nearest-neighbour accuracies are
outside the Processing scope.

## Main results

* `production_centroid_eq_of_decodable`: a least-squares-trained map sends the centroid of a
  linearly decodable tone pattern's tokens exactly to the mean of their target contours.

## References

* [Y. Lu, Y.-Y. Chuang and R. H. Baayen, *The realization of tones in spontaneous spoken Taiwan
  Mandarin: a corpus-based survey and theory-driven computational modeling*
  (2026)][lu-chuang-baayen-2026]
* [Y. Lu, Y.-Y. Chuang and R. H. Baayen, *Form and meaning co-determine the realization of tone
  in Taiwan Mandarin spontaneous speech* (2024)][lu-chuang-baayen-2024]
* [Y.-Y. Chuang, M. J. Bell, Y.-H. Tseng and R. H. Baayen, *Word-specific tonal realizations
  in Mandarin* (2026)][chuang-bell-tseng-baayen-2026]
* [S. Gahl and R. H. Baayen, *Time and thyme again* (2024)][gahl-baayen-2024]
* [J. Fon, *A preliminary construction of Taiwan Southern Min spontaneous speech corpus*
  (2004)][fon-2004]
* [Y. Xu, *Contextual tonal variations in Mandarin* (1997)][xu-1997]
-/

namespace LuChuangBaayen2026

open DiscriminativeLexicon ChuangEtAl2026

/-- The paper samples 100 f0 values per token in normalized time, centered and scaled per
token (§4.1). -/
abbrev PitchSampleCount : ℕ := 100

/-- A pitch contour at the paper's resolution. -/
abbrev PitchVector : Type := FormVec PitchSampleCount

/-- The paper's DLM: 100-sample pitch vectors from the 768-dimensional CKIP GPT-2
contextualized embeddings of [chuang-bell-tseng-baayen-2026] (§4.2). -/
abbrev TaiwanMandarinDLM : Type := Linear ℝ PitchVector ContextualEmbedding

/-- **Centroids under least squares** (§4.4, Fig. 9): if membership in a tone pattern's set `P`
of training tokens is a linear functional of their embeddings, a least-squares-trained production
map sends the centroid of `P`'s embeddings exactly to the centroid of `P`'s target contours. -/
theorem production_centroid_eq_of_decodable {m : ℕ} {D : TaiwanMandarinDLM}
    {data : TrainingExperience m PitchSampleCount CKIPGPT2HiddenDim} (hD : D.IsELTrainedOn data)
    {P : Finset (Fin m)} (hP : P.Nonempty) {w : ContextualEmbedding →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.S i) = if i ∈ P then 1 else 0) :
    D.production (P.centroid ℝ data.S) = P.centroid ℝ data.C :=
  hD.production_centroid_eq_of_decodable hP hw

end LuChuangBaayen2026
