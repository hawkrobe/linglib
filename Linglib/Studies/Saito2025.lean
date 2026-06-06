import Linglib.Processing.Lexical.Discriminative.Defs
import Linglib.Processing.Lexical.Discriminative.Normed
import Linglib.Processing.Lexical.Discriminative.Training

/-!
# Saito, Tomaschek & Baayen (2025): frequency × inflectional status via the DLM

[saito-tomaschek-baayen-2025] reanalyse German tongue-position data (560 tokens, 88 word
types sharing the rhyme `[a(:)(X)t]`, Karl-Eberhard Corpus): high-frequency *non-inflected*
words show articulatory reduction (tongue raising, for the low vowel `[a(:)]`), while in
high-frequency *inflected* words the reduction is attenuated (paper §2.2). Replacing the
binary inflectional-status factor with `SemSupSuffix` — semantic support from word meaning
to the suffix triphone, read off a trained DLM ([baayen-2019],
[heitmeier-chuang-baayen-2026]) — improves the tongue-position GAMM by 142.87 AIC units
with one fewer effective degree of freedom (paper §3.3, Table 3). The apparent
morphological-boundary effect is thus driven by inflectional semantics, challenging
production models with an intermediate morpheme layer such as WEAVER++
([levelt-roelofs-meyer-1999], [roelofs-1997]).

## Main declarations

* `GermanInflectionalDLM`: `LinearDiscriminativeLexicon` at the paper's carrier types,
  triphone form vectors of dimension 14404 and word2vec meaning vectors of dimension 300
  (paper §3.1).
* `close_meanings_imply_close_form`: the substrate Lipschitz bound at those carriers —
  close meanings yield close predicted articulations.
* `semSupSuffix_lt_of_forms_lt`: when the suffix triphone is linearly decodable from
  meanings, training alone gives suffix-bearing (inflected) words strictly greater
  suffix support — the direction of the paper's headline contrast.

## Implementation notes

The paper's positional measures `SemSupVowel` and `SemSupSuffix` (paper §3.1 eqs. 3–4) are
`semSup` (`Discriminative/Measures.lean`) at the stem-vowel and suffix triphone indices;
the paper's triphone indexing is not reproduced here, so they get no separate definitions.
The paper's production matrix `G` (solving `SG = C`) is the substrate's `production`, its
comprehension matrix `F` (solving `CF = S`) is `comprehension`. The DLM's
no-stored-entries architecture sits against the `Phonology/ItemSpecificity/` frequency
channels and [bybee-1985]'s `tokenFreq` (`Morphology/UsageBased/Network.lean`); cf. the
channel discrimination in `Studies/BreissKatsudaKawahara2026.lean`.
-/

namespace Saito2025

open Processing.Lexical.Discriminative

/-- Triphone count of the paper's CELEX-derived form matrix `C` (paper §3.1). -/
abbrev TriphoneCount : ℕ := 14404

/-- Dimension of the pretrained German word2vec embeddings of [muller-2015]. -/
abbrev Word2VecGermanDim : ℕ := 300

/-- Zero/one triphone-indicator form vectors. The binary structure is a property of the
training data, not of the type. -/
abbrev TriphoneVec := FormVec TriphoneCount

/-- 300-dimensional word2vec meaning vectors. -/
abbrev GermanWord2VecVec := MeaningVec Word2VecGermanDim

/-- The paper's DLM: `LinearDiscriminativeLexicon` at German triphone × word2vec
carrier types. -/
abbrev GermanInflectionalDLM :=
  LinearDiscriminativeLexicon ℝ TriphoneVec GermanWord2VecVec

/-- Close meanings yield close predicted articulations, with constant `‖production‖`. -/
theorem close_meanings_imply_close_form
    (D : GermanInflectionalDLM) (s₁ s₂ : GermanWord2VecVec) {ε : ℝ}
    (h : ‖s₁ - s₂‖ ≤ ε) :
    ‖D.production s₁ - D.production s₂‖ ≤
      ‖D.production.toContinuousLinearMap‖ * ε :=
  dlm_neighbor_centroids_imply_neighbor_contours D h

/-- If the suffix-triphone coordinate is linearly decodable from word meanings —
the paper's §4 mechanism, inflectional semantics tied to the suffix — then a
trained DLM's `SemSupSuffix` reproduces it exactly, so a word carrying the
suffix triphone (an inflected word) gets strictly greater suffix support than
one lacking it: the direction of the paper's headline contrast (its Fig. 11),
from the linear architecture alone. -/
theorem semSupSuffix_lt_of_forms_lt
    {m : ℕ} {D : GermanInflectionalDLM}
    {data : TrainingExperience m TriphoneCount Word2VecGermanDim}
    {q : FrequencyVector m}
    (hD : D.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {suffixIdx : Fin TriphoneCount} {w : GermanWord2VecVec →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.meanings i) = data.forms i suffixIdx)
    {i k : Fin m} (hik : data.forms i suffixIdx < data.forms k suffixIdx) :
    semSup D (data.meanings i) suffixIdx < semSup D (data.meanings k) suffixIdx := by
  rw [hD.semSup_eq_of_decodable hq hw i, hD.semSup_eq_of_decodable hq hw k]
  exact hik

end Saito2025
