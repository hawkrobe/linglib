module

public import Linglib.Processing.DiscriminativeLexicon.Defs
public import Linglib.Processing.DiscriminativeLexicon.Normed
public import Linglib.Processing.DiscriminativeLexicon.Training

/-!
# Saito, Tomaschek & Baayen (2025): Interaction of Frequency and Inflectional Status

This file formalizes the paper's discriminative-lexicon account of a frequency effect that
reverses with inflectional status. In tongue-position data from the Karl Eberhards Corpus of
spontaneous southern German, high-frequency non-inflected words show articulatory reduction
of the stem vowel while high-frequency inflected words do not, and the paper replaces the
binary inflectional-status predictor by the semantic support that a word's meaning lends to
its suffix triphone in a trained discriminative lexicon, which improves the tongue-position
model with one fewer degree of freedom. The model is the substrate's linear discriminative
lexicon over the paper's triphone form vectors and word2vec meaning vectors
(`GermanInflectionalDLM`); close meanings yield close predicted articulations
(`close_meanings_imply_close_form`), and when the suffix triphone is linearly decodable from
meanings, training alone gives inflected words strictly greater suffix support than
non-inflected ones, the direction of the paper's contrast (`production_suffix_lt`). The
result bears on production models with a morpheme layer such as WEAVER++
([levelt-roelofs-meyer-1999], [roelofs-1997]), since the apparent morphological-boundary
effect is carried by inflectional semantics.

## Implementation notes

The paper's positional measures, the semantic support for the vowel and suffix triphones, are
the predicted form `D.production s` at the two triphone indices, the substrate's
`semanticSupport` at a coordinate indicator; the paper's triphone indexing is not reproduced. Its
production matrix, solving `SG = C`, is the substrate's `production`, and its comprehension
matrix, solving `CF = S`, is `comprehension`. The generalized additive models of the
articulatory study are not formalized.

## References

* [saito-tomaschek-baayen-2025]
* [baayen-2019]
* [heitmeier-chuang-baayen-2026]
* [levelt-roelofs-meyer-1999]
* [roelofs-1997]
* [muller-2015]
-/

@[expose] public section

namespace Saito2025

open DiscriminativeLexicon

/-- The paper's CELEX-derived form matrix has `TriphoneCount` triphones. -/
abbrev TriphoneCount : ℕ := 14404

/-- The pretrained German word2vec embeddings of [muller-2015] have `Word2VecGermanDim`
dimensions. -/
abbrev Word2VecGermanDim : ℕ := 300

/-- A triphone vector is a form vector over the paper's triphones; that its entries are zero or
one is a property of the training data, not of the type. -/
abbrev TriphoneVec := FormVec TriphoneCount

/-- A German word2vec vector is a meaning vector of the embeddings' dimension. -/
abbrev GermanWord2VecVec := MeaningVec Word2VecGermanDim

/-- The paper's discriminative lexicon is the linear model over German triphone form vectors
and word2vec meaning vectors. -/
abbrev GermanInflectionalDLM :=
  Linear ℝ TriphoneVec GermanWord2VecVec

/-- Close meanings yield close predicted articulations, with the production map's norm as
the constant. -/
theorem close_meanings_imply_close_form
    (D : GermanInflectionalDLM) (s₁ s₂ : GermanWord2VecVec) {ε : ℝ}
    (h : ‖s₁ - s₂‖ ≤ ε) :
    ‖D.production s₁ - D.production s₂‖ ≤
      ‖D.production.toContinuousLinearMap‖ * ε :=
  D.norm_production_sub_le h

/-- When the suffix-triphone coordinate is linearly decodable from word meanings, the
inflectional semantics the paper ties to the suffix, a trained lexicon's `SemSupSuffix`
reproduces it exactly, so a word carrying the suffix triphone gets strictly greater suffix
support than one lacking it, which is the direction of the paper's contrast between inflected
and non-inflected words, obtained from the linear architecture alone. -/
theorem production_suffix_lt
    {m : ℕ} {D : GermanInflectionalDLM}
    {data : TrainingExperience m TriphoneCount Word2VecGermanDim}
    {q : FrequencyVector m}
    (hD : D.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {suffixIdx : Fin TriphoneCount} {w : GermanWord2VecVec →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.S i) = data.C i suffixIdx)
    {i k : Fin m} (hik : data.C i suffixIdx < data.C k suffixIdx) :
    D.production (data.S i) suffixIdx < D.production (data.S k) suffixIdx := by
  rw [hD.production_apply_eq_of_decodable hq hw i, hD.production_apply_eq_of_decodable hq hw k]
  exact hik

end Saito2025
