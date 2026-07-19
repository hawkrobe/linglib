import Linglib.Processing.Lexical.Discriminative.Defs
import Linglib.Processing.Lexical.Discriminative.Normed


/-!
# Chuang, Bell, Tseng & Baayen (2026): Word-specific tonal realizations in Mandarin
[chuang-bell-tseng-baayen-2026] [baayen-2019] [heitmeier-chuang-baayen-2026]

Chuang, Y.-Y., Bell, M. J., Tseng, Y.-H., & Baayen, R. H. (2026).
Word-specific tonal realizations in Mandarin. *Language*, in press.
DOI 10.1017/S0097850725000001.

## Empirical claims (the four predictions)

The paper investigates Mandarin disyllabic words with the rise-fall (RF)
tonal pattern (T2 followed by T4) in spontaneous Taiwan Mandarin speech
(3,778 tokens across 51 word types from the Taiwan Mandarin Spontaneous
Speech Corpus). Standard accounts attribute variation in tonal
realisation to (i) lexical tone, (ii) voluntary intonation/focus, and
(iii) involuntary articulatory constraints (coarticulation, speech
rate, segmental makeup). The paper adds a fourth source — **word
meaning itself** — and derives four testable predictions:

1. **Word type predicts f0 above segmental controls.** A by-word factor
   smooth in a generalised additive model (GAM) of f0 contour reduces
   AIC more than the joint contribution of all segment-related controls
   (vowel height × 2 syllables, onset type × 2, rhyme structure × 2).
2. **Sense further refines word.** Replacing the word-level factor
   smooth with a sense-level smooth further improves model fit on the
   subset of senses with sufficient tokens.
3. **f0 → meaning predictability.** A linear (or near-linear) mapping
   from token-level pitch contours to token-level contextualised
   embeddings achieves above-chance comprehension accuracy.
4. **meaning → f0 predictability.** A reverse mapping from contextualised
   embeddings to pitch contours achieves above-chance production
   accuracy.

The substantive theoretical claim is that **word meaning is a
co-determiner of phonetic realization** — equivalently, that the form
space of pitch contours and the meaning space of contextualised
embeddings exhibit quantifiable **isomorphism** (predictions 3 and 4),
contradicting the dual-articulation axiom that form and meaning are
orthogonal modules of grammar.

## Substrate

The DLM substrate (`LinearDiscriminativeLexicon`, `FormVec`, `MeaningVec`,
`broadcast`, `LinearDiscriminativeLexicon.sub_mem_ker_iff`)
lives in `Processing/Lexical/Discriminative/Defs.lean`
[baayen-2019] [heitmeier-chuang-baayen-2026]. This file
imports it and supplies the paper-specific instantiation: 50-dim pitch
contours and 768-dim CKIP GPT-2 contextualised embeddings.

The DLM's defining architectural commitment is that the lexicon is not
an inventory of stored, decomposed form-meaning entries — the trained
connection weights of the comprehension and production maps carry all
form-meaning knowledge. The substrate `structure` has exactly two
fields, both `LinearMap`s; there is no `entries`-typed projection.
This is the substantive reason the DLM is housed under
`Processing/Lexical/` rather than `Theories/Lexicon/` — see
the substrate file's docstring.

## Relation to existing usage-based / frequency-channel theories

The DLM is the latest in a lineage of usage-based, gradient-weight
theories. Adjacent linglib substrate:

- Four rival theories of token frequency in the grammar — UseListed
  ([zuraw-2000]), indexed constraints ([pater-2010]), representational
  strength ([moore-cantwell-2021]), and scaled weights
  ([coetzee-pater-2008]), adjudicated in
  `Studies/BreissKatsudaKawahara2026.lean` (§5). All four presuppose a
  stored lexicon to which frequency attaches.
- `Studies/Bybee1985.lean` ([bybee-1985]):
  Bybee's dynamic network — typed `LexicalEntry`s with `tokenFreq`
  strength + connection edges. Stores entries.

The DLM is the natural extreme of these traditions: it rejects the
storage premise altogether — no `LexicalEntry`, no `tokenFreq`, no
entry-typed connections. The architectural divergence is sharpest
against Bybee (both usage-based, only one stores entries) and is
documented in the substrate file's docstring. The four frequency
theories and Bybee's network are linguistic-level theories
parameterised by lexical-frequency, not theories of "the lexicon as
its own object" — the DLM is the tradition's extreme that rejects the
storage premise the others share.

## Architectural note: tones as emergent vs stored

The discrete-tone substrate in `Phonology/Tone/Constraints.lean`,
`Studies/Hyman2006.lean` ([hyman-2006]),
`Studies/Lionnet2025.lean` ([lionnet-2025]), and
`Studies/AkinboFwangwar2026.lean`
([akinbo-fwangwar-2026]) treats tonal categories (H/M/L; T1–T4)
as primitive featural objects with faithfulness/markedness violations
defined over them. The present study adopts the **opposite** stance:
tonal categories are statistical generalisations across token-level
pitch contours, not stored cognitive objects.

This file's claims live on continuous f0 vectors (`PitchContour` below),
deliberately *not* on `Autosegmental.FloatingForm`. The two
substrates coexist as competing analyses of overlapping data; this file
does not bridge them. The decision is methodological: bridging would
require committing to a translation between continuous contours and
discrete tonal categories that is itself the empirical question the
paper interrogates.

## Cross-framework note: vs. Storme 2026 *HOMOPHONY

`Storme2026.starHomophony` ([storme-2026],
`Studies/Storme2026.lean`) formalises a **systemic**
constraint that penalises output tuples in which distinct inputs
produce identical surface forms. It operates on **segmental** form and
predicts **categorical** distinct-meaning–distinct-form pressure.

The DLM-based account here predicts **graded** distinct-meaning–
distinct-form pressure operating on **fine phonetic detail** (here, f0
contours). Even nominally homophonous Mandarin disyllables (e.g.
*cheng2shi4* 'city' vs. *cheng2shi4* 'computer program', paper §2.1)
have measurably distinct pitch contours.

The two formalisations are sibling responses to homophony pressure at
different levels of phonological/phonetic resolution. Their structural
common generalisation is **injectivity of the meaning→form map**:
Storme's `*HOMOPHONY` enforces it categorically over a discrete
output paradigm; the Discriminative Lexicon substrate expresses it via
the kernel characterisation `sub_mem_ker_iff` (distinct meanings
surface distinctly exactly when their difference avoids
`ker production`). A formal
subsumption result would require a substrate that admits both
discrete-segmental and continuous-sub-segmental representations of
"the same" lexical item; linglib does not currently provide one.

## Sections

- Paper-specific instantiation: Taiwan Mandarin RF disyllables
- Quantitative form of prediction (iv) via Lipschitz continuity
- Empirical content (the four predictions, in prose)
-/

namespace ChuangEtAl2026


open Processing.Lexical.Discriminative

/-! ### Paper-specific instantiation — Taiwan Mandarin RF disyllables -/

/-- The paper uses 50 evenly-spaced f0 samples per token (paper §3.2). -/
abbrev TaiwanMandarinPitchSampleCount : ℕ := 50

/-- The paper uses 768-dimensional CKIP GPT-2 contextualised embeddings
    (paper §3.1). -/
abbrev CKIPGPT2HiddenDim : ℕ := 768

/-- A pitch contour: 50 f0 samples on the normalised time scale [0, 1],
    centred and scaled per token (paper §3.2 min-max normalisation),
    representing pitch **shape** rather than absolute pitch or amplitude. -/
abbrev PitchContour : Type := FormVec TaiwanMandarinPitchSampleCount

/-- A contextualised embedding: a 768-dim vector from CKIP GPT-2
    conditioned on the token's preceding utterance (paper §3.1).
    Distinct tokens of the same word type carry distinct CEs reflecting
    their context-specific meanings. -/
abbrev ContextualEmbedding : Type := MeaningVec CKIPGPT2HiddenDim

/-- The paper's specific DLM instantiation for Taiwan Mandarin RF tones. -/
abbrev TaiwanMandarinRFDLM : Type :=
  LinearDiscriminativeLexicon ℝ PitchContour ContextualEmbedding

/-! ### Quantitative form of prediction (iv) via Lipschitz continuity -/

/-- **Quantitative form of prediction (iv).** Paper §3.4 reports that
    the trained DLM production net maps similar CEs to similar contours
    above chance. The Lipschitz form: any `TaiwanMandarinRFDLM` satisfies
    `‖production e₁ - production e₂‖ ≤ ‖production‖ * ‖e₁ - e₂‖`. The
    paper's empirical content is that the trained `‖production‖` is
    moderate, making this bound informative for the homograph pair
    *cheng2shi4* 'city' vs. *cheng2shi4* 'computer program' (paper
    §2.1) — similar context-specific embeddings yield similar but
    *measurably distinct* pitch contours.

    Direct application of `dlm_neighbor_centroids_imply_neighbor_contours`
    to the paper-specific carrier types. -/
theorem dlm_close_meanings_imply_close_contours
    (D : TaiwanMandarinRFDLM) (e₁ e₂ : ContextualEmbedding) {ε : ℝ}
    (h : ‖e₁ - e₂‖ ≤ ε) :
    ‖D.production e₁ - D.production e₂‖ ≤
      ‖D.production.toContinuousLinearMap‖ * ε :=
  dlm_neighbor_centroids_imply_neighbor_contours D h

/-! ### The four predictions as paper-supplied empirical facts

Per `CLAUDE.md` (Processing-scope guidance), measurement modalities and
empirical-fit tables are out of scope as Lean theorems. The four
predictions are recorded here as documented empirical findings — not
as Lean-derivable theorems — since their content is the paper's GAM
and DLM training results, not a structural property of the substrate.

**Prediction (i)** — paper §2.6.2, Fig. 4, Fig. 6. The GAM with a
by-word factor smooth has cross-validated SSE strictly less than the
GAM with all six segmental factor smooths combined (vowel1, vowel2,
onset1, onset2, syllable1, syllable2). Reported AIC reduction
relative to baseline: −6,795 (word) vs. −4,938 (omnibus segmental).

**Prediction (ii)** — paper §2.7.1, Fig. 10, Fig. 12. On the
restricted dataset where senses have ≥ 14 tokens (3,458 tokens,
65 senses across 48 word types), the GAM with a sense factor smooth
reduces AIC by an additional 365 units relative to the word-smooth
GAM. Polysemous words such as *bu2yao4* (4 senses: 'prohibition',
'dissuasion', 'unnecessity', 'wish-against'; Fig. 11) have visibly
distinct sense-specific contours.

**Prediction (iii)** — paper §3.3, Fig. 16. A DLM comprehension net
trained on (pitch contour → CE) pairs achieves test accuracy ~30%
(LDL) and ~50% (ResLDL), where "accuracy" means the predicted CE's
nearest neighbour belongs to a token of the same word type.
Permutation chance baseline: ~3.5% over the 51-word vocabulary.

**Prediction (iv)** — paper §3.4, Fig. 17. A DLM production net
trained on (CE → pitch contour) pairs achieves test accuracy ~35–40%
for both LDL and ResLDL. Notable: linear and nonlinear models perform
similarly here, suggesting the meaning → form mapping is dominantly
linear. The qualitative match between the LDL-predicted contour from
word-centroid CEs and the GAM-predicted contour from word-factor
smooths (Fig. 18) is the paper's headline form-meaning isomorphism
finding.

### Implications recorded in the paper's discussion

- **Anti-stored-tone-representation** (paper §4): tones are emergent
  statistical generalisations, not discrete cognitive objects. The
  substantive challenge to the discrete-tone substrate noted in the
  module docstring's *Architectural note*.
- **Anti-dual-articulation** (paper §4): form and meaning are not
  orthogonal levels of grammar; their isomorphism is quantifiable and
  predictively useful in both comprehension and production.
- **Contextualism about meaning** (paper §1, §3.1): word meaning is a
  property of the token in context, not a context-independent symbol
  shared by all tokens of a type. Operationalised by contextualised
  rather than type-level embeddings. -/

end ChuangEtAl2026
