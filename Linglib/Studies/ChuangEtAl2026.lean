import Linglib.Processing.DiscriminativeLexicon.Defs
import Linglib.Processing.DiscriminativeLexicon.Normed

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

Per the Processing scope discipline, the GAM/DLM fit results above are empirical
findings recorded in prose, not Lean theorems. The Lean content instantiates the
DLM substrate (`Processing/DiscriminativeLexicon/`, [baayen-2019]
[heitmeier-chuang-baayen-2026]) at the paper's carriers and proves the one
structural claim the paper itself states (fn. 29,
`comprehension_not_surjective`). The substrate supplies the rest:
`Linear.norm_production_sub_le` (the production map's Lipschitz
bound — similar embeddings surface as similar contours) and
`LinearMap.sub_mem_ker_iff` (homophones like *cheng2shi4*
'city' ~ 'computer program' (§2.1) surface distinctly iff their embedding
difference avoids the production kernel).

## Main results

* `PitchContour` / `ContextualEmbedding` / `TaiwanMandarinRFDLM` — the paper's
  carriers: 50-sample min–max-normalized pitch shapes (§3.2) and 768-dim CKIP
  GPT-2 contextualized embeddings (§3.1)
* `comprehension_not_surjective` — fn. 29: a linear map from 50-dimensional
  pitch space cannot reach all of the 768-dimensional embedding space

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

open DiscriminativeLexicon

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

/-- **Fn. 29** (§3.3): "it is impossible to map a lower-dimensional space into a
higher-dimensional space with a linear mapping without losing information" — any
linear comprehension map from 50-sample pitch contours reaches at most a
50-dimensional subspace of the 768-dimensional embedding space, the paper's
ground for finding ResLDL's comprehension advantage over LDL "unsurprising". -/
theorem comprehension_not_surjective (D : TaiwanMandarinRFDLM) :
    ¬ Function.Surjective D.comprehension := fun h => by
  simpa [CKIPGPT2HiddenDim, TaiwanMandarinPitchSampleCount] using
    LinearMap.finrank_le_finrank_of_surjective (f := D.comprehension) h

end ChuangEtAl2026
