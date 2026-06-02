import Linglib.Processing.Lexical.Discriminative.Defs
import Linglib.Processing.Lexical.Discriminative.Measures
import Linglib.Processing.Lexical.Discriminative.Normed

/-!
# Saito, Tomaschek & Baayen (2025): Frequency × inflectional status via DLM
[saito-tomaschek-baayen-2025] [baayen-2019]
[heitmeier-chuang-baayen-2026]

Saito, M., Tomaschek, F., & Baayen, R. H. (2025). Interaction of
frequency and inflectional status: An approach from discriminative
learning. Preprint v1.

## Empirical claims

The paper investigates the apparent contradiction between two
documented frequency effects on phonetic realization:

- **Phonetic reduction**: high-frequency words have shorter durations,
  more centralized formants, more raised tongue positions
  ([aylett-turk-2004] smooth signal redundancy hypothesis +
  several earlier corpus and ultrasound studies cited in paper §1).
- **Phonetic enhancement**: high-frequency morphologically *complex*
  words show longer/clearer realizations (paradigmatic enhancement
  literature, paper §1).

The study reanalyses German tongue position data (560 word tokens,
88 word types containing the rhyme `[a(:)…t]` from the Karl-Eberhard
Corpus of spontaneous southern German) and finds:

1. **Inflectional status × frequency interaction**: high-frequency
   *non-inflected* words show tongue raising (reduction); high-
   frequency *inflected* words show attenuated reduction (paper §2.2,
   Tables 1–2).
2. **DLM-derived semantic support replaces the binary morphological
   predictor**: replacing the categorical `InflStatus` factor with the
   continuous `SemSupSuffix` measure (semantic support from word
   meaning to the suffix triphone, derived from the trained DLM)
   improves model fit by 142.87 AIC units (paper §3.3, Table 3).
3. **Architectural challenge to WEAVER++**: the result undermines
   speech production models that posit intermediate symbolic
   morphological representations ([levelt-roelofs-meyer-1999]
   and the Roelofs WEAVER lineage). Form ↔ meaning mappings without
   a morpheme layer suffice.

The substantive theoretical move: **what looks like a morphological-
boundary effect is driven by inflectional semantics**.

## Substrate (this file)

This file is the **third** consumer of the
`LinearDiscriminativeLexicon` substrate
(`Processing/Lexical/Discriminative/Defs.lean`), after
[chuang-bell-tseng-baayen-2026] and [lu-chuang-baayen-2026].
It validates the polymorphic carrier typing across **every** axis of
variation:

| Axis              | Chuang 2026   | Lu 2026       | **Saito 2025**         |
|-------------------|---------------|---------------|------------------------|
| Language          | Mandarin      | Mandarin      | **German**             |
| Modality          | f0 pitch      | f0 pitch      | **EMA tongue position**|
| Form rep          | 50-dim ℝ      | 100-dim ℝ     | **14,404-dim binary**  |
| Meaning rep       | 768-dim CKIP  | 768-dim CKIP  | **300-dim word2vec**   |
| Phenomenon        | tonal realiz. | tone sandhi   | **morpho-phonetics**   |

The same `LinearDiscriminativeLexicon ℝ FormVec MeaningVec` instantiates
to all three. The "binary" structure of form vectors here (zero/one
triphone presence) is a property of the **training data** the network
sees, not of the type — `Fin 14404 → ℝ` accommodates {0,1}-valued
sequences as a special case.

## SemSup measures (substrate)

The paper introduces a family of derived measures (paper §3.1) on top
of a trained DLM: `SemSup`, `SemSupVowel`, `SemSupSuffix`, `SemSupWord`,
`PredAcc`, `FuncLoad`, `SemLen`, `UncertProd`, `UncertComp`. The first
four are paper-headline; the rest are diagnostic.

The general measures (`semSup`, `semSupWord`) plus their linearity
lemmas live in `Processing/Lexical/Discriminative/Measures.lean`,
having graduated to substrate when [gahl-baayen-2024] landed as a
second consumer. The paper-specific positional variants
(`semSupVowel`, `semSupSuffix`) stay here as `abbrev`s wrapping the
substrate primitive.

## Cross-framework note: WEAVER++ challenged but unformalized

The paper's headline architectural claim — that no intermediate
morpheme layer is needed between semantics and articulation — directly
challenges WEAVER++ ([levelt-roelofs-meyer-1999] and the broader
WEAVER lineage). linglib does not currently formalize WEAVER++; the
cross-framework discrimination would require a
`Processing/Lexical/WEAVER/` sibling that explicitly posits a
lemma layer. Defer until a second WEAVER-using study lands.

## Sibling-framework engagement

Like the Chuang and Lu DLM Studies, this file's claims sit in tension
with the **stored-lexicon** assumptions in:
- `Phonology/ItemSpecificity/{UseListed, IndexedConstraints,
  RepresentationStrength, ScaledWeights}.lean` — four phonological
  frequency-channel theories, all of which posit stored entries to
  attach frequency to. Saito's frequency × inflectional-status
  interaction is *the* phenomenon those channels would compete to
  explain; the DLM offers a 5th, no-stored-entries account.
- `Morphology/UsageBased/Network.lean` ([bybee-1985]):
  Bybee's `tokenFreq : Nat` is the canonical stored-frequency primitive;
  the DLM's `production` linear map dispenses with it.

`Studies/BreissKatsudaKawahara2026.lean` is the
closest sibling phenomenon — Japanese morpho-phonetics with explicit
discrimination among the four `ItemSpecificity` channels. Saito's
DLM analysis would form a natural 5th line in that paper's
discrimination table; the structural cross-framework theorem is
deferred until a unified `LexiconArchitecture` typeclass exists (per
the cross-framework reconciler's recommendation, see CHANGELOG 0.231.15).

## Sections

- §1 Substrate instantiation (German DLM at 14404/300 dimensions)
- §2 Paper-specific semSup aliases (vowel/suffix variants)
- §3 Lipschitz application to articulation
- §4 Empirical content (prose)
-/

namespace Saito2025

open Processing.Lexical.Discriminative

-- ============================================================================
-- §1: Substrate instantiation — German DLM
-- ============================================================================

/-- The full set of triphones in the paper's CELEX-derived word-by-
    triphone matrix (paper §3.1: matrix `C` of shape `64068 × 14404`).
    Form vectors are zero/one binary indicators of triphone presence. -/
abbrev TriphoneCount : ℕ := 14404

/-- The dimensionality of the pretrained word2vec German embeddings
    (paper §3.1: matrix `S` of shape `64068 × 300`; paper cites the
    German word2vec model of Müller 2015 — bib entry omitted). -/
abbrev Word2VecGermanDim : ℕ := 300

/-- A form vector: zero/one indicator of which triphones the word
    contains. The "binary" structure is data, not type — `FormVec`
    is `Fin n → ℝ` and binary vectors are a subset. -/
abbrev TriphoneVec : Type := FormVec TriphoneCount

/-- A semantic vector: 300-dim word2vec embedding of word meaning. -/
abbrev GermanWord2VecVec : Type := MeaningVec Word2VecGermanDim

/-- The paper's specific DLM instantiation. The substrate type
    `LinearDiscriminativeLexicon` is in
    `Processing/Lexical/Discriminative/Defs.lean`; this
    abbreviation specialises it to the German triphone × word2vec
    dimensions. -/
abbrev GermanInflectionalDLM : Type :=
  LinearDiscriminativeLexicon ℝ TriphoneVec GermanWord2VecVec

-- ============================================================================
-- §2: Paper-specific semantic-support aliases
-- ============================================================================

/-! ### SemSupVowel and SemSupSuffix (paper §3.1 eq. 3, 4)

The general measures `semSup` and `semSupWord` (with linearity lemmas)
live in `Processing/Lexical/Discriminative/Measures.lean`.
The two positional variants below are paper-specific bindings naming
which triphone index is being projected. `abbrev` for transparency
(`simp` / `rw` see through to `semSup`). -/

/-- **SemSupVowel** (paper §3.1 eq. 3): semantic support for the
    triphone centred on the word's stem vowel. -/
abbrev semSupVowel (D : GermanInflectionalDLM)
    (s : GermanWord2VecVec) (vowelTriphoneIdx : Fin TriphoneCount) : ℝ :=
  semSup D s vowelTriphoneIdx

/-- **SemSupSuffix** (paper §3.1 eq. 4): semantic support for the
    triphone centred on the suffix exponent (`[t]` in this paper).
    The headline measure of paper §3.2.2: replacing the binary
    inflectional-status factor with `semSupSuffix` improves the
    tongue-position GAMM by 142.87 AIC units. -/
abbrev semSupSuffix (D : GermanInflectionalDLM)
    (s : GermanWord2VecVec) (suffixTriphoneIdx : Fin TriphoneCount) : ℝ :=
  semSup D s suffixTriphoneIdx

-- ============================================================================
-- §3: Lipschitz application — close meanings ⇒ close articulations
-- ============================================================================

/-- **Quantitative form of the DLM's articulation prediction.**
    Paper §3.3 reports that the trained DLM's production map yields
    tongue-position predictions consistent with empirical
    measurements. The Lipschitz form: any `GermanInflectionalDLM`
    sends close-in-meaning word pairs to close-in-form
    triphone-vectors, with constant `‖production‖`.

    This is the third consumer of
    `dlm_neighbor_centroids_imply_neighbor_contours` (after Chuang
    2026 and Lu 2026), validating that the polymorphic substrate
    accommodates German morpho-phonetics with no specialisation
    beyond carrier-type instantiation. -/
theorem saito_close_meanings_imply_close_form
    (D : GermanInflectionalDLM) (s₁ s₂ : GermanWord2VecVec) {ε : ℝ}
    (h : ‖s₁ - s₂‖ ≤ ε) :
    ‖D.production s₁ - D.production s₂‖ ≤
      ‖D.production.toContinuousLinearMap‖ * ε :=
  dlm_neighbor_centroids_imply_neighbor_contours D h

-- ============================================================================
-- §4: Empirical content (prose)
-- ============================================================================

/-! ### Findings as paper-supplied empirical facts

Per `CLAUDE.md` (Processing-scope guidance), specific GAMM fits, AIC
deltas, and Random Forest variable-importance scores are out of scope
as Lean theorems. They are recorded here as documented findings.

**Frequency × inflectional status interaction** (paper §2.2.1, Table 1).
For non-inflected words, higher (log) frequency predicts higher tongue-
tip positions (articulatory reduction). For inflected words this
reduction effect is significantly attenuated (interaction term
`te(Freq, Time):Inflected`: edf=7.51, F=15.83, p<0.001). The same
interaction is observed for tongue-body positions (paper §2.2.2,
Table 2; F=3.29, p=0.020).

**SemSupSuffix is the strongest predictor of inflectional status**
(paper §3.2.1, Fig. 10). In a Random Forest analysis with nine
DLM-derived semantic measures as candidate predictors, `SemSupSuffix`
ranks highest; `SemSupVowel` ranks second; `SemSupWord` ranks fourth
(after `PredAcc`). Inflected words have significantly higher
`SemSupSuffix` (Mann-Whitney U=152,201, p<0.001) and higher
`SemSupWord`; lower `SemSupVowel` (paper §3.2.2, Fig. 11abc).

**SemSupSuffix replaces InflStatus in the GAMM** (paper §3.3, Table 3).
Replacing the binary factor `InflStatus` with the continuous
`SemSupSuffix` measure in the tongue-position GAMM reduces AIC by
142.87 units (62.64 ML score units), with one fewer effective degree
of freedom. The DLM-derived continuous measure is structurally simpler
than the categorical alternative *and* fits the data better.

**Frequency interaction explained by SemSupSuffix** (paper §3.4). The
interaction `te(Time, SemSupSuffix, Freq)` (edf=20.31, F=30.92, p<0.001)
shows that higher `SemSupSuffix` correlates with lowered tongue
positions for high-frequency words (= articulatory enhancement),
while low-`SemSupSuffix` high-frequency words show raising
(= articulatory reduction). The frequency paradox dissolves: both
effects coexist, modulated by semantic support.

### Implications recorded in the paper's discussion

- **No morphological-boundary primitive needed** (paper §4): the
  apparent boundary effect is driven by inflectional semantics —
  `SemSupSuffix` reflects how well a word's meaning supports its
  word-final triphone, which is high for inflected words because
  inflectional meanings are tied to the suffix.
- **Anti-WEAVER++** (paper §4 contra [levelt-roelofs-meyer-1999],
  Roelofs 1997): production models with intermediate symbolic
  morphological layers are not required; direct meaning ↔ form
  mappings via the DLM suffice.
- **Reduction-enhancement composite** (paper §4 conclusion): both
  effects can be expressed within the DLM as `h_{ω,k} * Ĉ_{i,s}` —
  informativity (h) modulates the strength of semantic support (Ĉ) on
  word-final triphones. (See [gahl-baayen-2024] for an analogous
  formulation on word duration.)
- **Cross-modal substrate validation**: the paper's success applying
  DLM to *articulatory* (tongue-tip / tongue-body trajectories)
  rather than acoustic data demonstrates that the form ↔ meaning
  isomorphism finding of the Mandarin tone studies generalises
  beyond pitch — cf. Lu et al. 2026 §5 conjecture that "form-meaning
  isomorphism is not a tone-language quirk". -/

end Saito2025
