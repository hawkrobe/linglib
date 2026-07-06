import Linglib.Processing.Lexical.Discriminative.Defs
import Linglib.Processing.Lexical.Discriminative.Measures
import Linglib.Processing.Lexical.Discriminative.Normed

/-!
# Gahl & Baayen (2024): English homophone duration via DLM
[gahl-baayen-2024] [baayen-2019]
[heitmeier-chuang-baayen-2026]

Gahl, S., & Baayen, R. H. (2024). Time and thyme again: Connecting
English spoken word duration to models of the mental lexicon.
*Language* 100(4), 623–670.

## Empirical claims

The paper reanalyses the Switchboard-corpus homophone-duration data
of Gahl 2008 (409 English homophone pairs such as *time* / *thyme*,
*side* / *sighed*) and asks whether a discriminative-lexicon (DL) model
without stored words can recover the homophone duration effect — long
attributed to lexical *frequency*. The headline findings:

1. **Form-meaning isomorphism predicts homophone duration differences.**
   The duration of a homophone correlates with how strongly its
   meaning supports its form (paper §5.2 Table 4). The semantic
   support measure outperforms lexical frequency in a Gaussian
   location-scale GAMM (DL-based AIC −239.13 vs. localist AIC −231.69;
   evidence ratio 41.26 in paper Table 5).
2. **Homophone semantic similarity predicts duration similarity.**
   Pearson correlation of homophone-pair semantic vectors is a
   significant predictor of how close their durations are (paper §5.2
   Table 4). Semantically similar homophones are produced more
   similarly, consistent with the DL prediction that meaning →
   form mappings vary continuously with the meaning input.
3. **Contextual independence (CIND) outperforms frequency.**
   A novel measure derived from a word-to-word matrix `W` (satisfying
   `UW = U` for utterance multi-hot matrix `U`) captures how much a
   word's meaning can be inferred independently of its utterance
   context. Replacing lemma frequency with CIND consistently improves
   model fit (paper §5.3 Table 5).

The substantive theoretical move: **lexical frequency is composite,
not primitive**. The "frequency effect" on duration decomposes into
(a) `practice`/learning (operationalised via Frequency-Informed
Learning of the mapping `G`), (b) `contextual independence` (CIND),
and (c) `semantic support for form` (SemSupForm). A model **without
stored lexical entries** can recover the duration patterns previously
attributed to frequency.

## Substrate (this file)

This is the **fourth** consumer of the `LinearDiscriminativeLexicon`
substrate (`Processing/Lexical/Discriminative/Defs.lean`),
after `ChuangEtAl2026`, `LuChuangBaayen2026`, and `Saito2025`. It is
also the **second** consumer of the `semSup` family (after Saito
2025), the consumer that triggered the `semSup`/`semSupWord` lift
to `Measures.lean`.

Carrier instantiation: 5,600-dim binary triphone vectors × 200-dim
fastText English embeddings (paper §3.4, appendix §A2). The substrate
is dimension-polymorphic; only the dimensions and the empirical
training data differ from Saito's German setup.

## Substrate generality validated (cumulative table)

| Axis              | Chuang 2026   | Lu 2026       | Saito 2025      | **Gahl-B 2024**          |
|-------------------|---------------|---------------|-----------------|--------------------------|
| Language          | Mandarin      | Mandarin      | German          | **English**              |
| Modality          | f0 pitch      | f0 pitch      | EMA tongue pos. | **acoustic duration**    |
| Form rep          | 50-dim ℝ      | 100-dim ℝ     | 14,404-dim binary| **5,600-dim binary**    |
| Meaning rep       | 768-dim CKIP  | 768-dim CKIP  | 300-dim word2vec| **200-dim fastText**     |
| Phenomenon        | tonal realiz. | tone sandhi   | morpho-phonetics| **homophone duration**   |
| Headline measure  | word smooth   | sense smooth  | semSupSuffix    | **semSupForm + CIND**    |

Same `LinearDiscriminativeLexicon ℝ FormVec MeaningVec` accommodates
all four with carrier-type instantiation only — no specialisation.

## Cross-paper convergence

The four DLM Studies share a common architectural commitment that
this file makes especially explicit: **the seemingly pretheoretical
construct "lexical frequency" decomposes into separable distributional
facts** (paper §1.1, §6.4). Three of the four (Chuang, Lu, Saito) make
this point implicitly by demonstrating word-or-meaning predictors
that subsume frequency effects; Gahl & Baayen 2024 makes it the
explicit headline. Lu's tone sandhi and Saito's morphological-boundary
effects are both special cases of this composite-frequency story.

## Cross-framework note: localist (WEAVER, Dell) vs DL

The paper directly compares DL-based GAMMs to GAMMs grounded in
**localist** lexical models (Dell 1986, Levelt-Roelofs-Meyer 1999)
where frequency is a property of stored lexical entries. linglib does
not currently formalize WEAVER or Dell-style spreading-activation
substrates; the cross-framework discrimination lives in this file's
prose (§5 below). When a `Processing/Lexical/WEAVER/` sibling
lands, the localist–DL comparison can become a Lean-stateable
contrast theorem.

## Sections

- §1 Substrate instantiation (English DLM at 5600/200 dimensions)
- §2 Paper-specific alias for word-level semantic support
- §3 Lipschitz application: similar homophone meanings ⇒ similar predicted forms
- §4 Empirical content (prose; includes CIND and HomophoneSemSim)
-/

namespace GahlBaayen2024

open Processing.Lexical.Discriminative

-- ============================================================================
-- §1: Substrate instantiation — English DLM
-- ============================================================================

/-- Number of triphones in the paper's CELEX-derived word-by-triphone
    matrix `C` (paper appendix §A2: matrix `C` of shape `10,636 × 5,600`).
    Form vectors are zero/one binary indicators of triphone presence. -/
abbrev EnglishTriphoneCount : ℕ := 5600

/-- Dimensionality of the pretrained fastText English embeddings
    (paper appendix §A2: matrix `S` of shape `10,636 × 200`; the
    embeddings are the tweet-based fastText vectors cited in the
    paper). -/
abbrev FastTextEnglishDim : ℕ := 200

/-- A form vector for the English DLM. The "binary" structure is data,
    not type — `FormVec` is `Fin n → ℝ`. -/
abbrev EnglishTriphoneVec : Type := FormVec EnglishTriphoneCount

/-- A semantic vector: 200-dim fastText embedding of word meaning. -/
abbrev EnglishFastTextVec : Type := MeaningVec FastTextEnglishDim

/-- The paper's specific DLM instantiation. -/
abbrev EnglishHomophoneDLM : Type :=
  LinearDiscriminativeLexicon ℝ EnglishTriphoneVec EnglishFastTextVec

-- ============================================================================
-- §2: Paper-specific alias for word-level semantic support
-- ============================================================================

/-- **Semantic Support for Form** (paper §3.4 eq. 10): the total
    support a word's meaning provides to its constituent triphones,
    `Σ_{j ∈ word} (D.production s) j`. The paper's name for the
    `semSupWord` measure (now in
    `Processing/Lexical/Discriminative/Measures.lean`); here
    as an `abbrev` re-exporting under the paper-specific name.

    Two other paper-specific measures (`CIND` for contextual
    independence, `HomophoneSemSim` for Pearson correlation of
    homophone-pair semantic vectors) are defined in the paper but
    not formalised as Lean defs in this file. CIND requires
    formalising the word-to-word matrix `W` satisfying `UW = U`
    (paper §3.2 eq. 9 — substantial substrate work). HomophoneSemSim
    requires inner-product / Pearson machinery on `MeaningVec`
    (deferred to a future `Measures/InnerProduct.lean` sibling).
    Both measures are recorded in §4 prose. -/
noncomputable abbrev semSupForm (D : EnglishHomophoneDLM)
    (s : EnglishFastTextVec) (triphones : List (Fin EnglishTriphoneCount)) : ℝ :=
  semSupWord D s triphones

-- ============================================================================
-- §3: Lipschitz application — similar homophones ⇒ similar form vectors
-- ============================================================================

/-- **Quantitative form of the homophone-similarity → duration-similarity
    prediction** (paper §3.4, §5.2). The paper reports that homophone
    pairs with high `homophoneSemSim` (semantically similar meanings)
    have more similar durations.

    Structurally, this follows from the Lipschitz continuity of the
    production map: if two semantic vectors are close, their predicted
    form vectors are close, which (given that triphone presences feed
    duration estimation) implies close predicted durations.

    Direct application of `dlm_neighbor_centroids_imply_neighbor_contours`
    to the English homophone DLM. The fourth consumer of this Lipschitz
    theorem (after Chuang, Lu, Saito), validating it as DLM-substrate-
    canonical. -/
theorem homophone_similarity_implies_form_similarity
    (D : EnglishHomophoneDLM) (s₁ s₂ : EnglishFastTextVec) {ε : ℝ}
    (h : ‖s₁ - s₂‖ ≤ ε) :
    ‖D.production s₁ - D.production s₂‖ ≤
      ‖D.production.toContinuousLinearMap‖ * ε :=
  dlm_neighbor_centroids_imply_neighbor_contours D h

-- ============================================================================
-- §4: Empirical content (prose)
-- ============================================================================

/-! ### Findings as paper-supplied empirical facts

Per `CLAUDE.md` (Processing-scope guidance), specific GAMM fits, AIC
deltas, and random forest variable-importance scores are out of scope
as Lean theorems. They are recorded here as documented findings.

**DL-based GAMM outperforms localist GAMM** (paper §5.2 / §5.3,
Tables 3-5). Three Gaussian-location-scale GAMMs fitted to log-duration
of 409 Switchboard homophones:

- Localist (predictors: lemma frequency, relative frequency,
  phonological neighbourhood density, +controls): AIC = −231.69.
- DL with frequency-informed-learning (FIL) semSupForm + CIND
  +HomophoneSemSim +controls: AIC = −239.13. **Best DL model**:
  endstate-learning semSupForm + CIND + ortho consistency → AIC =
  −244.77 (evidence ratio 692.29 vs. localist baseline; paper Table 5).

**SemSupForm with endstate learning is the strongest predictor**
(paper §5.4, Fig. 5). Random Forest variable importance ranks
`LogSemanticSupportFormEOL` highest, ahead of phonological neighbourhood
density, orthographic regularity, lemma frequency, and CIND. The
endstate-learning variant is preferred for variable-importance
analysis because it is uncorrelated with frequency (r ≈ −0.38, vs
r = +0.61 for the FIL variant).

**Homophones do NOT sound identical** (paper §6.1, §1.3 — confirmed
contra prior reanalyses claiming the effect is artefactual).
Confirmed: the duration of *time* differs from the duration of
*thyme* even when speaker, phonetic-segment baseline, prosodic
position, and noun-bias are controlled for. The DL model explains
this *via* meaning: identical triphone vectors but different semantic
vectors → different predicted form vectors via `D.production` →
different duration estimates.

**Frequency is composite** (paper §1.1, §6.4 — the headline
theoretical claim). The DL predictors `practice` (FIL),
`contextual independence` (CIND), and `semantic support for form`
(SemSupForm) jointly capture what was previously bundled under
"frequency". The "frequency effect" decomposes; no stored lexical
entry need carry a frequency property.

### Implications recorded in the paper's discussion

- **Anti-lexical-storage** (paper §6.1, §6.2 contra
  [levelt-roelofs-meyer-1999] and the Dell-style spreading-
  activation lineage): frequency effects on duration emerge from a
  model *without* stored words. The DL model has only the matrices
  `C`, `S`, and the trained mappings `G`, `F`, `W` — no lexical
  entries bearing frequency annotations.
- **Form-meaning isomorphism** (paper §6.3, §6.4): the linear mapping
  `G : S → C` predicts considerable structural alignment between the
  semantic and form spaces — a generalisation of sound-symbolism /
  iconicity beyond onomatopoeia and ideophones. Quantitatively
  validated by the homophone-similarity → duration-similarity
  prediction (§3 above).
- **Contextual independence as cognitive measure** (paper §3.2,
  §6.4): CIND captures how much a word's meaning can be learned
  *without* its co-occurring contexts, and is correlated with
  visual lexical decision times (paper appendix §A5.1, validated
  against the British Lexicon Project).
- **Convergence with [saito-tomaschek-baayen-2025]**: both
  papers find that DL-derived semantic-support measures replace
  categorical morphological / lexical predictors with smaller AIC
  values and (in Saito) fewer effective degrees of freedom. The
  composite-frequency thesis of paper §6.4 receives independent
  support from the German morpho-phonetics data of Saito 2025. -/

end GahlBaayen2024
