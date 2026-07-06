import Linglib.Processing.Lexical.Discriminative.Defs
import Linglib.Processing.Lexical.Discriminative.Normed
import Linglib.Studies.ChuangEtAl2026

/-!
# Lu, Chuang & Baayen (2026): Realization of tones in spontaneous Taiwan Mandarin
[lu-chuang-baayen-2026] [chuang-bell-tseng-baayen-2026]
[baayen-2019] [heitmeier-chuang-baayen-2026]

Lu, Y., Chuang, Y.-Y., & Baayen, R. H. (2026). The realization of tones
in spontaneous spoken Taiwan Mandarin: a corpus-based survey and
theory-driven computational modeling. *Corpus Linguistics and
Linguistic Theory*. DOI 10.1515/cllt-2025-0028.

## Empirical claims

This study **generalises** [chuang-bell-tseng-baayen-2026] from a
single tone pattern (T2-T4 rise-fall) to **all 20 disyllabic tone
patterns** of Taiwan Mandarin, in a 4,283-token / 313-word-type subset
of the Corpus of Spontaneous Taiwan Mandarin (Fon 2004), restricted to
the four most frequent tonal contexts (4.4, 3.4, 4.1, 4.0).

1. **Word effect generalises across all 20 tone patterns.** Withholding
   `word` from the GAMM raises AIC by 7,269.27 to 12,345.54 across the
   four tonal contexts (paper §3.4.1, Fig. 2), far exceeding any other
   predictor. When `word` is included, withholding `tone_pattern`
   raises AIC by only single- or low-double-digit units, reflecting
   near-total subsumption of `tone_pattern` by `word`.
2. **Sense > word.** Replacing the `word` factor smooth with a `sense_type`
   factor smooth further reduces AIC (paper §3.4.2, Table 4),
   replicating [chuang-bell-tseng-baayen-2026] on the broader
   20-pattern dataset.
3. **Form–meaning isomorphism for all 20 tone patterns.** A linear
   meaning→form mapping from CE centroids to fixed-length pitch vectors
   recovers the GAMM-derived gold-standard contours of all 20 tone
   patterns with high cosine similarity (paper §4.4, Fig. 9).
4. **T3 tone sandhi as DLM kernel-neutralization.** The classically
   stipulated "T3 → T2 / __ T3" sandhi rule **does not appear in the
   model**: T3-T3 and T2-T3 word-token CE centroids in Taiwan Mandarin
   differ only by elements that lie in the **kernel of the trained
   production map**, so their surface pitch contours are identical
   ("complete neutralization for Taiwan Mandarin", paper §5; consistent
   with [lu-chuang-baayen-2025]'s corpus measurement showing T3-T3 ≡
   T2-T3 surface in spontaneous Taiwan Mandarin).

The substantive theoretical claim is that **a word-and-paradigm DLM
suffices to predict every disyllabic tone pattern's surface realisation
without any explicit phonological tone-sandhi rule**. The architecture
predicts neutralization where the meaning-space evidence supports it
(Taiwan Mandarin, complete) and underdetermines it where evidence does
not (Standard Chinese, where T3-T2 / T3-T3 distinction "is hardly
visible to the eye" but reportedly incomplete; [lu-chuang-baayen-2026]
§5).

## Substrate

The `LinearDiscriminativeLexicon` substrate
(`Processing/Lexical/Discriminative/Defs.lean`) is **reused
verbatim** — this is the second paper-anchored study consuming it
([chuang-bell-tseng-baayen-2026] is the first). This file
specialises the substrate to:

- **100-dimensional** pitch vectors (vs. Chuang's 50-dim) — paper §4.1;
- the **same 768-dimensional** CKIP GPT-2 embedding space
  (`CKIPGPT2HiddenDim`, reused from `ChuangEtAl2026`);
- a **20-element** `TonePattern20` enum covering all disyllabic
  combinations of T1/T2/T3/T4/T0.

The fact that the same substrate parameterises cleanly to both 50-dim
and 100-dim form vectors validates the dimension-polymorphic carrier
typing of `LinearDiscriminativeLexicon`.

## Cross-framework note: vs. autosegmental T3 sandhi

The classical autosegmental account of Mandarin T3 sandhi
([chen-2000], [duanmu-2007], and the surrounding literature)
posits a structural rule: an underlying `/T3 T3/` sequence undergoes
spreading or delinking, surfacing as `[T2 T3]`. Linglib's existing
discrete-tone substrate (`Phonology/Tone/Constraints.lean`,
`Phonology/Autosegmental/Floating.lean`) is set up to express
such rule-based accounts, although no Mandarin-specific T3-sandhi
fragment has been formalised in linglib to date.

The DLM-side account differs both **architecturally** and
**predictively**:

- **Architecturally**, no rule is invoked. The neutralisation falls out
  of the kernel of the trained meaning→form map. `t3_sandhi_via_kernel`
  below states this as a direct application of the kernel
  characterisation `LinearDiscriminativeLexicon.production_eq_iff`.
- **Predictively**, the DLM accommodates **dialect variation** in
  sandhi completeness without re-stipulating the rule: Taiwan Mandarin's
  complete neutralisation = the kernel-difference holds; Standard
  Chinese's incomplete neutralisation = the difference is small but
  non-zero. The autosegmental account requires either a derivational
  optionality or a different rule per dialect.

The two formalisations are not in head-on conflict; they generate
different predictions on the same data. A formal cross-framework
discrimination experiment would require the discrete-tone substrate
to commit to a Mandarin T3-sandhi fragment, which it currently does
not. Until then, this comparison lives in prose.

## Sections

- Substrate import and paper-specific dimensional instantiation
- The 20 disyllabic tone patterns of Mandarin
- Tone sandhi neutralization as DLM kernel application
- DLM dialect flexibility: same architecture, different kernels
- Empirical content (AIC, accuracies, isomorphism metrics)
-/

namespace LuChuangBaayen2026

open Processing.Lexical.Discriminative
open ChuangEtAl2026

/-! ### Substrate import + paper-specific instantiation -/

/-- The paper uses 100 evenly-spaced f0 samples per token (paper §4.1).
    Distinct from [chuang-bell-tseng-baayen-2026]'s 50; the
    `FormVec` substrate is dimension-polymorphic so both fit. -/
abbrev LuPitchSampleCount : ℕ := 100

/-- Pitch contour at the paper's chosen sampling resolution. -/
abbrev LuPitchContour : Type := FormVec LuPitchSampleCount

/-- The paper's specific DLM instantiation: 100-dim pitch vectors,
    768-dim contextualised embeddings (`CKIPGPT2HiddenDim` reused from
    `ChuangEtAl2026`). The substrate type
    `LinearDiscriminativeLexicon` is in
    `Processing/Lexical/Discriminative/Defs.lean`. -/
abbrev LuTaiwanMandarinDLM : Type :=
  LinearDiscriminativeLexicon ℝ LuPitchContour ContextualEmbedding

/-! ### The 20 disyllabic tone patterns -/

/-- The 20 disyllabic tone patterns of Mandarin (paper Table 1).
    Enumerated as the row-major Cartesian-product list of
    {T1, T2, T3, T4} (full lexical tones) on the first syllable with
    {T1, T2, T3, T4, T0} (full + neutral) on the second.

    The neutral tone (T0) appears only on the second syllable in this
    paradigm; mono-T0 disyllables are not analysed. The structural fact
    20 = 4 × 5 is by enumeration here, not by a typeclass. -/
inductive TonePattern20 where
  | T1_T1 | T1_T2 | T1_T3 | T1_T4 | T1_T0
  | T2_T1 | T2_T2 | T2_T3 | T2_T4 | T2_T0
  | T3_T1 | T3_T2 | T3_T3 | T3_T4 | T3_T0
  | T4_T1 | T4_T2 | T4_T3 | T4_T4 | T4_T0
  deriving DecidableEq, Repr

/-! ### Tone sandhi neutralization as DLM kernel application -/

/-- **T3 tone sandhi neutralization via DLM kernel**.

    The classical phonological rule "T3 → T2 / __ T3" stipulates that
    underlying `/T3 T3/` surfaces as `[T2 T3]`. Within the DLM, this
    surface coincidence is **derived**, not stipulated: if the CE
    centroids of T3-T3 and T2-T3 word tokens differ by an element of
    the production map's kernel, then their predicted pitch contours
    coincide.

    The paper (§5) reports that for Taiwan Mandarin this kernel
    condition holds empirically — complete neutralization. For
    Standard Chinese the kernel condition holds only approximately,
    consistent with the literature's report that T3 sandhi
    neutralization is incomplete in Standard Chinese.

    The specific patterns `T3_T3` and `T2_T3` are **load-bearing in
    the type signature**: the theorem witnesses the paper's specific
    empirical claim, not a generic two-pattern claim. The body is the
    kernel characterisation
    `LinearDiscriminativeLexicon.production_eq_iff`. -/
theorem t3_sandhi_via_kernel
    (D : LuTaiwanMandarinDLM)
    (centroidOf : TonePattern20 → ContextualEmbedding)
    (h_kernel :
      centroidOf .T3_T3 - centroidOf .T2_T3 ∈ LinearMap.ker D.production) :
    D.production (centroidOf .T3_T3) = D.production (centroidOf .T2_T3) :=
  D.production_eq_iff.mpr h_kernel

/-- **Quantitative refinement of `t3_sandhi_via_kernel`.** The exact-
    kernel hypothesis is the limiting case; in real data the centroid
    difference is *small but non-zero*. Lipschitz continuity bounds
    the resulting contour difference by `‖production‖ * ε` whenever
    the centroid difference is within ε.

    The empirical content of [lu-chuang-baayen-2026] §5 is that
    for Taiwan Mandarin the trained `‖production‖` and the centroid
    distance are both small enough that the contour bound is
    consistent with the reported "essentially identical" surface
    realizations. For Standard Chinese the bound permits visible
    contour difference, matching the reported incomplete neutralization.

    Lipschitz application of `dlm_neighbor_centroids_imply_neighbor_contours`. -/
theorem t3_sandhi_quantitative
    (D : LuTaiwanMandarinDLM)
    (centroidOf : TonePattern20 → ContextualEmbedding) {ε : ℝ}
    (h : ‖centroidOf .T3_T3 - centroidOf .T2_T3‖ ≤ ε) :
    ‖D.production (centroidOf .T3_T3) - D.production (centroidOf .T2_T3)‖ ≤
      ‖D.production.toContinuousLinearMap‖ * ε :=
  dlm_neighbor_centroids_imply_neighbor_contours D h

/-! ### Dialect flexibility via different production maps -/

/-- **DLMs accommodate dialect variation in neutralization without
    rule modification.** The same `LinearDiscriminativeLexicon`
    architecture supports both complete neutralization (Taiwan Mandarin:
    T3-T3 surface = T2-T3 surface) and incomplete neutralization
    (Standard Chinese: T3-T3 differs subtly from T2-T3) by varying *the
    production map's kernel*, not by introducing a separate sandhi
    rule.

    Witness: the all-zero DLM has every `MeaningVec` mapping to the
    zero contour — every meaning pair is "neutralized" (degenerate
    Taiwan-Mandarin extreme); a DLM with the non-degenerate `broadcast`
    production map distinguishes the same pair (Standard-Chinese-like
    extreme). The architectural point survives the witness's simplicity:
    a SINGLE `LinearDiscriminativeLexicon` type accommodates both
    regimes; only the trained weights differ.

    Cross-framework significance: a rule-based account requires
    dialect-specific rule modification (or stochastic optionality) to
    handle this variation. The DLM accommodates it without any
    framework-level move. -/
theorem dlm_dialect_flexibility :
    ∃ (D₁ D₂ : LuTaiwanMandarinDLM) (e₁ e₂ : ContextualEmbedding),
      D₁.production e₁ = D₁.production e₂ ∧
      D₂.production e₁ ≠ D₂.production e₂ := by
  refine ⟨⟨0, 0⟩, ⟨0, broadcast 0⟩, 0, Pi.single 0 1, rfl, fun h => ?_⟩
  have h0 := congrFun h 0
  simp only [broadcast_apply, Pi.zero_apply, Pi.single_eq_same] at h0
  exact zero_ne_one h0

/-! ### Empirical content (prose) -/

/-! ### Methods + accuracies as paper-supplied empirical facts

Per `CLAUDE.md` (Processing-scope guidance), specific numerical fits
(R² values, AIC reductions, cross-validation accuracies) are out of
scope as Lean theorems. They are recorded here as documented empirical
findings with paper-section pointers.

**Word emerges as crucial across all 20 tone patterns** (paper §3.4.1,
Fig. 2, Table 4). Withholding the `word` factor smooth from the GAMM
raises AIC by 7,269.27 to 12,345.54 across the four tonal contexts,
substantially exceeding the AIC change for any other predictor
including `tone_pattern`. When `word` is included, withholding
`tone_pattern` raises AIC by only single- or low-double-digit units
per context (paper §3.4.1) — `word` essentially subsumes `tone_pattern`.

**Sense > word** (paper §3.4.2, Table 4). Adding `sense_type` on top
of `tone_pattern` produces a substantial AIC reduction
(−16,077.20 at 4.4, −10,541.88 at 3.4, −9,171.19 at 4.1, −7,895.57
at 4.0; values from Table 4), exceeding the contribution of
`word` alone. Replicates the headline sense-effect of
[chuang-bell-tseng-baayen-2026] on the broader 20-pattern dataset.

**DLM accuracy across three preprocessing methods** (paper §4.4):
- Method I (per-token GAMMs): training 2.8% / test 1.4%
- Method II (per-word-type GAMMs): training 23.5% / test 15.1% (**best**)
- Method III (per-tonal-context GAMMs): training 12.0% / test 6.9%
- Permutation baseline ≈ 0.4%; majority baseline ≈ 1.3%.

**Form–meaning isomorphism across all 20 tone patterns** (paper §4.4,
Fig. 9, Fig. 10). Cosine similarity / Pearson correlation /
Euclidean distance between GAMM-derived gold-standard contours and
DLM-predicted contours, respectively for methods I, II, III:
- Method I:   cosine 0.73 / corr 0.85 / dist 1.24
- Method II:  cosine 0.93 / corr 0.98 / dist 1.50
- Method III: cosine 0.82 / corr 0.96 / dist 1.09

Method II wins on cosine and correlation; loses (slightly) on
Euclidean distance. Boxplot of the three measures across methods:
paper Fig. 10.

**Comparison to lab speech** (paper §5, Fig. 11). The DLM-derived
contours from spontaneous Taiwan Mandarin closely match [xu-1997]'s
lab-speech contours for most tone patterns (T4-T4, T2-T3, T2-T4 nearly
identical); some patterns (T1-T1, T1-T2) differ visibly, attributed
to dialect (Beijing vs. Taiwan Mandarin) and register (lab vs.
spontaneous) effects.

### Implications recorded in the paper's discussion

- **Word-and-paradigm sufficiency** (paper §5): the DLM does not need
  abstract phonological units (syllable, segment, tone) to predict
  pitch realisation — meaning vectors → pitch vectors directly. This
  aligns with [heitmeier-chuang-baayen-2026]'s W&P framing of
  the DLM and challenges item-and-arrangement architectures that
  presuppose stored sub-word inventories.
- **Anti-arbitrariness of the sign** (paper §5): the linear meaning→form
  mapping generalises to held-out data, falsifying the axiom that
  the form–meaning relation is fundamentally arbitrary.
- **Anti-dual-articulation** (paper §5, also [chuang-bell-tseng-baayen-2026]):
  the same DLM architecture exhibits isomorphism between phonetic
  form-space and contextualised meaning-space, undermining the
  assumption that form and meaning are orthogonal grammar modules.
- **Tone sandhi as kernel-emergence**: see §3 (`t3_sandhi_via_kernel`).
- **Dialect variation as kernel variation**: see §4 (`dlm_dialect_flexibility`).
- **Beyond Mandarin**: paper §5 cites preliminary results
  ([chuang-bell-tseng-baayen-2026] discussion) that English
  two-syllable words also exhibit word-specific pitch components,
  suggesting form-meaning isomorphism is not a tone-language quirk. -/

end LuChuangBaayen2026
