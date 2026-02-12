# Changelog

## [0.184.0] - 2026-02-11

### Fixed
- **NeoGricean/Exhaustivity/Basic.lean**: Removed false `exhMX_unique_when_closed` (claimed all exhMX readings equivalent under conjunction closure — counterexample: ALT with distinct MC-sets under ∧-closure). Replaced with correct `exhOperators_coincide_under_closure` (exhIE = ⋁ readings, combining theorem9 + lemma3, fully proved) and `exhMX_unique_when_unique_MCset` (readings equivalent when MC-set is unique, trivially proved). `flat_singleton` and `flat_empty` fully proved (no sorry) via propext + funext.

## [0.183.0] - 2026-02-11

### Fixed
- **NeoGricean/Exhaustivity/Basic.lean**: Replaced incorrectly stated `exhIE_eq_bigConj_exhMX` (claimed exhIE ≡ₚ ⋀ readings, but forward direction is false when MC-sets diverge) with `bigConj_exhMX_entails_exhIE` — correct one-directional entailment, fully proved (no sorry). FLAT operator upgraded from List-based to Set-based definition using total choice functions.
- **NeoGricean/Constraints/Wang2025.lean**: Replaced vacuous `IC_violation_always_blocks` (concluded `¬P ∨ True`, trivially true by `right; trivial`) with meaningful theorem proving IC violation forces `.odd` status via `wangCheck`. Extracted `wangCheck` as named function for provability.
- **Phenomena/Presupposition/Studies/Wang2025.lean**: Renamed `ContextCondition.partial_` (Lean keyword collision hack) to `ContextCondition.partialSupport`.

## [0.182.0] - 2026-02-11

### Added
- **NeoGricean/Exhaustivity/Basic.lean**: `exhMX` operator (Wang 2025) — per-MC-set exhaustification completing the Spector triad. `exhMXReading`, `exhMXReadings`, `bigConj_exhMX_entails_exhIE` (⋀ readings ⊆ₚ exh_ie), `exhMW_eq_bigDisj_exhMX` (exh_mw = ⋁ exh_mx readings), `exhMXReading_entails_exhIE`, `exhMX_unique_when_closed`. FLAT operator: `flat`, `flat_singleton`, `flat_empty`.
- **NeoGricean/Presuppositions.lean**: Wang (2025) Table 4.1 alternative structure classification. `AltStructure` (.deletion/.replacement/.none), `PragConstraint` (.IC/.FP/.MP) with `isViolable`, `constraintRanking`, `Obligatoriness` (.obligatory/.optional/.blocked), `PresupTriggerEntry`, `PresupTrigger.defaultAltStructure`.
- **NeoGricean/Constraints/Wang2025.lean**: Full constraint evaluation module. `satisfiesIC`, `satisfiesFP`, `partialFP`, `mpPrefers`, `wangCheck`, `predictObligatoriness`. Key theorems: `deletion_alt_partial_resolution`, `no_alt_blocked_partial`, `full_cg_obligatory`, `no_cg_blocks`, `IC_violation_always_blocks`. K operator: `speakerK`. `FelicityCondition` instance for `WangInput`. CI bridge: `ciLift_felicitous_when_fp_holds`.
- **TruthConditional/Expressives/Basic.lean**: CI bifurcation for de re presupposition (Wang & Buccola 2025). `ciLift` (PrProp → TwoDimProp bridge), `ciLift_atIssue`, `ciLift_ci`, `deRe_from_ciLift`, `ciLift_neg_preserves_presup`, `ciLift_roundtrip`.
- **Phenomena/Presupposition/Studies/Wang2025.lean**: Experimental data. `ContextCondition` (.full/.partialSupport/.noSupport), `MandarinTrigger` (9 triggers), `Exp1Datum` (naturalness ratings), `Exp3Datum` (de re judgments). Key data: `ye_full/partial/none`, `jiu_full/partial/none`, `zhidao_full/partial/none`. Theorems: `ye_jiu_partial_diverge`, `obligatory_trigger_pattern`, `blocked_trigger_pattern`, `additive_deRe_available`.
- **Fragments/Mandarin/Particles.lean**: 9 Mandarin presuppositional particle entries. `PresupParticle` structure linking hanzi/pinyin/gloss to `PresupTriggerEntry` and `MandarinTrigger`. Per-datum verification: `ye_deletion`, `jiu_no_alt`, `zhidao_replacement`, `obligatory_all_deletion`, `blocked_no_alt`.

## [0.181.0] - 2026-02-11

### Changed
- **Core/Scales.lean**: Removed `NumExpr`, `numScaleLowerBound`, `NumeralAlternativeKind`, `numAlternatives` — numerals don't fit `HornScale` (infinite under lower-bound, non-monotonic under bilateral). Added docstring explaining why. Numeral alternative infrastructure lives in `Semantics.lean` (`NumeralAlternative`, `NumeralTheory.isStrongerThan`).
- **Lexicon.lean**: Removed `ScaleMembership.numeral` constructor. `ScaleMembership` now covers only closed-class scales (quantifiers, connectives, modals).
- **NeoGricean/ScalarImplicatures/Basic.lean**: Removed `.numeral` case from `getScaleInfo`.

## [0.180.0] - 2026-02-11

### Changed
- **Numeral type unification & file consolidation**: Consolidated 5 files (`Theory.lean`, `LowerBound.lean`, `Bilateral.lean`, `Maximality.lean`, `Compare.lean`) into single `Semantics.lean`. `NumeralTheory` now parameterized by `bareRel : OrderingRel` (`.ge` for lower-bound, `.eq` for bilateral) instead of arbitrary `meaning` function — all numeral meanings flow through `maxMeaning rel m n`. Theory instances are one-liners. Grounding theorems (`atLeast_eq_lowerBound`, `bare_eq_bilateral`) become `rfl`. `BareNumeral` replaces duplicate `NumWord` type. Backward-compat aliases (`NumWord`, `DeFregean`, `Exact`, `lowerBoundMeaning`, `bilateralMeaning`) preserve all consumer APIs.
- **CumminsFranke2021.lean**: Removed local `moreThanMeaning` definition, now uses canonical one from `Semantics.lean`. Grounding theorems rewritten against unified `maxMeaning`.
- **NumeralModifiers.lean**: Import updated from `Maximality` to `Semantics`.
- **NegationScope.lean**, **Operations.lean**, **GoodmanStuhlmuller2013.lean**: Import updates only.

### Removed
- `Theory.lean`, `LowerBound.lean`, `Bilateral.lean`, `Maximality.lean`, `Compare.lean` — all content consolidated into `Semantics.lean`.

## [0.179.0] - 2026-02-11

### Added
- **Maximality.lean**: Kennedy (2015) unified modified numeral semantics. `OrderingRel` (=, >, <, ≥, ≤), `ModifierClass` (.classA/.classB), `BoundDirection` (.upper/.lower), `maxMeaning` (unified meaning function for all numeral expressions). Named specializations: `bareMeaning`, `moreThanMeaning`, `fewerThanMeaning`, `atLeastMeaning`, `atMostMeaning`. Grounding theorems: `bare_eq_bilateral_{one,two,three}` (= bilateral), `atLeast_eq_lowerBound_{one,two,three}` (≥ = lower-bound), `moreThan_eq_cumminsFranke` (> = C&F). Class A/B theorems: `classA_gt_excludes_bare`, `classB_ge_includes_bare`, `classB_entailed_by_bare`, `classA_not_entailed_by_bare`. Anti-Horn-scale: `bare_not_monotonic`, `numerals_not_horn_scalar`. `CardinalityDegree` HasDegree instance, `maxMeaning_{gt,ge}_from_degree`. `NumeralAlternative`, `lowerAlternatives`, `upperAlternatives`.
- **ClausWalch2024.lean**: Empirical data on evaluative valence framing effects. `Modifier` (.exactly/.atMost/.upTo), `FramingCondition` (.standard/.reversed), `Exp1Datum` (truth-value judgments), `Exp2Datum` (framing endorsement rates). Key theorems: `atMost_reverses_framing`, `upTo_standard_framing`, `exactly_standard_framing`, `atMost_upTo_diverge`.

### Changed
- **NumeralModifiers.lean**: Added `ModifierType.bound`, `PragmaticFunction.boundSignal`, `EvaluativeValence` (.positive/.negative/.neutral). Extended `NumeralModifierEntry` with `boundDir`, `modClass`, `evaluativeValence`, `generatesIgnorance` (all with defaults). 6 new entries: `atLeast`, `atMost`, `moreThan`, `fewerThan`, `upTo`, `fromOn`. Collections: `boundModifiers`, `classAModifiers`, `classBModifiers`. Theorems: `classB_all_generate_ignorance`, `classA_no_ignorance`, `atMost_upTo_differ_only_in_valence`. Now imports Maximality.lean.
- **Compare.lean**: Now imports Maximality.lean (transitively gets LowerBound + Bilateral). Added `classA_classB_diverge_on_bare_world`, `classB_strictly_weaker_than_bare`, `moreThan_eq_cumminsFranke_bridge`.
- **NumeralSalience.lean**: Bridge 7 (evaluative valence → framing). Imports ClausWalch2024. `atMost_negative_predicts_reversal`, `upTo_positive_predicts_standard`, `valence_explains_framing_divergence`.
- **Core/Scales.lean**: Renamed `numScale` → `numScaleLowerBound` with `abbrev numScale` for backward compat. Added docstring explaining that under bilateral semantics numerals are non-monotonic and do NOT form a Horn scale. Added `NumeralAlternativeKind` (.bare/.classA/.classB) and `numAlternatives` for Kennedy's alternative set structure.

## [0.178.0] - 2026-02-11

### Added
- **Core/Roundness.lean**: Framework-agnostic k-ness infrastructure extracted to Core. `hasIntKness`, `has2_5ness`, `RoundnessProperties` (6-field struct), `roundnessScore` (0–6), `maxRoundnessScore`. `RoundnessGrade` enum (`.high`/`.moderate`/`.low`/`.none`) for shared score-binning. `contextualRoundnessScore` (base-relative divisibility properties) + `roundnessInContext` (Krifka 2007 granularity override). Per-datum verification: `roundness_100 = 6`, `roundness_7 = 0`, `roundness_50 = 4`.
- **Woodin, Winter & Bhatt 2024** (NumberUse/WoodinEtAl2024.lean): Corpus frequency data. 6 `RoundnessCoefficient` β values (10-ness 4.46 > 2.5-ness 3.84 > ... > mult5 0.06), `hierarchy_ordering` theorem, `weightedRoundnessScore`, `Register` effect data. Bridges: `weighted_100_gt_50`, `weighted_50_gt_110`.
- **Cummins 2015 OT constraints** (NeoGricean/Constraints/NumericalExpressions.lean): `QuantifierForm`, `NumeralCandidate`, `inferGranularity`. 4 constraint functions: `infoViolations`, `granularityViolations`, `qsimpViolations`, `nsalViolations` (= 6 - roundnessScore). `OTConstraint`, `defaultRanking` (INFO >> Gran >> QSIMP >> NSAL), `lexLessThan` + `harmonicallyBounds`, `optimalCandidate`. `enrichmentWidth` (predicts C&F 2021 pragmatic enrichment range via `RoundnessGrade`). `nsalAsRSACost` (normalized ℚ cost). Theorems: `nsal_is_complement`, `round_beats_nonround_nsal`, `rounder_wider_enrichment`, `round_cheaper_in_rsa`.
- **Numeral Salience bridges** (Comparisons/NumeralSalience.lean): 6 cross-module bridges. NSAL↔RSA cost (`round_cheaper_in_rsa_bridge`, `maximally_round_free`), Woodin↔prior (`roundness_prior_monotone`), k-ness↔PrecisionMode (`roundness_grounds_precision_100/7`, `base10_round_implies_approximate` sorry), k-ness↔NumeralModifiers (`round_wider_halo`), k-ness↔C&F enrichment (`enrichment_100_wider_than_110`), OT↔RSA map (`ot_rsa_agree_round_preference`).

### Changed
- **Degree.lean**: Added `adaptiveBase` (uses `RoundnessGrade`), `adaptiveTolerance`, `haloWidth`, `inferPrecisionMode` — k-ness-derived adaptive pragmatic halo connecting to Lasersohn (1999), Krifka (2007), Kao et al. (2014). Import: `Linglib.Core.Roundness` (not Phenomena).
- **Numerals.lean**: k-ness definitions extracted to `Core/Roundness.lean`. Retains `classifyRoundness`, datum types, and `coarse_implies_kness` bridge theorem. Deleted false `kness_refines_coarse` theorem (counterexample: n=15).
- **NumericalExpressions.lean**: `harmonicallyBounds` refactored to use standalone `lexLessThan` (provable transitivity). `enrichmentWidth` uses `RoundnessGrade` match instead of duplicated score-binning.

## [0.177.0] - 2026-02-11

### Changed
- **Unified multi-objective RSA speakers under `combined`/`combined3`**: All weighted speaker utilities now flow through `CombinedUtility.combined` or `combined3`.
- **CombinedUtility.lean**: Added `betaToLam`/`lamToBeta` reparameterization bridge (additive β ↔ convex λ). `goalOriented_eq_scaled_combined` (key identity: `U+β·V = (1+β)·combined(β/(1+β), U, V)`), `goalOriented_same_ranking` (scaling preserves ordering), round-trip theorems.
- **YoonEtAl2020.lean**: S1 refactored to use `combined phi socialScore infoScore cost`. S2 refactored to use `combined3 ω_inf ω_soc ω_pres ...`. Added `s1_uses_combined`, `s2_uses_combined3` bridge theorems.
- **SumersEtAl2023.lean**: `combinedUtility` body refactored to use `combined params.lam uT uR cost`. Bridge theorems `combined_pure_truthfulness`/`combined_pure_relevance` now delegate to `combined_at_zero`/`combined_at_one`. Added `sumers_uses_combined`.
- **NoncooperativeCommunication.lean**: `NoncooperativeRSAParams.β` reparameterized to `goalWeight ∈ [0,1]` (convex form). `fullModel` speaker side now uses `combined goalWeight uEpi uGoal` (was `goalOrientedUtility`). `barnettFitted` updated to `goalWeight := 226/326` (= β/(1+β) for β=2.26). Added `barnett_eq6_via_combined`.
- **BarnettEtAl2022.lean**: Added `eq6_via_combined` theorem bridging additive Eq. 6 to convex `combined` form.
- **NoncooperativeCommunication.lean**: Pragmatic vulnerability theorems (Cummins 2025 §4). `pragmatic_vulnerability`/`pragmatic_vulnerability_sym` (when L1 diverges from L0, vigilant posterior is strictly between them), `vigilant_mono_trust`/`vigilant_mono_trust_sym` (more trust monotonically pulls posterior toward L1), `no_vulnerability_when_equal` (L1=L0 ⇒ no exploitation possible). Quantitative exploitability bounds: `vigilant_deviation_exact` (deviation from L0 = τ·(L1-L0)), `vulnerability_gap_exact`, `exploitability_scales_as_tau_sq` (squared error ∝ τ²), `vigilant_error_decomposition`, `vigilant_error_when_l0_correct`, `optimal_vigilance`/`optimal_vigilance_in_range` (zero-error τ* = (truth-L0)/(L1-L0)). Backfire generalization conjecture: `backfire_generalization` (monotone L0 + goal-oriented speaker ⇒ ∃ non-maximal utterance where L1 reverses literal evidence), `barnett_backfire_instance` (sorry).

## [0.176.0] - 2026-02-11

### Changed
- **CombinedUtility.lean**: `goalOrientedUtility` promoted from NoncooperativeCommunication to shared core (`U_epi + β · U_goal`). Theorems: `goalOriented_eq_combinedWeighted`, `goalOriented_cooperative`, `goalOriented_mono_beta`, `goalOriented_antimono_beta_neg`.
- **BarnettEtAl2022.lean**: Namespace `RSA.BarnettEtAl2022` → `RSA.Implementations.BarnettEtAl2022`. Replaced `combinedPersuasiveUtility` with `abbrev eq6 := goalOrientedUtility` (→ CombinedUtility). Tighter bridges: `eq6_is_goalOriented`, `eq6_at_one`.
- **CumminsFranke2021.lean**: Namespace `RSA.CumminsFranke2021` → `RSA.Implementations.CumminsFranke2021`.
- **ArgumentativeStrength.lean**: Added `argStr_speaker_prefers_stronger` (goal-oriented speaker prefers higher argStr, → CombinedUtility.goalOrientedUtility).
- **NoncooperativeCommunication.lean**: Removed local `goalOrientedUtility` duplicate (uses CombinedUtility). Updated Barnett bridges to use `eq6`. Removed duplicate `argStr_speaker_prefers_stronger` (uses ArgumentativeStrength).

## [0.175.0] - 2026-02-11

### Added
- **Noncooperative Communication** (NoncooperativeCommunication.lean): Unified argumentative RSA framework following Cummins (2025). `goalOrientedUtility` generalizing both Barnett et al.'s persuasive RSA and C&F's argumentative strength as `combinedWeighted(1, β, U_epi, U_goal)`. `SpeakerOrientation` (.cooperative/.argumentative), `orientationOf`. Bridges: `barnett_is_goalOriented` (→ BarnettEtAl2022), `barnett_goalOriented_combinedWeighted` (transitive identity), `all_cooperative_at_zero` (all three agree at β=0), `bayesFactor_monotone_in_posterior` (C&F's ordinal measure monotone in Barnett's posterior), `positive_argStr_iff_posterior_above_prior` (→ ArgumentativeStrength), `argStr_speaker_prefers_stronger`. `MeaningLevel` taxonomy (.assertion/.implicature/.presupposition/.typicality) with `blameworthinessRank` (Mazzarella et al. 2018). `EpistemicVigilance` (Sperber et al. 2010): `vigilantPosterior`, `vigilant_is_combined` (→ CombinedUtility), `vigilant_convex`. `NoncooperativeRSAParams` (β, τ), `standardRSA`, `barnettFitted`, `fullModel` with `fullModel_standard`.

## [0.174.0] - 2026-02-11

### Added
- **Barnett, Griffiths & Hawkins 2022** (BarnettEtAl2022.lean): Persuasive RSA framework extending speaker utility with goal state w*. `persuasiveUtility` (Eq. 4), `combinedPersuasiveUtility` (Eq. 6), `weakEvidenceOccurs` definition. Stick Contest domain (3 sticks from {1,...,5}, 10 worlds): `l0Longer`, `speakerProb`, `l1Longer` with exact ℚ computation. Key theorems: `weak_evidence_effect_s4` (positive evidence backfires at β=2), `strong_evidence_works_s5`, `beta_zero_literal` (β=0 recovers L0). Bridges: `combinedPersuasive_eq_combinedWeighted` (→ CombinedUtility), `argStr_positive_but_backfires` (→ ArgumentativeStrength).
- **Weak Evidence Effect Data** (WeakEvidenceEffect/Data.lean): Stick Contest experimental design and results (n=723). `pragmatic_backfire` (m=34.7 < 50 for pragmatic group), `literal_no_backfire` (m=50.1), `groups_differ`. Model comparison Table 1: `rsa_speaker_dep_best_likelihood`, `rsa_speaker_dep_best_waic`. Fitted parameters: β̂=2.26, pragmatic group p̂_z=0.99 (J1), literal group p̂_z=0.1 (J0).

## [0.173.0] - 2026-02-11

### Added
- **Argumentative Strength** (ArgumentativeStrength.lean): Merin (1999) log-likelihood ratio measure. `ArgumentativeGoal`, `bayesFactor`, `argStr` (C&F Eq. 17), `pragArgStr` (C&F Eq. 25), `hasPositiveArgStr`/`argumentativelyStronger` ordinal comparisons, `ArgumentativeDifficulty` (MS et al. 2024), `rationalHearerSemantic`/`rationalHearerPragmatic` (C&F Eqs. 27–28). Bridge theorems: `argStr_eq_pointwiseKL` (→ InformationTheory), `argStr_positive_iff` (ordinal characterization), `argStr_from_combined_at_one` (→ CombinedUtility).
- **Cummins & Franke 2021** (CumminsFranke2021.lean): Conference registration scenario. `moreThanMeaning` with grounding theorems to `lowerBoundMeaning`. Semantic argStr computation: `moreThan110_semantically_stronger`. Pragmatic reversal: `wider_enrichment_weakens_argStr`. Exam scenario: `ExamStimulus`, `examDifficulty`, `truthfulQuantifiers`, `strongestTruthfulPositive` with weakening pattern verification (all→most→some). `quantifier_ordering_matches_scale` (→ Core.Scales).
- **Argumentative Framing Data** (ArgumentativeFraming/Data.lean): `FramingDirection`, `QuantifierChoice`. C&F REF case study: 10 `TopMDatum` entries (examples 29–38), `h1_all_round`, `h1_all_truthful`, `h2_majority_preferred`. MS et al. Exp 1: `exp1_adjective_matches_condition`, `exp1_some_most_dominant`, difficulty-driven weakening. MS et al. Exp 2: `exp2_positive_bias`, `exp2_quant_numeral_most_common`.

## [0.172.0] - 2026-02-11

### Added
- **Outlook Markers** (Kubota 2026): `OutlookMarker.lean` formalizing dual-layered secondary meaning (presuppositional + expressive-like). `StanceType` (.negative/.minimum/.contrary/.emphasis), `OutlookMeaning` with `toPrProp`/`toTwoDimProp` decomposition, `SecondaryMeaningClass` three-way typology (anaphoric presupposition / lexical precondition / discourse-sensitive), `TriggerStrength` (hard/soft), `SecondaryMeaningProperties` diagnostic profile. `ModalCompatibility` with `semete_rejects_epistemic`/`nanka_accepts_all_modals`. Key theorems: `outlook_shares_descriptiveIneffability`, `outlook_lacks_independence`, `outlook_lacks_nondisplaceability`, `outlook_requires_discourse_antecedent`, `outlook_allows_perspective_shift`, projection through negation for both layers.
- **Japanese Outlook Marker Fragment** (Particles.lean): 13 `OutlookEntry` items — adverbs (*dōse*, *shosen*, *yahari*, *kekkyoku*, *masani*, *mushiro*, *kaette*, *yoppodo*, *semete*, *mashite*) and focus particles (*nanka*, *kurai*, *koso*). Per-entry stance verification theorems. `all_require_counterstance`, `semete_unique_modal_restriction`.
- **Kubota2026 Phenomena** (OutlookMarkers/Kubota2026.lean): `FelicityDatum` (counterstance requirement: (37)–(39)), `DenialDatum` (descriptive ineffability: (40)–(41)), `PerspectiveShiftDatum` ((42)), `ModalInteractionDatum` ((45)–(46)). Bridge theorems: `semete_modal_matches_data`, `nanka_modal_matches_data`.

## [0.171.0] - 2026-02-11

### Added
- **TTR Full Ch8 Context Machinery** (Underspecification.lean): `Cntxt₈` (eq 82, 7-field context: q/𝔰/𝔩/𝔯/𝔴/𝔤/𝔠), `Cntxt₈.initial`, `isEq10`/`isEq74` (evolution across eqs 10→74→82). `boundary₈` (B, eq 77: removes locality at clause boundaries), `anaphoricCombine₈` (@_{i,j} with l-field, eq 76), `sentenceRule₈` (eq 81). `anaphorFree₈` (𝔄, eq 85: r-field filter), `reflexivize₈` (full ℜ₈, eq 84), `vpRule₈` (eq 88). `UnderspecClosure₈` (eq 89: 7-clause inductive for generalized 𝔖). `NQuantScope` (n-ary scope, `ScopeOrdering`, `nestQuants`), three-quantifier example. `DiscourseContext`, `crossSententialResolve` (eqs 37-44: cross-sentential anaphora), "A man walked. He whistled." phenomenon. `alignPaths` (eq 52: path alignment), `semNo₈`, "No dog which chases a cat catches it" with true/false scenarios (eqs 46-55). Bridge: `reflexivize₈_agrees_with_simple` (ℜ₈ ↔ ℜ), `twoQuant_embeds_in_closure`, `donkeyNeg_uses_localization`.
- **Assgnmnt operations** (Discourse.lean): `Assgnmnt.empty`, `Assgnmnt.update`, `Assgnmnt.merge` with `update_same`, `update_other`, `empty_none`, `merge_empty_left`.

## [0.170.0] - 2026-02-10

### Changed
- **TTR Underspecification cleanup**: updated module docstring (was stale "First Slice"), replaced Cooper §-based section labels with conceptual names, scoped file-level `variable {E : Type}` into `ScopeInfrastructure` section to prevent namespace leakage, renamed `isDog'` → `isDog₈` for consistency with `isDonkey₈`.
- **`localizeConditional`**: new conditional localization operator completing the 𝔏/𝔏ʸ hierarchy. `strongDonkeyConditional` now derives from `localizeConditional beatsParam ownsGate` rather than being defined ad hoc. Added `localizeUniv_iff_conditional_trivial` (𝔏ʸ = degenerate conditional) and `localizeUniv_implies_conditional` (𝔏ʸ ⊂ conditional).
- **`like₈` made non-trivial**: Sam likes everyone, Bill likes Bill/Kim, Kim likes only herself. Reflexivization now genuinely constrains witness space (`reflexive_constrains_kim`). `allLikeSelf` requires per-case witnesses instead of trivial wildcard.
- **Removed `PPpty.isAnaphorFree`**: convoluted unused encoding of Cooper's 𝔄 (eq 85). Left a NOTE explaining that 𝔄 and B (eq 77) await full record-type machinery.

## [0.169.0] - 2026-02-10

### Added
- **TTR Binding Theory** (Ch8 §8.3): `reflexivize` (ℜ, eq 84), `anaphoricResolve` (@_{i,j}, eq 28). Phenomenon: "Sam likes himself" vs "Sam likes him" with ℜ vs pronoun resolution. Bridge theorem 3 `reflexive_predicts_binding` connecting ℜ to `Phenomena.Anaphora.Coreference`: per-datum verification for `reflexivePattern` (Condition A), `pronounPattern` (Condition B), `complementaryDistributionData`. Bridge to `Core.Interfaces.BindingSemantics`: `reflexivize_to_binding`, `reflexiveBindingConfig` (well-formed), `pronominalBindingConfig`.

## [0.168.0] - 2026-02-10

### Added
- **TTR donkey → Phenomena bridge**: `strongDonkeyConditional` (conditional universal strong reading, distinct from the too-strong 𝔏ʸ), `strong_donkey_distinction` (𝔏ʸ ≠ correct strong reading). Per-datum verification theorems connecting TTR predictions to `Phenomena.Anaphora.DonkeyAnaphora`: `geach_weak_available`, `geach_strong_available`, `geach_bound_reading`, `strongDominant_readings_available`.

## [0.167.0] - 2026-02-10

### Added
- **TTR Underspecification localization** (Ch8 §8.5): `localize` (𝔏), `localizeUniv` (𝔏ʸ), `localization_is_purification` bridge theorem (𝔏 = 𝔓), `localizationUniv_is_purificationUniv` (𝔏ʸ = 𝔓ʸ), `localization_readings_agree_when_pure` (corollary of Ch7 `donkey_readings_agree_when_pure`). Donkey anaphora phenomenon: "every farmer who owns a donkey beats it" with weak/strong readings, `donkey_readings_diverge` (weak ≠ strong when Bg non-trivial).

## [0.166.0] - 2026-02-10

### Added
- **TTR Underspecification.lean** (Ch8 first slice): `QStore`, `isPlugged`/`isUnplugged`, `store`/`retrieve`, `TwoQuantScope`, `𝔖` underspecification closure, "every boy hugged a dog" scope example with surface/inverse readings. Bridge theorems: `𝔖_to_tagged`/`tagged_to_𝔖` (bijection with `ScopeConfig` from Scontras & Pearl 2021), `surfaceScope_inner_witness` (scope → `ParticularWC_Exist`), `surface_scope_matches_existPQ` (scope → Ch7 `existPQ`).
- **IType → Intension bridge** (Core.lean): `IType.toIntension`, `IType.rigid_iff_isRigid`, `IType.coext_not_intEq` — connects Ch1 intensional types to `Core.Intension.IsRigid` via Bool-valued `ModalTypeSystem`.

## [0.165.0] - 2026-02-10

### Changed
- **TTR re-split**: `Basic.lean` (~2161 lines) → `Core.lean` + `Discourse.lean` along linglib's conceptual joints (foundations vs discourse/pragmatics) instead of Cooper chapter boundaries. Import chain: Core → Discourse → Modality → Quantification.
- **ModalTypeSystem**: replaced `structure` wrapper with `abbrev ModalTypeSystem (W : Type) (Pred : Type) := W → Pred → Bool` — isomorphic but lighter.
- **propT**: added `abbrev propT (p : Prop) : Type := PLift p` in Core.lean, replacing raw `PLift` usage across all 4 files.
- **QuantName**: replaced `String`-dispatched `anaphoraAvailable` with `QuantName` inductive for typed quantifier dispatch.
- **ExperienceBase**: parameterized with `(E : Type) (P : Type)` and `Finset` instead of `ℕ`-indexed predicates and `List`.
- **Bridge theorems**: `toParametric_toPrProp_assertion` (Parametric ↔ PrProp roundtrip), `modalSystem_induces_intension` + `ModalSystem.isRigidType` (Core.Intension bridge), `InfoState.toCoreInfoState` (DynamicSemantics.Core bridge), `meaningPostulate_transfers_belief` (MeaningPostulate → believe transfer).

## [0.164.0] - 2026-02-10

### Changed
- **TTR cleanup**: `semDefArt`/`semUniversal` now return `Type` (not `Prop`), consistent with TTR's types-as-propositions philosophy. `WitnessSet` base structure factored out of 11 witness set types via `extends`. Three `sorry` theorems proved: `witnessGQ_exist_conservative`, `witnessGQ_every_conservative`, `comp_witness_card`. Bridge theorems connecting witness quantification to extensional GQs: `particular_exist_iff_witnessGQ`, `universal_iff_witnessGQ`, `particularWC_to_witnessGQ`, `particularWC_no_to_witnessGQ`. TTR modules added to `Linglib.lean` imports.

## [0.163.0] - 2026-02-10

### Changed
- **Core/TTR.lean → Theories/DynamicSemantics/TTR/**: Moved TTR from `Core/` to `Theories/DynamicSemantics/TTR/` and split the 3744-line monolith into 3 files along chapter boundaries. `Basic.lean` (Ch 1–5: foundations, records, Ppty, frames, Parametric), `Modality.lean` (Ch 6: ModalSystem, Topos, believe/know, broccoli), `Quantification.lean` (Ch 7: witness sets, purification, witness conditions). Namespace renamed `Core.TTR` → `Theories.DynamicSemantics.TTR`. Follows existing convention alongside DRT, DPL, PLA.

## [0.162.0] - 2026-02-10

### Changed
- **Core/TTR.lean**: Synthesis & integration pass (~250 lines added, restructured). Redundancy elimination: renamed `Subtype` class → `SubtypeOf` (avoids shadowing Lean's `Subtype`), consolidated `Ppty` as alias for `PredType`, unified `Topos ≃ Parametric Type` (`toposEquivParametric`). Appendix material: `Restriction T P := { x : T // P x }` (A11.7, native Lean `Subtype`), symmetric merge = `MeetType` = `Prod` with `symmetric_merge_comm` (A11.3), `AsymMerge` for asymmetric merge. New bridges: `ModalTypeSystem.toModalSystem`/`ModalSystem.toModalTypeSystem` (Ch1 Bool ↔ Ch6 Prop), `ModalSystem.toAccessRel` (TTR → Kripke accessibility), `Parametric.toPrProp`/`PrProp.toParametric` (bg/fg ↔ presupposition/assertion), `know_iff_believe_and_true` + `believe_not_entails_true` (abstract doxastic veridicality), `Topos.inducedNec`/`inducedPoss` + `nec_implies_poss` (abstract Kratzer bridge). 5-layer organization with section markers. Module docstring updated for Ch 1–6 with native Lean type table.

## [0.161.0] - 2026-02-10

### Added
- **Core/TTR.lean**: Cooper (2023) Chapter 5 — Frames and Descriptions (~500 lines). Ambient temperature frames (`AmbTempFrame`, `Scale`, `ζ_temp`), rise events (`RiseEvent`). Partee puzzle resolution: `IndPpty` vs `FramePpty` distinction, `Bot` (Empty) for type-inappropriate application, `framePptyOnInd` blocks "ninety is rising". Two copulas: `semBeID` (individual identity) vs `semBeScalar` (scale readoff). Definite descriptions as dynamic GQs: `unique`, `semDefArt`, `semUniversal` with `Nonempty` bridge from Type to Prop. Fixed-point types (`FixedPtType`, `FrameType`, `pFrame`) for frame-level nouns. Property restriction (`restrictPpty`). Passenger individuation: `TravelFrame`, `PassengerFrame`, `intransVerbFrame`, `pluralPred`, `IsProperPart`. Phenomena: temperature rising/ninety/blocked, dog uniqueness, definite article, same-person-different-journeys passenger individuation.

## [0.160.0] - 2026-02-10

### Added
- **Core/TTR.lean**: Cooper (2023) Chapter 4 — Reference and Mental States (~450 lines). Parametric content (`Parametric` bg/fg structure, `PPpty`, `PQuant`, `PQuantDet`, `PRel2`). `HasNamed` typeclass and `NameContext` for presuppositional proper names. `semPropNameP` — parametric proper name semantics with presupposition (revised from Ch3 `semPropName`). `TotalInfoState` for long-term memory + gameboard. `AccommodationKind` with three-level control regime (gameboard > LTM > no match). Paderewski puzzle: `TwoConcept`/`OneConcept` structures, `merge` with identity proof, `merge_preserves_both`, bridge to `Core.Intension.CoExtensional` via `paderewski_nonrigid_identity`. Unbound pronouns: `Assgnmnt` (variable assignment), `Cntxt` (assignment + propositional context), `semPron` as parametric quantifier. Parametric verb semantics: `semIntransVerbP`, `semTransVerbP`. S-combinator: `Parametric.combine` for merging backgrounds. Phenomena: "Sam leaves" full parametric derivation with `samLeavesTrue` witness, Paderewski two-concept → one-concept merge, pronoun resolution.

## [0.159.0] - 2026-02-10

### Changed
- **TruthConditional/Verb/ViewpointAspect.lean**: Lifted `ViewpointAspectB` from `Modal/Ability.lean` to its canonical home alongside `ViewpointType`. Added `ViewpointType.toBoolAspect`, `ViewpointAspectB.toKleinViewpoint`, and roundtrip theorem `toBoolAspect_toKleinViewpoint`.
- **Core/CausalModel.lean**: Added `factuallyDeveloped` — shared primitive for checking that a cause is present and the effect holds after normal development. Used by `actuallyCaused` (Necessity.lean) and `complementActualized` (Ability.lean).
- **Causative/Necessity.lean**: Refactored `actuallyCaused` to use `factuallyDeveloped`.
- **Modal/Ability.lean**: Removed local `ViewpointAspectB` and `toKleinViewpoint` (now imported from `ViewpointAspect`). Refactored `complementActualized` to use `factuallyDeveloped`. Added `complementActualized_eq_factuallyDeveloped` bridge theorem.
- **Causative/Implicative.lean**: Added `ImplicativeBuilder` enum (`.positive`/`.negative`) following `CausativeBuilder` pattern. `entailsComplement`, `toSemantics` derived properties. Grounding theorems: `positive_entails_complement`, `negative_entails_not_complement`.
- **Fragments/English/Predicates/Verbal.lean**: Replaced `implicativeEntailment : Option Bool` with `implicativeBuilder : Option ImplicativeBuilder`. Added derived `VerbEntry.entailsComplement`. Updated *manage*, *fail*, *remember*, *forget* entries. Grounding theorems: `manage_semantics_implicative`, `fail_semantics_implicative`, per-verb `entailsComplement` verification.
- **Phenomena/ActualityInferences/Data.lean**: Updated `ViewpointAspectB` import to canonical location.

## [0.158.0] - 2026-02-10

### Added
- **Theories/IntensionalSemantics/Causative/Implicative.lean**: Nadathur (2023) Ch. 1 implicative verb semantics (*manage*, *fail*) as two-event causal models. `ImplicativeScenario` bundles `CausalDynamics` with action/complement variables. `manageSem` = action occurred + causally sufficient + complement developed. `manage_entails_complement` grounds `VerbEntry.implicativeEntailment := some true`. `fail_entails_not_complement` for negative implicatives. `implicative_not_aspect_governed` contrasts with ability modals. Concrete `tryAction → swimAcross` scenario verified by `native_decide`.
- **Theories/IntensionalSemantics/Modal/Ability.lean**: Central file bridging causality, modality, and aspect for actuality inferences. `AbilityScenario` maps `World → Situation` (bridge from Kratzer to CausalModel). `abilityAt = causallySufficient` (rfl). `ViewpointAspectB` with `toKleinViewpoint` bridge to Klein's interval semantics. `abilityWithAspect` conjoins ability with actualization under perfective. `perfective_ability_entails_complement` (the central result). `imperfective_ability_compatible_with_unrealized`, `aspect_governs_actuality`, `ability_differs_from_implicative`. `toCircumstantialBase` and `abilityAsKratzerPossibility` bridge to Kratzer modal semantics.
- **Phenomena/ActualityInferences/Data.lean**: Cross-linguistic actuality inference data (8 data points: Greek *boro*, Hindi *saknaa*, French *pouvoir*, English *be able*, each PFV/IMPF). `empirical_matches_theory`: `(aspect == .perfective) == complementEntailed` for all data by `native_decide`.

## [0.157.0] - 2026-02-10

### Changed
- **Fragments/{Hindi,Tamil,Korean,Japanese,Basque,Galician,Magahi,Maithili,Punjabi}/Pronouns.lean**: Expanded from 2nd-person-only to full person inventories (1st, 2nd, 3rd; sg, pl). Language-specific highlights: Tamil inclusive/exclusive 1pl (*naam*/*naangaL*), Korean/Japanese 1sg register variants (*na*/*jeo*, *boku*/*watashi*), Galician 2pl T/V (*vós*/*vostedes*), Basque 2pl *zuek*, Maithili 3sg honorific (*ũ*/*o*), Punjabi 3sg/3pl homophony (*uh*). Each file now exports `secondPersonPronouns` for allocutive-specific theorems and `allPronouns` for full inventory. `has_all_persons` and `has_both_numbers` verification added uniformly.
- **Theories/Minimalism/Phenomena/Allocutivity.lean**: Bridge theorems updated to reference `secondPersonPronouns` instead of `allPronouns`.

## [0.156.0] - 2026-02-10

### Added
- **Core/Pronouns.lean**: Shared cross-linguistic `PronounEntry` and `AllocutiveEntry` types. `PronounEntry` has `form`, `person`, `number`, `case_`, `formality`, `script` (for non-Latin orthography). `AllocutiveEntry` has `form`, `formality`, `gloss`. Eliminates 9 duplicate local type definitions across Fragment files.

### Changed
- **Fragments/{Hindi,Tamil,Korean,Japanese,Basque,Galician,Magahi,Maithili,Punjabi}/Pronouns.lean**: Refactored to import and use shared `Core.Pronouns.PronounEntry` and `Core.Pronouns.AllocutiveEntry`. Korean/Japanese `hangul`/`kanji` fields → `script : Option String`. All local `AllocMarkerEntry`/`AllocParticleEntry`/`AllocCliticEntry` → shared `AllocutiveEntry`. All existing verification theorems preserved.

## [0.155.0] - 2026-02-10

### Added
- **Phenomena/Agreement/PersonMarkingTypology.lean**: Cysouw (2009) paradigmatic structure of person marking typology. 8-cell `PersonCategory` scheme (3 singular + 5 group categories), `ParadigmaticStructure` as morpheme-class assignment, computed `SingularType` (Sa–Se), `FirstPersonComplexType` (Pa–Pe), `ExplicitnessLevel` hierarchy (10.7), `HorizHomophonyLevel` hierarchy (10.1–10.2). 12 language paradigms (Latin, English pronouns/inflection, Dutch, Spanish subjunctive, French, Mandara, Ilocano, Maká, Pirahã, Toda, Czech). ~40 verified theorems: all 5 singular types attested, all 5 FPC types attested, addressee inclusion implication (3.23), split inclusive implication (3.24), homophony implication (10.4), explicitness–form-count correlation, first person hierarchy (3.26). Bridges: `PersonCategory ↔ UD.Person` roundtrip, `UD.Person × UD.Number` mapping with `ud_conflates_incl_excl` theorem (Cysouw's central critique), English/Czech Fragment connections, inflectional-vs-independent explicitness correlation.

## [0.154.0] - 2026-02-10

### Changed
- **Core/NounCategorization.lean**: Added `ClassifierEntry.encodes` helper for uniform membership checks. Added `collectSemantics` to derive preferred semantic parameters from classifier inventories.
- **Fragments/Mandarin/Classifiers.lean**: Verification theorems now use `encodes` idiom instead of raw `.any`.
- **Fragments/Japanese/Classifiers.lean**: Same `encodes` idiom cleanup.
- **Fragments/Mandarin/Determiners.lean**: Replaced `classifierExample : Option String` with `typicalClassifier : Option ClassifierEntry`. All classifier-requiring quantifiers (每/几/两…都) now reference typed `ge` from the classifier lexicon. Bridge theorems: `requires_cl_has_typical`, `typical_classifier_is_default`.
- **Phenomena/NounCategorization/ → Phenomena/Agreement/NounCategorization.lean**: Merged Typology + Universals into a single file under `Phenomena.Agreement`, where noun categorization is framed as the cross-linguistic typological context for agreement phenomena (Aikhenvald's core diagnostic: agreement ↔ noun class, no agreement ↔ classifier). `preferredSemantics` derived from classifier lexicons via `collectSemantics`. `nominalMappingToClassifierType` returns `Option ClassifierType` — `argAndPred` (English) returns `none`. Standardized all membership checks to `.any (· == ...)` Bool idiom.

## [0.153.0] - 2026-02-10

### Added
- **Core/NounCategorization.lean**: Aikhenvald (2000) noun categorization typology. `ClassifierType` (9 types from Table 15.1), `SemanticParameter` (12 universal parameters from §11.1.1), `CategorizationScope`, `AssignmentPrinciple`, `SurfaceRealization`. `ClassifierEntry` structure with typed semantics replaces `Option String`. `NounCategorizationSystem` captures all 7 definitional properties (A–G).
- **Fragments/Mandarin/Classifiers.lean**: Typed Mandarin classifier lexicon — 11 entries (个/只/本/辆/朵/位/条/张/把/头/棵) with semantic parameters (animacy, shape, function, humanness, size, socialStatus). Verification: `ge_is_default`, `zhi_encodes_animacy`, `specific_classifiers_have_semantics`, `all_sortal`.
- **Fragments/Japanese/Classifiers.lean**: Typed Japanese classifier lexicon — 9 entries (つ/匹/冊/台/羽/本/人/枚/頭) with semantic parameters. Verification: `tsu_is_default`, `hiki_encodes_animacy`, `nin_encodes_humanness`, `specific_classifiers_have_semantics`.
- **Phenomena/NounCategorization/Typology.lean**: Cross-linguistic noun categorization typology mapping French (noun class), Mandarin (numeral CL), Japanese (numeral CL) to `NounCategorizationSystem`. Chierchia (1998) bridge: `nominalMappingToClassifierType`, `mandarin_chierchia_consistent`, `french_chierchia_consistent`. Cross-linguistic: `classifier_no_agreement_nounclass_agreement`, `bare_np_tracks_arg`, `blocking_tracks_mapping`.
- **Phenomena/NounCategorization/Universals.lean**: 12 Aikhenvald universals — U1 noun class requires agreement, U3 classifier assignment semantic, U5 animacy universal, U8 noun class small inventory, Table 10.17 interaction matrix (`interacts`), Greenberg (1972) classifier–number complementarity, default classifier universals.

### Changed
- **Fragments/Mandarin/Nouns.lean**: `NounEntry.classifier` changed from `Option String` to `Option ClassifierEntry`. `NP.classifierOverride` now `Option ClassifierEntry`. Added `NP.classifierForm` for string access. Semantic verification theorems: `animals_take_zhi`, `honorific_humans_take_wei`, `books_take_ben`, `vehicles_take_liang`, `mass_nouns_no_classifier`.
- **Fragments/Japanese/Nouns.lean**: Same typed classifier redesign as Mandarin. `NounEntry.classifier` now `Option ClassifierEntry`. Verification: `animals_take_hiki`, `birds_take_wa`, `books_take_satsu`, `vehicles_take_dai`, `people_take_nin`, `mass_nouns_no_classifier`.

## [0.152.0] - 2026-02-10

### Added
- **Phenomena/AuxiliaryVerbs/Typology.lean**: Anderson (2006) AVC inflectional pattern typology. 5-way `InflPattern` (auxHeaded/lexHeaded/doubled/split/splitDoubled), `AVCElement`, `HeadednessType`, `AVCFunction`. Key invariant: `semantic_head_always_lex`. Cross-linguistic data: English, Doyayo, Gorum, Jakaltek, Pipil. Bridges to `UD.VerbForm` (auxHeaded LV is nonfinite) and `FunctionWords.AuxType` (English modals are aux-headed).
- **Phenomena/AuxiliaryVerbs/Diagnostics.lean**: Huddleston (1976) NICE properties for English auxiliary classification. `NICEProfile` with `niceCount`, `isFullAux`, `isSemiAux`. Full auxiliaries: modals, be, have, do (all 4 NICE). Semi-auxiliaries: need, dare (2/4), ought (2/4). `niceToModule` bridge mapping each NICE property to the Phenomena module that formalizes it.
- **Phenomena/AuxiliaryVerbs/Selection.lean**: Be/have auxiliary selection in European perfects (Burzio 1986, Sorace 2000). `PerfectAux`, `TransitivityClass`, `SelectionRule`, `canonicalSelection`. Data: Italian, French, German, Dutch (split), English (have-only). `english_breaks_canonical` theorem. Bridge to VendlerClass: `vendlerClassToTypicalTransitivity` (achievement → unaccusative → selects *be*).
- **Phenomena/AuxiliaryVerbs/NegativeAuxiliaries.lean**: Anderson (2006) §1.7.2 negative auxiliary strategies. `NegStrategy` (negVerb/negAffix/negParticle). Key theorem: `negVerb_implies_auxHeaded` (negative verbs create aux-headed AVCs). Data: Finnish *ei*, Komi *oz*, Udihe *e-si* (negVerb); Kwerba *or-*, Tswana *ga/se* (negAffix); English *not* (negParticle).

## [0.151.0] - 2026-02-10

### Changed
- **CzechThreeWayNeg.lean**: Split into core (§§1–6: `NegPosition`, `Diagnostic`, `licenses`, scope generalizations) and **CzechThreeWayNeg/Typology.lean** (§§7–21: Romero bridge, Šimík CzechPQForm, VerbPosition, bias profiles, example data, corpus data). Core no longer imports BiasedPQ or Definiteness.
- **CzechThreeWayNeg/Typology.lean**: Replaced duplicate `EpistemicBias`/`EvidentialBias` enums with `OriginalBias`/`ContextualEvidence` from BiasedPQ. `czechBiasProfile` now takes Romero types directly. Replaced stringly typed `NegPosition.wordOrder : String` with `NegPosition.toVerbPosition : VerbPosition`. `CzechNegDatum.wordOrder` → `CzechNegDatum.verbPosition : VerbPosition`. Removed stipulative `czechStrictNegConcord := true`, tautological `czech_no_articles`, and `strict_nc_predicts_inner_only_nci` (the important theorem `only_inner_licenses_nci` remains in core). Corpus data (NahodouCorpusData, InterNPQUseCategory) moved here from Particles.lean.
- **Fragments/Czech/Particles.lean**: `requiresEvidentialBias` now dispatches on `ParticleSemantics` + diagnostic status instead of string form comparison. Corpus data sections moved to Typology.lean.
- **Phenomena/Questions/SlavicPQStrategies.lean**: Removed unused CzechThreeWayNeg import.

## [0.150.0] - 2026-02-10

### Added
- **Phenomena/StankovaSimik2024/Data.lean**: Experimental data from Staňková & Šimík (FASL 32 / JSL 33) — three naturalness judgment experiments on Czech negation in PQs. `CLMMEffect` structure stores z-values (×1000). Main experiment (2×2×2, 75 participants): V1 PPIs preferred (`v1_indefinite`, z = −15.674), V1 context-insensitive (`v1_context`, n.s.), nonV1 context-sensitive (`nonV1_context`, z = 8.674), nonV1 NCIs preferred (`nonV1_indefinite`, z = 6.208). náhodou subexperiment: PPIs preferred (`nahodou_indefinite`, z = −12.845), confirming FALSUM requirement. copak subexperiment: biased contexts preferred (`copak_context`, z = 9.372), confirming evidential bias requirement. Bridge theorems: `v1_confirms_outer_neg`, `nonV1_confirms_inner_default`, `context_asymmetry`, `epistemic_vs_evidential_coherence`. Czech FALSUM broader than English: positive-evidence subexperiment (median 6/7).
- **Phenomena/Negation/CzechThreeWayNeg.lean**: `VerbPosition` enum (V1/nonV1) from Staňková & Šimík §2/§4. `availableReadings` (V1 → outer only; nonV1 → inner/medial/outer), `defaultReading` (V1 → outer; nonV1 → inner). `requiresContextualEvidence` (V1 = false; nonV1 = true). Bridge theorems connecting VerbPosition to PQForm, CzechPQForm, and bias strength: `v1_default_is_hiNQ`, `nonV1_default_is_declNPQ`, `context_tracks_bias_strength`, `czech_falsum_broader_than_english`.
- **Fragments/Czech/Particles.lean**: *copak* particle entry with new `evidentialConflict` semantics variant. `requiresEvidentialBias` function contrasting náhodou (false, FALSUM-tied) vs copak (true, evidential bias). `nahodou_copak_opposite_context` theorem. `copak_nahodou_different_semantics` theorem.

## [0.149.0] - 2026-02-10

### Added
- **Fragments/Czech/Determiners.lean**: Czech polarity-sensitive determiners — *žádný* (NCI), *nějaký* (PPI), *každý*, *některý*. `compatibleWith` bridges to `CzechThreeWayNeg.licenses`. Key theorems: `zadny_nejaky_complementary` (NCI/PPI have exactly opposite distributions), `nci_ppi_identifies_inner` (NCI+¬PPI uniquely picks out inner negation).
- **Fragments/Czech/Particles.lean**: Czech diagnostic particles — *náhodou* (ordering source modifier, outer only), *ještě* (temporal endpoint, inner only), *fakt* (veridical emphasis, inner+medial), *vůbec* (NPI), *snad* (razve family). `compatibleWith` bridges to `CzechThreeWayNeg.licenses`. Identification theorems: `nahodou_identifies_outer`, `jeste_identifies_inner`, `fakt_plus_no_jeste_identifies_medial`. Šimík (2024) corpus data for *náhodou* (100 PQ occurrences, all negated, all indefinites were PPIs). InterNPQ use categories with distribution: explanation-seeking 40%, relevance 20%, hope 20%, belief 14%.
- **Phenomena/Questions/SlavicPQStrategies.lean**: Cross-Slavic PQ strategy typology (Šimík 2024 §4.1). 10 Slavic languages with `SlavicPQProfile`: Czech/Slovak/Upper Sorbian (verb movement), Slovenian (*ali*), Ukrainian (*čy*), Polish (*czy*), Serbian (*da li*), Macedonian (*dali*), Bulgarian (*li*), Russian (intonation/li). `verbMovement_implies_declPQ` generalization. Bias particles: Russian *razve*, Czech *náhodou*/*copak*, Serbian *zar* — with `razve_nahodou_differ` theorem.
- **IntensionalSemantics/Modal/BiasedPQ.lean**: FALSUM^CZ (Šimík 2024 eq. 44) — weaker Czech variant using epistemic *possibility* rather than belief. `standard_falsum_entails_CZ_definedness`. *Náhodou* as ordering source modifier with `nahodou_widens_domain` theorem proving that loosening the ordering source preserves FALSUM^CZ definedness.
- **Phenomena/Negation/CzechThreeWayNeg.lean**: Šimík's 2×2 `CzechPQForm` grid (InterPPQ/InterNPQ/DeclPPQ/DeclNPQ), `CzechPQForm.toPQForm` bridge to Romero, `NegPosition.toCzechPQForm` mapping. Table 2 Czech bias profiles (`czechBiasProfile : EvidentialBias → EpistemicBias → List CzechPQForm`) with per-cell verification: `interPPQ_is_default`, `interNPQ_broad_distribution`, `decl_polarity_matches_evidence`.

## [0.148.0] - 2026-02-10

### Added
- **IntensionalSemantics/Modal/BiasedPQ.lean**: Cross-linguistic framework for biased polar questions (Romero 2024). PQ form typology (`PosQ`/`LoNQ`/`HiNQ`), two bias dimensions (original speaker bias + contextual evidence bias), Romero's Tables 1–2 as compatibility matrices. VERUM and FALSUM operators built on existing Kratzer + CommonGround infrastructure. Staňková (2026) evidential bias modal □_ev as `EvidentialBiasFlavor` (just a `KratzerParams` instantiation). Inner/medial scope interactions with `inner_entails_medial` theorem (D axiom). Focus requirement on FALSUM connecting to InformationStructure.
- **Phenomena/Negation/CzechThreeWayNeg.lean**: Czech three-way negation distinction in polar questions (Staňková 2026). `NegPosition` (inner/medial/outer), Table 1 licensing matrix (`licenses : NegPosition → Diagnostic → Bool`) with 15 per-cell verification theorems. Signature uniqueness proof. Scope generalizations: `only_inner_licenses_nci`, `only_outer_licenses_nahodou`. `NegPosition.toPQForm` mapping Czech positions to Romero's PQ typology (outer→HiNQ, inner/medial→LoNQ). Per-example Romero classification (7 theorems) and bias-prediction bridges connecting each Czech example to Romero's Tables 1–2. Key cross-linguistic result: `czech_refines_loNQ` proving that Czech inner/medial split reveals finer structure within Romero's LoNQ category (same PQ form, different bias strength, different diagnostic signatures).

## [0.147.0] - 2026-02-10

### Added
- **Blog**: "Generalized Quantifiers in Three Layers" — pedagogical post covering GQ theory, the three-layer architecture (Core → TruthConditional → Fragments), van Benthem's "Aristotle reversed" characterization, and the Zwarts bridge.

### Changed
- **Core/Quantification.lean**: Reorganized into definitions-first layout: §1 property definitions (grouped by B&C, P&W, van Benthem, Mostowski), §2 operations (duality, Boolean algebra, type shifts), §3 Mathlib bridge, §4–§8 theorems (duality, symmetry/strength, Boolean closure, type ⟨1⟩, van Benthem characterization). No content changes.
- **DynamicSemantics/PLA/Quantifiers.lean**: Added cross-reference docstring connecting PLA's Set-based `GQRel` to Core's Bool-based `GQ`, explaining why both representations exist.

## [0.146.0] - 2026-02-10

### Added
- **Core/Quantification.lean**: Van Benthem (1984) relational properties — `QTransitive`, `QAntisymmetric`, `QLinear`, `QuasiReflexive`, `QuasiUniversal`, `AlmostConnected`. `Variety` (VAR). Uniqueness theorem `vanBenthem_refl_antisym_is_inclusion` (Thm 3.1.1: "all" is the only reflexive antisymmetric quantifier). Zwarts bridge theorems: `zwarts_refl_trans_scopeUp`, `zwarts_refl_trans_restrictorDown` (Thm 4.1.1), `zwarts_sym_scopeUp_quasiRefl`, `zwarts_sym_scopeDown_quasiUniv` (Thm 4.1.3). `DoubleMono` type (§4.2 Square of Opposition). `RightContinuous` + `scopeUpMono_rightContinuous` (§4.3). `Filtrating` (§4.4). `QuantityInvariant` (model-agnostic QUANT).
- **TruthConditional/Determiner/Quantifier.lean**: Concrete relational proofs — `every_transitive`, `every_antisymmetric`, `some_quasi_reflexive`, `no_quasi_universal`. Restrictor monotonicity: `every_restrictor_down` (from Zwarts bridge), `some_restrictor_up`, `no_restrictor_down`. Double mono classification: `every_doubleMono` (↓MON↑), `some_doubleMono` (↑MON↑), `no_doubleMono` (↓MON↓), `notAll_doubleMono` (↑MON↓). `every_filtrating`.
- **Fragments/English/Determiners.lean**: `InferentialClass` type (van Benthem §3.3 Square of Opposition corners). `QuantityWord.inferentialClass`, `QuantityWord.doubleMono` classifications. Bridge theorems: `all_inferential_bridge`, `some_inferential_bridge`, `none_inferential_bridge`, `all_doubleMono_bridge`, `some_doubleMono_bridge`, `none_doubleMono_bridge`.
- **Phenomena/Quantification/Universals.lean**: Van Benthem impossibility results — `no_asymmetric_quantifiers` (Thm 3.2.1), `no_strict_partial_order_quantifiers`, `no_euclidean_quantifiers` (Thm 3.2.3). `aristotle_reversed_square` (§3.3). `conservativeQuantifierCount` (Thm 5.4: 2^((n+1)(n+2)/2) conservative quantifiers on n individuals).

## [0.145.0] - 2026-02-10

### Added
- **Core/Quantification.lean**: Boolean GQ algebra — `gqMeet`, `gqJoin` (K&S §2.3 D_Det closure). Boolean closure of conservativity: `conservative_outerNeg`, `conservative_gqMeet`, `conservative_gqJoin` (K&S PROP 1 / Conservativity Theorem). De Morgan laws: `outerNeg_gqJoin`, `outerNeg_gqMeet` (K&S eq. 26). Monotonicity closure: `scopeUpMono_gqMeet`, `scopeDownMono_gqMeet`, `scopeUpMono_gqJoin` (K&S PROP 6). Adjectival restriction: `adjRestrict`, `conservative_adjRestrict` (K&S PROP 3), `scopeUpMono_adjRestrict`, `scopeDownMono_adjRestrict` (K&S PROP 5).
- **TruthConditional/Determiner/Quantifier.lean**: K&S Existential det classification (§3.3, G3) — `some_existential`, `no_existential` (existential dets), `every_not_existential`, `most_not_existential` (non-existential, proved by toyModel witnesses). `some_existential_weak_bridge` (third independent path to weak/strong).
- **Fragments/English/Determiners.lean**: `both`/`neither` entries with metadata. `both_sem`/`neither_sem` compositional GQ denotations via `gqMeet`. `both_conservative`, `neither_conservative`. Bridge theorems: `both_neither_mono_duality`, `neither_decreasing`, `both_positive_strong_on_nonempty`.
- **Fragments/Japanese/Determiners.lean**: `ryoho` (両方 ryōhō "both") — universal dual, strong. `ryoho_universal_strong`.
- **Fragments/Mandarin/Determiners.lean**: `liang_dou` (两…都 liǎng…dōu "both") — universal dual, strong, requires classifier. `liang_dou_universal_strong`, `liang_dou_requires_cl`.
- **Phenomena/Quantification/Typology.lean**: Updated Mandarin/Japanese inventories to 7 entries. `east_asian_have_dual_universal`.

## [0.144.0] - 2026-02-10

### Added
- **Core/Quantification.lean**: Extension (EXT) — completes the "big three" alongside CONS and ISOM. Van Benthem (1984) characterization: `vanBenthem_cons_ext` (CONS+EXT ↔ LivesOn). `extension_trivial`: EXT is a design theorem for universe-free `GQ α`.
- **TruthConditional/Determiner/Quantifier.lean**: FiniteModel Extension spectator-irrelevance proofs (`every_ext_spectator`, `some_ext_spectator`, `no_ext_spectator`, `most_ext_spectator`). Denotation-level Extension: `every_sem_extension` (every(R,S) = filter(R).all S), `some_sem_extension`, `no_sem_extension`, `most_sem_extension` — compose spectator irrelevance with actual GQ denotations. `every_positive_strong` (P&W Ch.6).
- **Fragments/English/Determiners.lean**: LAA bridge theorems — `every_laa_bridge` (gqDenotation identity + LeftAntiAdditive), `none_laa_bridge` (gqDenotation identity + LeftAntiAdditive + ScopeDownwardMono). Connects Fragment denotations to NPI licensing.
- **Phenomena/Polarity/Exceptives.lean**: Bridge from Fragment QForce to but-exceptive licensing (von Fintel 1993). `qforceToExceptiveType`, `fragment_exceptive_bridge`, `universal_qforce_partition`. Now imports `Fragments.English.Determiners`.
- **Barker2011.lean**: Bridge connecting possessives to type ⟨1⟩ GQ framework (NPQ). `possessiveAsNPQ` (existential interpretation), `possessive_individual_eval`. Now imports `Core.Quantification`.
- **Phenomena/Quantification/Universals.lean**: `extension_universal` added to universal list. Thread map updated with Extension and PositiveStrong cross-references.

## [0.143.0] - 2026-02-10

### Added
- **Phenomena/Quantification/Examples.lean** (NEW): End-to-end Fragment test-drive. Phenomena-level scenario (4 entities, 4 predicates) composed with Fragment denotations. Tier 1: there-insertion acceptability from `Strength`. Tier 2: 8 truth-value judgments (all `rfl`). Tier 3: monotonicity-driven entailments (`some_passed_entails_laughed`, `no_laughed_entails_no_passed`). Tier 4: scalar distinctness witnesses.
- **Phenomena/Quantification/Typology.lean** (NEW): Cross-linguistic quantifier inventories for English, Mandarin, Japanese. Derived from Fragment entries. `QuantifierInventory` structure with per-language verification (size, weak/strong split, article-less). Cross-linguistic universals: `all_have_weak_strong`, `all_have_universals`, `no_articles_east_asian`, `conservativity_crosslinguistic`.
- **Phenomena/Quantification/Universals.lean**: Added P&W Ch.5-6 universals — symmetry ↔ there-insertion (`weak_are_symmetric`, `strong_not_symmetric`), LAA → NPI licensing (`laa_licenses_npis`), positive-strong monotonicity (`positive_strong_determiners_upward_monotone`). Thread map updated with v0.142.0 proof cross-references.

## [0.142.0] - 2026-02-10

### Added
- **Core/Quantification.lean**: P&W Ch.6 Tier 1 properties — `CONS2` (second conservativity), `Existential` (there-insertion characterization), `conserv_symm_iff_int` (CONSERV → SYMM ↔ INT, the central equivalence), `PositiveStrong`, `NegativeStrong`, `symm_not_positive_strong` (P&W Ch.6 Fact 7). `LeftAntiAdditive`, `RightAntiAdditive` (P&W §5.9).
- **TruthConditional/Determiner/Quantifier.lean**: Symmetry proofs (`some_symmetric`, `no_symmetric`, `every_not_symmetric`). Intersectivity via bridge (`some_intersective`, `no_intersective` — derived from CONSERV+SYMM, not proved directly). Left anti-additivity (`every_laa`, `no_laa`).
- **Fragments/English/Determiners.lean**: Symmetry bridges (gap G) — `some_symmetry_bridge` (weak ∧ symmetric), `none_symmetry_bridge` (weak ∧ symmetric), `every_not_symmetric_bridge` (strong ∧ ¬symmetric). Verifies P&W Ch.6: weak ↔ symmetric under CONSERV.
- **Fragments/Mandarin/Determiners.lean**: Cross-linguistic quantifier fragment — 6 entries (měi, suǒyǒu, yǒu-de, méi-yǒu, jǐ, dà-bùfèn) with `MandarinQuantEntry` structure including classifier requirements. Per-datum verification theorems.
- **Fragments/Japanese/Determiners.lean**: Cross-linguistic quantifier fragment — 6 entries (subete, dono-N-mo, dare-ka, dare-mo, nan-nin-ka, hotondo) with `JapaneseQuantEntry` structure including indeterminate/particle morphology and floating quantifier properties. `particle_force_shift` theorem (ka→∃, mo→∀).

## [0.141.0] - 2026-02-10

### Added
- **Core/Quantification.lean**: Peters & Westerståhl Ch.0-3 infrastructure — `innerNeg_down_to_up` (missing duality theorem, gap F), involution theorems (`outerNeg_involution`, `innerNeg_involution`, `dualQ_involution`), restrictor duality (`outerNeg_restrictorUp_to_down`, `outerNeg_restrictorDown_to_up`). Type ⟨1⟩ quantifiers: `NPQ α`, `restrict`, `LivesOn`, `conservative_iff_livesOn`. Montagovian individuals: `individual`, `individual_upward_closed`, `individual_meet_closed`. Co-property monotonicity: `co_property_mono`.
- **TruthConditional/Determiner/Quantifier.lean**: Concrete duality square (P&W §1.1.1) — `innerNeg_every_eq_no`, `dualQ_every_eq_some`, `outerNeg_some_eq_no`. Instantiates `every ←innerNeg→ no ←outerNeg→ some ←dualQ→ every`.
- **Fragments/English/Determiners.lean**: Per-datum bridge theorems (gap G) — monotonicity bridges (`every_mono_bridge`, `some_mono_bridge`, `none_mono_bridge`, `all_mono_bridge`) verifying enum metadata matches semantic property. Conservativity bridges (`all_conservative_bridge`, `some_conservative_bridge`, `none_conservative_bridge`, `most_conservative_bridge`) verifying `gqDenotation` identity and `Conservative` property.

## [0.140.0] - 2026-02-10

### Added
- **Core/Quantification.lean**: Extracted model-agnostic GQ properties from `TruthConditional.Determiner.Quantifier` into `Core.Quantification`. Generic over `{α : Type*}`: `GQ α` abbreviation, `Conservative`, `ScopeUpwardMono`, `ScopeDownwardMono`, `IntersectionCondition`, `QSymmetric`, `RestrictorUpwardMono`, `RestrictorDownwardMono`, `outerNeg`, `innerNeg`, `dualQ`. Bridge lemmas `scopeUpMono_iff_monotone`, `scopeDownMono_iff_antitone` (no Preorder hacks needed). Duality theorems: `outerNeg_up_to_down`, `outerNeg_down_to_up`, `innerNeg_up_to_down`, `intersection_conservative_symmetric`.

### Changed
- **TruthConditional/Determiner/Quantifier.lean**: Deleted `GQProperties` section (definitions, private Preorder instances, bridge lemmas, duality operations). Now imports and opens `Core.Quantification`. Retains `FiniteModel`, denotations, and `FiniteModelProofs`.
- **Phenomena/Conditionals/Studies/RamotowskaEtAl2025.lean**: Imports `Fragments.English.Determiners`. `Quantifier.isStrong` now derives from canonical `Strength` enum via `Quantifier.strength`.
- **Core/Duality.lean**, **Fragments/English/Determiners.lean**, **Phenomena/Quantification/Universals.lean**: Updated docstring cross-references to point to `Core.Quantification`.

## [0.139.0] - 2026-02-09

### Added
- **TruthConditional/Determiner/Quantifier.lean**: B&C §4.11 duality operations — `outerNeg`, `innerNeg`, `dualQ`. Proved `outerNeg_up_to_down`, `outerNeg_down_to_up` (Corollary 9: negation reverses scope monotonicity), `innerNeg_up_to_down`. B&C §4.3–4.8: `IntersectionCondition`, `QSymmetric`, `intersection_conservative_symmetric` (Theorem C5). `RestrictorUpwardMono` (persistence), `RestrictorDownwardMono`.
- **Fragments/English/Determiners.lean**: `Strength` enum (weak/strong, B&C Table II). Added `strength` field to `QuantifierEntry`; annotated every/each/all/most/the/this/that/these/those as strong, rest as weak.
- **Phenomena/Quantification/Universals.lean**: B&C universals U7 (`strong_implies_monotone`), U8 (`persistent_implies_weak_and_up`). Verification: `weak_there_insertion`, `strong_no_there_insertion`.

### Changed
- **Sentence/Entailment/Monotonicity.lean**: Refactored to delegate `every`/`some'`/`no` to canonical `every_sem`/`some_sem`/`no_sem` via `entailmentModel` bridge. Local defs are now `abbrev`s.

## [0.138.0] - 2026-02-09

### Added
- **TruthConditional/Determiner/Quantifier.lean**: Barwise & Cooper (1981) semantic universals — `Conservative`, `ScopeUpwardMono`, `ScopeDownwardMono`, `Quantity` (Mostowski 1957 isomorphism closure), `SatisfiesUniversals`. Proved conservativity for every/some/no/most, scope monotonicity for every (↑), some (↑), no (↓). Non-conservative counterexample `m_sem` with proof `m_not_conservative`. Numerical determiners: `at_least_n_sem`, `at_most_n_sem`, `exactly_n_sem`.
- **Fragments/English/Determiners.lean**: Imported `Quantifier.lean` as canonical source of truth. `QuantityWord.gqDenotation` maps fragment entries to compositional GQ denotations. `NumericalDetEntry` structure with `atLeast`, `atMost`, `exactlyN`, `moreThan`, `fewerThan`. Thread-map docstring linking Fragment → Theories → Phenomena → Conjectures.
- **Core/Conjectures.lean**: `simplicity_explains_universals` and `monotonicity_strongest_predictor` — van de Pol et al. (2023) claim that B&C-satisfying quantifiers have lower Lempel-Ziv / MDL complexity.
- **Phenomena/Quantification/Universals.lean**: Empirical findings from Barwise & Cooper (1981) and van de Pol et al. (2023). `MonotonicitySimplicity`, `ConservativitySimplicity`, `QuantitySimplicity`, `UniversalsSimplicityRanking`. Verification: `english_quantifiers_mostly_monotone`, `half_nonmonotone`, `some_all_scale_upward`.

### Changed
- **Sentence/Entailment/Monotonicity.lean**: Added note pointing to canonical GQ denotations in `Quantifier.lean` and thread through `Fragments.English.Determiners.QuantityWord.gqDenotation`.

## [0.137.0] - 2026-02-09

### Added
- **Core/ModalLogic.lean**: `ForceFlavor.cartesianProduct` — list infrastructure for constructing modal meanings from forces × flavors, moved out of Typology.lean so Fragments can use it without importing Theories.
- **Fragments/English/FunctionWords.lean**: `modalMeaning` field on `AuxEntry` (defaults to `[]` for non-modals). 9 English modals annotated with force-flavor meanings via `cartesianProduct` following Kratzer (1981), Palmer (2001). Renamed `to` → `to_` to avoid conflict with Mathlib keyword.
- **IntensionalSemantics/Modal/Typology.lean**: `ModalInventory.fromAuxEntries` — constructs a modal inventory from Fragment auxiliary entries, filtering to non-empty modal meanings. Local `cartesianProduct` is now an `abbrev` for the Core definition.
- **Phenomena/Modality/Typology.lean**: English modal inventory derived from the Fragment (single source of truth). `english_all_iff`, `english_size`. Updated cross-linguistic summary to 9 languages (7/9 perfect IFF).

## [0.136.0] - 2026-02-09

### Changed
- **Core/ModalLogic.lean**: Added `LawfulBEq` instances for `ModalForce` and `ModalFlavor`, providing `beq_self_eq_true` and `eq_of_beq` for downstream proofs.
- **IntensionalSemantics/Modal/Typology.lean**: Proved `sav_implies_iff` and `cartesianProduct_satisfies_iff` (both previously `sorry`). Added `cartesianProduct` as the primitive force-flavor meaning constructor with `mem_cartesianProduct` membership lemma, replacing the duplicated `kratzerMeaning`/`kratzerVariableForceMeaning`. Unified SAV proofs into `cartesianProduct_singleton_force_satisfies_sav` and `cartesianProduct_singleton_flavor_satisfies_sav` (both proved via `mem_cartesianProduct`). Deleted `satisfiesSAV'` and its sorry'd equivalence proof. Kratzer-Typology bridge: `FlavorAssignment`, `canonicalAssignment`. Imports Kratzer.lean.
- **IntensionalSemantics/Modal/Kratzer.lean**: Added `.flavorTag` mapping each flavor structure (`EpistemicFlavor`, `DeonticFlavor`, `BouleticFlavor`, `TeleologicalFlavor`) to the theory-neutral `ModalFlavor` enum. Added `.toKratzerParams` extracting `KratzerParams` from each flavor structure.

## [0.135.0] - 2026-02-09

### Added
- **Core/ModalLogic.lean**: `ModalFlavor` (epistemic/deontic/circumstantial), `ForceFlavor` (force-flavor pair), `ForceFlavor.universe` (all 6 meaning points). Theory-neutral vocabulary for cross-linguistic modal typology.
- **IntensionalSemantics/Modal/Typology.lean**: Independence of Force and Flavor (IFF) universal (`satisfiesIFF`) and Single Axis of Variability (SAV) universal (`satisfiesSAV`) from Steinert-Threlkeld, Imel, & Guo (2023). `sav_implies_iff` (SAV strictly stronger than IFF). `iff_not_implies_sav` (IFF allows both-axis variation). `cartesian_product_satisfies_iff` (Kratzer's independent parameterization → IFF). `ModalExpression`/`ModalInventory` structures with `allIFF`, `iffDegree`, `hasSynonymy`. Bridge from Kratzer (1981) to typological universals.
- **Phenomena/Modality/Typology.lean**: 8 cross-linguistic modal inventories (Tlingit, Javanese, Gitksan, Korean, Modern Greek, Mandarin, Dutch, Hungarian) from the Database of Modal Typology (Guo et al. 2022), mapped to the 2×3 force-flavor space following Imel, Guo, & Steinert-Threlkeld (2026). Per-expression IFF verification via `native_decide`. Verified: 6/8 languages have perfect IFF degree. Greek and Dutch have non-IFF modals (Prepei, zou/zouden...kunnen). Gitksan variable-force modals satisfy IFF but not SAV. Paper's three main empirical results stated as axioms/theorems.

## [0.134.0] - 2026-02-09

### Added
- **NeoGricean/Exhaustivity/Chierchia2013.lean**: Core theorems from Chierchia (2013) *Logic in Grammar* with real proofs (no sorry). Free Choice via double exhaustification (`free_choice_forward`/`free_choice_backward`: Exh(Exh(◇(p∨q))) ↔ ◇p∧◇q). SI–NPI Generalization (`si_vacuous_in_de`: SIs contradictory in DE contexts). Domain widening reversal (`widening_strengthens_in_de`/`widening_weakens_in_ue`: Kadmon & Landman's NPI licensing). Intervention disrupts DE (`intervention_negation_not_de`: non-monotone operators break DE chains). Scalar reversal (`entailment_reversal_in_de`/`weak_is_strong_in_de`). FC duality (`fc_duality_forward`: uniform derivation for any modal satisfying distributivity over disjunction). Polarity composition grounded in Mathlib (`double_negation_ue`, `ue_under_de`, `de_under_ue`, `ue_under_ue`). Maximize Strength = exhaustification bridge (`maximize_strength_eq_exhIE`).

### Removed
- **DynamicSemantics/BilateralUpdate/**: Deleted duplicate directory (`Basic.lean`, `FreeChoice.lean`). The canonical Elliott & Sudo (2025) implementation lives in `DynamicSemantics/BUS/`. `BilateralUpdate/` was an older standalone version with near-identical content; its sole consumer (`Comparisons/FreeChoice/Compare.lean`) now imports from `BUS/` instead.

### Changed
- **CLAUDE.md**: Clarified that `/-! ... -/` module docstrings must come after all `import` statements (Lean requires imports first).

## [0.133.0] - 2026-02-09

### Added
- **IntensionalSemantics/SituationSemantics/Elbourne.lean**: Formalization of Elbourne (2013) "Definite Descriptions" (OUP). `SituationFrame` ontology (D_s with ≤ partial order, isWorld, isMinimal). `the_sit`: situation-relative ⟦the⟧ — the core Fregean lexical entry with presupposition relativized to situations. `the_sit'`/`the_sit_at_world_eq_the_uniq_w`: proves existing `the_uniq_w` is a special case. `attributive_is_the_sit_bound`: Donnellan's attributive = `the_sit'`. Referential/attributive distinction derived (not ambiguity) via `SitVarStatus` (.free/.bound). `useModeToSitVar` roundtrip isomorphism bridging to Donnellan.lean. Donkey anaphora via minimal situations (`donkey_uniqueness_from_minimality`). De re/de dicto via situation scope. Existence entailments (Ch 8 data). Incomplete definites via `IncompletenessSource`. Pronouns = definite descriptions (`NPDeletionSource`, `PronounAsDefinite`, Voldemort phrases). Bridges to English fragment: `english_the_is_the_sit`, `english_the_is_uniqueness`, `english_demonstratives_are_definite`, `pronoun_is_definite_article`, per-entry classification theorems for it/he/she. Bridge to `Core/Definiteness.lean`: `presupTypeToSitDescription` maps weak/strong to situation size. Bridge to Donnellan: `useModeToSitVar`/`useMode_sitVar_roundtrip`. Situation binding operators (ς_i, Σ_i, σ_i) and situation variables (free/bound). 8 unified phenomena enumerated with `UnifiedPhenomenon`. §15 QUD–Situation bridge: `qudRelevantSituation` defines Q-relevant situation at a world (minimal part resolving QUD); conjectures `situation_pronoun_tracks_qud` (discourse-bound situation = QUD-relevant situation) and `qud_refinement_monotone` (finer QUD ⟹ larger situation).

## [0.132.0] - 2026-02-09

### Changed
- **Eliminate redundant Bool encodings in Core/Definiteness.lean**: Removed `requiresStrongArticle` (Bool) — duplicate of `useTypeToPresupType` (DefPresupType). Removed `bridgingArticle` (Bool) — replaced by `bridgingPresupType : BridgingSubtype → DefPresupType`. Removed 4 trivial aliases (`schwarz_weak_semantics`, `schwarz_strong_semantics`, `partWholePresupType`, `relationalPresupType`) and 3 theorems that only existed to prove the Bool/DefPresupType encodings agree (`schwarz_mapping_consistent`, `bridging_part_whole_is_uniqueness`, `bridging_relational_is_familiarity`). Updated `PronounTypology.lean` `semantic_mapping_parallel` to use `useTypeToPresupType` directly.

## [0.131.0] - 2026-02-09

### Changed
- **Consolidate definiteness types into Core/Definiteness.lean**: Extracted all lightweight definiteness vocabulary from Phenomena/ into a new zero-import Core/ module. `DefPresupType` (.uniqueness/.familiarity), `ArticleType` (Schwarz 2009), `DefiniteUseType` (Hawkins 1978), `BridgingSubtype` (.partWhole/.relational), `WeakArticleStrategy`, `Definiteness` (.indefinite/.definite), plus mappings (`useTypeToPresupType`, `articleTypeToAvailablePresup`, `bridgingPresupType`). Eliminated duplicate `PresupType` (Bridging.lean) and `BridgingType` (Bridging.lean). Fixed inverted Theories→Phenomena dependency: PronounTypology.lean and Bridging.lean now import from Core/Definiteness.lean instead of defining their own types. Definite.lean imports Core/Definiteness.lean instead of Phenomena/ files.

## [0.130.0] - 2026-02-09

### Added
- **TruthConditional/Determiner/Definite.lean**: Semantics of definiteness — the missing `⟦the⟧`. `the_uniq`: uniqueness-based definite (Russell/Strawson, Schwarz weak article) with existence+uniqueness presupposition via `PrProp`. `the_fam`: familiarity-based definite (Heim/Kamp, Schwarz strong article) with discourse-salience presupposition via `DiscourseContext`. Bridge theorems: `the_uniq_eq_definitePrProp` (= Donnellan attributive), `the_uniq_presup_iff_iota` (= Partee ι), `qforceToPresupType`/`qforceToDefiniteness` (Fragments `QForce`).

## [0.129.0] - 2026-02-09

### Added
- **Phenomena/Anaphora/PronounTypology.lean**: Patel-Grosz & Grosz (2017) PER/DEM pronoun classification. `PronounClass` (.per/.dem), `ArticleType` (Schwarz 2009), `PronounStrength` (Cardinaletti & Starke 1999), `DEMLicensingContext`. `PronounSystemDatum` with 11 languages. `PronounComplexityProfile` gradient measures (following WordOrder/Gradience.lean pattern). Verified generalizations: Minimize DP!, DEM⊂PER implicational universal, article-D-layer correlation, DEM productivity tracks overt strong articles. Schwarz (2013) §F: `DefiniteUseType` (Hawkins 1978), `BridgingSubtype` (part-whole vs producer), `SchwarzArticleDatum` for 7 languages (German, Fering, Akan, Mauritian Creole, Lakhota, Hausa, Haitian Creole), `requiresStrongArticle` mapping, bridging-split theorem, bare-nominal strategy. Bridges to Coreference.lean (AnaphorType), Demonstratives.lean (D_deix = demonstration), DirectReference.lean (PER = rigid), Schwarz article ↔ PG&G D-layers.

## [0.128.0] - 2026-02-09

### Added
- **Crosslinguistic pronoun & allocutive fragments** for 9 languages: Basque, Magahi, Korean, Japanese, Tamil, Galician, Hindi, Maithili, Punjabi. Each `Fragments/{Lang}/Pronouns.lean` contains typed 2nd-person pronoun entries with formality levels, allocutive marker entries (suffixes/particles/clitics), verb agreement examples, and per-datum verification theorems. Theory-neutral (imports only `Core.Basic`).
- **Allocutivity.lean bridge section** (Section E): `formalityToHonLevel` (Nat → HonLevel) bridging fragment formality to theory types. Per-language bridge theorems verifying fragment data consistency (all 2nd-person, correct level counts).

## [0.127.0] - 2026-02-09

### Added
- **Minimalism/Phenomena/SpeechActs.lean**: Speas & Tenny (2003) configurational point-of-view roles. `PRole` (speaker/hearer/seatOfKnowledge), `SAPMood` (4 moods from 2×2 feature matrix), `deriveMood`, `seatOfKnowledge`, `resolveRole`/`resolveRoleInMood` (KContext grounding). `personToRole`/`pronounDiscourseRole` (person→P-role mapping, theory-side). Bridge theorems: mood exhaustivity, seat of knowledge by mood, KContext grounding, SA phase head, person-to-role verification.
- **IntensionalSemantics/Reference/Kaplan.lean**: `pronYou` — "you" picks out `KContext.addressee` (parallel to `pronI` for agent). `pronYou_directlyReferential` theorem.

## [0.126.0] - 2026-02-09

### Added
- **Minimalism/Core/Basic.lean**: `Cat.Fin` (finiteness, Rizzi 1997 split-CP) and `Cat.SA` (speech act head, Speas & Tenny 2003) constructors. Connects narrow syntax to QuestionSemantics/LeftPeriphery SAP analysis.
- **Core/Context.lean**: `addressee : E` field on `KContext` (Speas & Tenny 2003). Extends the Kaplanian context tuple to model the hearer as a discourse participant.
- **Minimalism/Core/Agree.lean**: `HonLevel` (.nh/.h/.hh) — relational honorific levels (Alok 2020, Portner et al. 2019). `FeatureVal.hon` — [iHON] as an Agree-checkable feature. `featuresMatch` extended for hon.
- **Minimalism/Core/Phase.lean**: `isSAPhaseHead` — SA as a phase head (Speas & Tenny 2003). SAP is the highest phase; allocutive probing from SA is root-only.
- **Phenomena/Honorifics/Data.lean**: Theory-neutral crosslinguistic allocutive agreement data (9 languages: Basque, Magahi, Korean, Japanese, Tamil, Galician, Hindi, Maithili, Punjabi). `AMType`, `Embeddability`, `HonDomain`, `AllocDatum`. Verification theorems: `rootOnly_languages_exist`, `freelyEmbed_languages_exist`, `all_have_verbal`, `all_have_tv`.
- **Minimalism/Phenomena/Allocutivity.lean**: Allocutive agreement as standard Agree (Alok & Bhalla 2026). `AllocAgree` structure. `predictEmbeddability` (SA → rootOnly, Fin → freelyEmbed). Per-datum verification via `all_correctly_predicted`. `HonRelation`, `HonP` (nominal [iHON] projection). Bridge theorems: AA = Agree, SA/Fin embeddability predictions, per-language verification (Basque/Magahi/Korean), SAP parallel to question particle typology, pragmatic parallel to Yoon et al. 2020 social utility.

### Changed
- **IntensionalSemantics/Reference/Basic.lean**: `Context.toKContext` takes `addr : E` parameter for new `KContext.addressee` field.
- **IntensionalSemantics/Reference/KaplanLD.lean**: `LDStructure.cAddressee` field added. `toKContext` updated.

## [0.125.0] - 2026-02-09

### Changed
- **Minimalism Core reorganization**: Merged `Core/SyntacticObjects.lean` + `Core/Containment.lean` → new `Core/Basic.lean` (true foundation module). Merged old `Core/Basic.lean` (`MinimalistGrammar`, `MinDerivation`, `Grammar` instance) into `Formal/Workspace.lean`. Updated all imports (Labeling, FreeMagmaEquiv, Interface, RelativeClauses, FromFragments, Derivations, Linglib.lean). Net: 3 files → 1 file (Basic.lean), plus Workspace.lean absorbs the Grammar wrapper.
- **Phenomena/Scope.lean**: Fixed `dp_phase_barrier_from_pic` — decompose SO as `node (leaf tok) b` (head-is-leaf, complement-is-right-daughter), making the theorem precisely capture PIC freezing the complement domain. Eliminates both `sorry` holes; proof is now complete.

## [0.124.0] - 2026-02-09

### Added
- **Minimalism/Core/Phase.lean**: Phase Theory formalization (Chomsky 2000/2001/2008, Abels 2012, Citko 2014). `isPhaseHead` derived from `labelCat` (C, v). `isDPhaseHead` for D-as-phase. `PICStrength` (.strong/.weak). `Phase` structure (head, complement, edge). `phaseImpenetrable` (PIC). `antiLocality` (Abels 2012 ch.4). `stranding_from_antilocality_pic` (proven: anti-locality + PIC → complement immovable). `Transfer` (PF/LF shipping). `FeatureInheritance` (C→T, v*→V). `isPhaseBounded` locality predicate.
- **Core/SyntacticObjects.lean**: `phonForm` field on `SimpleLI` (backward-compatible default `""`). `uposToCat` (UD UPOS → Cat mapping). `mkTrace`/`isTrace` trace convention (id ≥ 10000). `phonYield` (collect phonological forms from leaves). `mkLeafPhon` smart constructor.
- **Core/Conjectures.lean**: Phase-bounded exhaustification conjectures: `exh_at_phase_boundaries`, `rsa_phase_locality`, `phase_bounded_alternatives`.
- **Phenomena/Scope.lean**: `dp_phase_barrier_from_pic` theorem deriving QR barrier from PIC (sorry'd for head-child case).

### Changed
- **SynObj → SyntacticObject migration**: Fully migrated Minimalism module from informal `SynObj` (.lex/.set/.trace) to formal `SyntacticObject` (.leaf/.node). Deleted `Feature`, `FeatureBundle`, `SynObj`, old `externalMerge`, `Movement`, `DerivStep`, `Derivation`, `Phase`/`isPhase` from `Core/Basic.lean`.
- **Core/Basic.lean**: Now a thin wrapper providing `MinimalistGrammar` and `Grammar` instance using formal `FullDerivation` from Workspace.lean. `MinDerivation` wraps `FullDerivation` + `ClauseType`.
- **Core/FromFragments.lean**: Rewritten to use `SyntacticObject` via `mkLeafPhon`. `verbToSO`, `pronounToSO`, `nounToSO`, `determinerToSO`, `lexResultToSO` replacing old SynObj-based functions.
- **Phenomena/Derivations.lean**: All derivation examples rewritten with `SyntacticObject` and formal `merge`. `phonYield` verification examples.
- **Bridge/Interface.lean**: Rewritten for `SyntacticObject`. `soSemanticType`, `interpSOTrace`, `getTraceIndex` replacing SynObj versions.
- **Bridge/RelativeClauses.lean**: Rewritten for `SyntacticObject`. Uses `mkTrace` instead of `SynObj.trace`.
- **Formal/Workspace.lean**: Added `transferStep` to `DerivationStep`.
- **Formal/HeadMovement/Basic.lean**: `isLocal` now uses `isPhaseHead` from Phase module. Removed axiom, replaced with theorem.
- **Core/Agree.lean**: Added `validAgreeWithPIC` and `fullAgree` (phase-bounded Agree).

## [0.123.0] - 2026-02-09

### Added
- **IntensionalSemantics/Reference/Kripke.lean**: Kripke (1980) *Naming and Necessity* Lecture I. **Main theorem: `rigid_iff_scope_invariant`** — a designator is rigid iff de re and de dicto readings coincide for all predicates (both directions proven; backward direction uses identity predicate as witness). `nonrigid_creates_ambiguity` — non-rigidity constructively produces a scope-distinguishing predicate (proven). `rigid_allOrNothing` — co-reference between rigid designators is world-independent (proven, strengthens `rigid_identity_necessary`). `nonrigid_identity_contingent` — without rigidity, identity can be contingent (the essential contrast). `modal_argument` — rigid name ≠ non-rigid description (proven). `properName_neq_description` — bridge to `Reference/Basic.properName`. `IsEssential`/`IsAccidental` with `essential_rigid_necessary` (proven) and `nonrigid_loses_essential` (proven). `rigidification_not_synonymy` — dthat rescues rigidity but destroys synonymy (proven, bridges to `KaplanLD.dthatW`). `IsStronglyRigid` with `rigid_stronglyRigid` (proven). Zero sorry.

## [0.122.0] - 2026-02-09

### Added
- **Core/Context.lean**: Full Kaplanian context of utterance `KContext W E P T` with agent, world, time, position. `ProperContext` (agent exists at context world), `LocatedContext` (agent at position/time/world), `toSituation` bridge to `Core.Time.Situation`.
- **Core/Intension.lean**: `StableCharacter` (same content at every context, Kaplan §XIX Remark 5). `stableCharacter_iff_sameContent` (proven). `rigid_stableChar_constant` — rigid + stable character = fully constant (proven, Remark 10).
- **IntensionalSemantics/Reference/KaplanLD.lean**: Kaplan (1989) LD formal system. `LDStructure` (full model with proper-context constraint). `dthat`/`dthatW` rigidifier (§XII) with `dthat_isRigid` (proven). `alpha_eq_dthat_alpha` (proven by rfl, Remark 3). `box_alpha_eq_dthat_not_valid` (proven). Indexical operators: `opNow`, `opActually`, `opYesterday`. Tense operators: `opFuture`, `opPast`. Modal operators: `opBox`, `opDiamond`. Metatheorems: `exist_i_valid` (proven from LDStructure.proper), `i_am_located_valid`, `actually_stable` (proven by rfl).
- **IntensionalSemantics/Reference/Demonstratives.lean**: True demonstratives and demonstrations (§IX, XV, XVI). `Demonstration` (manner of presentation → demonstratum). `TrueDemonstrative` with optional sortal. `demo_directlyReferential` — Principle 2 (proven). `demo_character_varies` (proven). `DemoFregePuzzle` — "that [Hes] = that [Phos]" informative because demonstrations differ. `fregePuzzle_same_content` (proven). `toReferringExpression` bridge to Basic.lean types.
- **IntensionalSemantics/Reference/Monsters.lean**: Kaplan's anti-monster thesis (§VIII). `ContentOperator` (shifts circumstances), `ContextOperator` (shifts context = monster). `IsMonster` (output depends on input at other contexts). `FixityThesis` (Schlenker 2003 (1)): indexical value fixed by actual speech act. `sayM` monstrous attitude operator (Schlenker 2003 (6)): attitude verbs as quantifiers over contexts. `sayM_accesses_shifted_context` (proven). `KaplansThesis`, `englishThesis`. Cross-linguistic counterexamples: `amharicShift` (Schlenker 2003), `zazakiShift` (Anand & Nevins 2004), `englishTemporalShift` (Schlenker 2003: "yesterday" shifts under attitude verbs). `MonsterDebate` with current consensus.
- **Reference/Basic.lean**: `Context.toKContext` bridge lifting simple `Context W E` to full `KContext W E P T`.
- **Phenomena/Reference/DirectReference.lean**: `MonsterThesis` phenomenon — Kaplan's claim, its status, supporting vs challenging languages.

## [0.121.0] - 2026-02-09

### Added
- **IntensionalSemantics/Reference/Basic.lean**: Core infrastructure for Almog's (2014) three-mechanism taxonomy of direct reference. `Context`, `Character`, `Content` (Kaplanian two-stage semantics). `RefMechanism` (`.designation | .singularProp | .referentialUse`). `ReferringExpression` bundling character + mechanisms. `isDirectlyReferential`, `constantCharacter`. `properName` with `properName_isDirectlyReferential` (proven). `IsDeJureRigid` vs `IsDeFactoRigid`. `properNames_corefer_coextensional` bridge to `Core.Intension.rigid_identity_necessary`.
- **IntensionalSemantics/Reference/Kaplan.lean**: Kaplan (1989) character/content semantics. `indexical`, `pronI` with `pronI_directlyReferential` (proven). `SingularProposition` (structured ⟨individual, property⟩), `eval`, `flatten`. `structured_distinguishes_unstructured` (proven) — the Frege puzzle. `constantCharacter_is_up` bridge to Attitude/Intensional's `up`. `i_am_here_now_logically_true`.
- **IntensionalSemantics/Reference/Donnellan.lean**: Donnellan (1966) referential/attributive distinction. `UseMode` (`.attributive | .referential`). `DefiniteDescription` with restrictor, use mode, optional intended referent. `attributiveContent` (Russellian unique-satisfier), `referentialContent` (rigid). `referentialUse_isRigid` (proven). `DonnellanDivergence` structure + `donnellanDivergence` theorem. `definitePrProp` bridge to `Core.Presupposition.PrProp`. `attributive_is_pointwise_iota` bridge to `TypeShifting.iota`.
- **IntensionalSemantics/Reference/Almog2014.lean**: Synthesis — `IndependenceWitness` witnessing all three mechanisms operating independently. `frege_puzzle` (proven). Bridge theorems to: Carlson1977 (bare plurals = designation), Doxastic (opacity from structured propositions), RSA reference games (L0=attributive, S1=referential), Core.Conjectures (rigid ↔ CG), PLA/Belief (concept divergence).
- **Phenomena/Reference/DirectReference.lean**: Six classic phenomena: `HesperusPhosphorus` (informative identity), `ModalArgument` (names rigid, descriptions not), `DonnellanMartini` (referential/attributive divergence), `SubstitutivityFailure` (belief opacity), `IAmHereNow` (logical truth ≠ necessity), `NecessityOfIdentity` (a posteriori necessity).
- **Core/Intension.lean**: `CoRefer`, `CoExtensional`, `rigid_identity_necessary` (proven) — Kripke's necessity of identity as the formal kernel.
- **Core/Conjectures.lean**: `almog_independence_conjecture` pointing to formal content in Almog2014.lean.
- **Phenomena/Attitudes/IntensionalExamples.lean**: `hesperus_rigid`, `morningStar_not_rigid` (proven), `hesperus_rigid_isRigid` (proven), `name_vs_concept_independence` (proven) — bridge connecting Fregean individual concepts to Kripkean rigid designators.

## [0.120.0] - 2026-02-09

### Changed
- **Factor Information Structure into Core**: Extracted foundational IS types from theory-specific files into three new Core modules, reflecting IS's cross-cutting nature (like QUD, Proposition, Scales).
  - **Core/Alternatives.lean**: `Alternatives`, `HasAlternatives`, `AltMeaning`, `AltMeaning.unfeatured` (from Focus/InformationStructure + KratzerSelkirk2020).
  - **Core/InformationStructure.lean**: `Theme`, `Rheme`, `Focus`, `Background`, `InfoStructure`, `HasInfoStructure`, `ISFeature`, `DiscourseStatus`, `isNew`, `applyFoC`, `applyG`, `isGiven`, `foc_g_exclusion` (from Focus/InformationStructure + KratzerSelkirk2020).
  - **Core/Prosody.lean**: `PitchAccent`, `BoundaryTone`, `ProsodicLevel`, `ProsodicConstituent` (from CCG/Phenomena/Intonation + KratzerSelkirk2020).
  - **KratzerSelkirk2020.lean** moved from `Theories/InformationStructure/` to `Theories/TruthConditional/Sentence/Focus/` alongside other focus theory files (Rooth, particles). Stripped to paper-specific content: TwoDimProp grounding, Contrast, ContrastOperator, onlySemantics, spellout, SOF data, Schwarzschild comparison.
  - Deleted `Theories/TruthConditional/Sentence/Focus/InformationStructure.lean` (all content in Core).
  - Deleted `Theories/InformationStructure/` directory.
  - Dropped unused types: `QUD World`, `QUDAbstract`, `Answer`, `QUDSemantics`, `congruent` (duplicated or never imported).
  - Updated imports in `Focus/Interpretation.lean`, `CCG/Phenomena/Intonation.lean`, `Linglib.lean`.

## [0.119.0] - 2026-02-09

### Added
- **Theories/InformationStructure/KratzerSelkirk2020.lean**: Formalization of Kratzer & Selkirk (2020) "Deconstructing Information Structure". Two-feature decomposition: `ISFeature` (.FoC / .G) replaces unified [F]. `AltMeaning` O-value/A-value pairs (§4-5). `applyFoC` expands A-value to full domain (def 45), `applyG` identity with Givenness presupposition (def 47), `isGiven` singleton A-value check (def 46). `foc_g_exclusion`: mutual exclusivity theorem (§8 (58)). Both features grounded in Potts' `TwoDimProp` as use-conditional via `focAsTwoDim`/`gAsTwoDim` with CI projection theorems. `Contrast`/`ContrastOperator` (defs 49/53-54): ~ operator consuming alternatives, enabling [G]-marking (`consumed_alts_enable_g`). `onlySemantics` (def 56). Prosodic hierarchy: `ProsodicLevel` (σ/f/ω/φ/ι), `FoCSpellout`/`GSpellout` constraints, `SpelloutRanking` OT-style priority (§7). `SOFDatum` with Beaver et al. 2007 example. Katz & Selkirk 2011 prosodic triple data. `PressureForG`/`PressureForFoC` pragmatic pressures (§9 (61)/(66)). Comparison with Schwarzschild: `givenness_entails_aGivenness` (K&S stronger) and `aGivenness_not_sufficient` (converse fails).

## [0.118.0] - 2026-02-09

### Added
- **HPSG/Core/FromFragments.lean**: New Fragment → HPSG Sign mapping layer (following CCG/Core/FromFragments pattern). `verbToSign`, `nounToSign`, `pronounToSign`, `determinerToSign`. `fragmentLexicon` builds complete HPSG lexicon from all English Fragment entries. Verification examples for intransitive/transitive/ditransitive valence, proper/common noun categories.

### Changed
- **HPSG reorganization**: Reorganized 6 flat files into Core/Phenomena structure matching CCG, Minimalism, and DependencyGrammar. `Basic.lean` + `Features.lean` merged into `Core/Basic.lean` with unified types (`Inv` inductive replaces `inv : Bool`, merged `VForm`/`VForm'` and `HeadFeatures`/`HeadFeatures'`). `HeadFiller.lean` → `Core/HeadFiller.lean`, `LexicalRules.lean` → `Core/LexicalRules.lean`, `Coreference.lean` → `Phenomena/Coreference.lean`, `Inversion.lean` → `Phenomena/Inversion.lean`. Updated imports in `Mueller2013.lean`, `CommandRelations.lean`, and `Linglib.lean`.

## [0.117.0] - 2026-02-09

### Added
- **Core/Basic.lean**: Sorry'd projection axioms (`projection_chain'`, `projection_nonempty`). List helper lemmas: `foldl_max_ge_init`, `foldl_max_ge_mem`, `foldl_max_zero_iff` (proven), `foldl_max_pos_of_mem_pos` (proven), `foldl_max_le_bound` (proven), `foldl_max_const` (proven). Sorry'd list-projection lemmas: `isInterval_iff_gaps_nil`, `blocks_length_eq_gaps_length_succ`.
- **Phenomena/NonProjectivity/Data.lean**: Extracted treebank empirical data from NonProjective.lean. `TreebankCoverage` + `pdt`/`ddt` (K&N 2006 Table 1), `LCFRSCoverage` + `arabic`/`czech`/`danish`/`slovene`/`turkish` (Kuhlmann 2013 Tables 3-4).

### Changed
- **NonProjective.lean**: Proved 4 of 6 hierarchy theorems (modulo sorry'd axioms about `projection` output properties). `projective_iff_gapDegree_zero` (Thm 1, proven), `projective_iff_blockDegree_one` (Thm 2, proven, added `t.words.length > 0` hypothesis), `blockDegree_eq_gapDegree_succ` (Thm 3, proven), `nonProjective_implies_gapDeg_ge1` (Thm 6, proven). `projective_implies_planar` (Thm 4) and `planar_implies_wellNested` (Thm 5) remain sorry'd — require edge-projection structural lemmas. Extracted empirical data to Phenomena/, verification theorems remain and reference `Phenomena.*`.

## [0.116.0] - 2026-02-09

### Added
- **Core/Basic.lean**: `projection` (π(i)) as first-class primitive — BFS yield of a node in sorted order. `isInterval`, `gaps`, `blocks`, `gapDegreeAt`, `blockDegreeAt`, `DepTree.gapDegree`, `DepTree.blockDegree`. Rewrote `isProjective` from arc-crossing to projection-based (every projection is an interval).
- **NonProjective.lean**: Full Kuhlmann & Nivre (2006) + Kuhlmann (2013) formalization. `linked`, `DepTree.isPlanar` (Definition 4), `projectionsInterleave`, `disjoint`, `DepTree.isWellNested` (Definition 8), `edgeSpan`, `edgeDegreeOf`, `DepTree.edgeDegree` (Definition 9). Example trees: K&N Figure 3a/3b/3c, Dutch cross-serial, German nested. Hierarchy theorems (sorry'd): projective ⟺ gap degree 0, projective ⟺ block-degree 1, block-degree = gap degree + 1, projective ⊂ planar ⊂ well-nested. Empirical data: PDT/DDT (K&N 2006 Table 1), Arabic/Czech/Danish/Slovene/Turkish LCFRS coverage (Kuhlmann 2013 Tables 3–4). All example properties verified by `native_decide`.

### Changed
- **Catena.lean**: Removed `descendants`/`subtree` BFS duplicate, rewrote `isConstituent` to use `projection`.
- **DependencyLength.lean**: Replaced `subtreeSize` BFS with `projection`-based wrapper.
- **HarmonicOrder.lean**: Replaced `subtreeMembers` BFS with `projection`-based wrapper.
- **Discontinuity.lean**: Replaced `isContiguous` with delegation to `isInterval`.
- **VPDivergence.lean**: Updated `subtree` references to `projection`.

## [0.115.0] - 2026-02-09

### Added
- **DependencyGrammar/Formal/Government.lean**: Osborne (2019, Ch 4 §4.8, Ch 5) government formalization. `GovernedFeature` (case, vform, mood, finiteness), `GovRequirement` linking head category + dep relation to required feature value. 5 English government patterns (infinitive, bare infinitive, gerund, finite, prepositional case). `matchGovFeature` checks feature bundles, `checkGovernment` validates a full tree. `GovernmentPattern` structures for want/enjoy/think/make. Example trees: "she wants to go", "she enjoys swimming", "with him" (ok) vs "with he" (violation). `government_orthogonal_to_valency` (same depRel, different requiredValue). Bridges: `same_valency_different_government` (→ CRDC), `government_implies_head` (→ HeadCriteria criterion 5), `argslot_agnostic_to_government` (→ Core/Basic).
- **DependencyGrammar/Formal/Ellipsis.lean**: Osborne (2019, Ch 12–13) ellipsis-as-catena formalization. `EllipsisType` (6 types). 5 example `DepTree`s with identified elided node sets: VP ellipsis ({cook, dinner}), gapping ({eats}), pseudogapping ({helped}), sluicing ({helped, she}), fragment answer ({helped}). 10 `native_decide` theorems: `*_elided_is_catena` + `*_elided_not_constituent` for each type. `all_ellipsis_targets_catenae` (all 5 are catenae), `all_ellipsis_not_constituent` (none are constituents). Bridge: `toGappingEllipsisType` (→ Phenomena/Ellipsis/Gapping), `gapping_always_catena_not_constituent`.
- **DependencyGrammar/Formal/Discontinuity.lean**: Osborne (2019, Ch 7–8) discontinuities as risen catenae. `DiscontinuityType` (5 types from Table 19: whFronting, topicalization, npInternalFront, scrambling, extraposition), `DisplacementDir` (rising/lowering), `RisingType` (constituent/nonConstituent from §7.11). `isContiguous` checks contiguous yield, `isRisenCatena` = catena ∧ ¬contiguous. 5 example trees from Osborne: "What did you eat?" (wh-fronting), "Those ideas I do accept" (topicalization), "dass uns Maria etwas gebacken hat" (scrambling), "The idea arose to try again" (extraposition), "He's nice, that boy" (right dislocation). `classifyDisplacement` on dependency arcs. `all_discontinuities_are_risen_catenae` (all 5 produce risen catenae by `native_decide`). Bridges: `displaced_pairs_are_catenae` (→ Catena), `wh_fronting_is_obj_gap` (→ LongDistance), `nonProjective_tree_also_risen` (→ NonProjective).
- **DependencyGrammar/Formal/Islands.lean**: Osborne (2019, Ch 9) islands as constraints on rising catenae. `OsborneIslandType` (8 types: leftBranch, specifiedNP, subject, adjunct, whIsland, rightRoof, pStranding, piedPiping). 5 island violation trees from actual Osborne sentences: "Whose do you like house?" (§9.4), "Which car did the driver of ignore the light?" (§9.7), "What do they argue before cleaning?" (§9.8), "Which judge might they inquire surprised?" (§9.9), "Who did you find those pictures of?" (§9.6). Island material proven as catenae (`all_islands_are_catenae`), extraction creates risen catenae (`all_island_extractions_risen`). Bridges: `toLongDistanceIslandType` (→ LongDistance, adjunct + subject shared), `toPhenomenaConstraintType` (→ Phenomena/Islands/Data, adjunct + subject + whIsland→embeddedQuestion), `island_extractions_are_discontinuities` (→ Discontinuity), `all_islands_are_catenae` (→ Catena).
- **DependencyGrammar/Formal/CoordinationParallelism.lean**: Osborne (2019, Ch 10–11) coordination parallelism. `SharingType` (forward/backward/symmetric/none). `parallelConjuncts` checks matching dep-rel sets, `sharedDepTypes` extracts shared relations. 4 example trees: forward sharing, gapping-as-coordination, ATB extraction + enhanced graph. `isATBExtraction`/`cscViolation` for CSC checking. Shared material proven as catenae for all examples. `gapping_conjuncts_parallel`, `atb_conjuncts_parallel`, `atb_extraction_is_atb`, `atb_no_csc_violation`. Bridges: `coordination_cat_match_preserved`/`gapping_argstr_match` (→ Coordination), `all_shared_are_catenae` (→ Catena), `gapping_is_catena_ellipsis` (→ Ellipsis), `sharing_direction_matches_gapping` (→ Phenomena/Ellipsis/Gapping).

## [0.114.0] - 2026-02-08

### Added
- **Phenomena/WordOrder/Gradience.lean**: Levshina, Namboodiripad et al. (2023) gradient word-order measures (*Linguistics* 61(4):825–883). §1: `harmonicProportion1000`/`disharmonicProportion1000`/`hiProportion1000` on existing `CrossTab` data, `harmony_decreases_with_complexity` (943 > 861 > 822), `categorical_consistent_with_gradient`. §2: `GradientWOProfile` (SO proportion, SO entropy, case MI × 1000) for 30 languages from OSF Dataset1.txt + Dataset3.txt (exact values, not eyeballed). §3: `rigid_languages_low_entropy`, `case_rich_flexible_languages_high_mi`, `tamil_counterexample` (high entropy but low case MI), `case_mi_correlates_with_so_entropy`, `so_proportion_is_continuous`. §4: 4 bridge theorems — `gradient_implies_categorical` (→ Typology), `high_so_entropy_implies_high_branch_entropy` (→ HahnDegenFutrell2021, 28 shared languages), `head_final_correlates_with_so` (→ FutrellEtAl2020, 26 shared languages), `high_entropy_languages_include_exceptions` (Latvian in both). §5: Russian register variation from OSF Dataset6.txt (`RegisterProfile`, conversation 390 / fiction 830 / news 830), `register_variation_is_large` (44pp spread). All by `native_decide`, no `sorry`.

## [0.113.0] - 2026-02-08

### Added
- **MemorySurprisal/Basic.lean**: Hahn, Degen & Futrell (2021) memory-surprisal trade-off framework. `MemoryEncoding`, `averageSurprisal` (wraps `conditionalEntropy`), `memoryEntropy` (wraps `entropy`), `MutualInfoProfile` with `totalInfo`/`weightedSum`, `information_locality_bound` (sorry, proof sketch from SI §1.2). `TradeoffPoint`/`TradeoffCurve` with trapezoidal `auc`, `efficientTradeoffHypothesis`. Bridges: rate-distortion correspondence (sorry), `memoryToLocality` → ProcessingModel, `information_locality_generalizes_dep_locality` (sorry). Concrete profiles: efficient vs inefficient I_t decay with `efficient_lower_weighted_sum`.
- **MemorySurprisal/FedzechkinaEtAl2017.lean**: Study 1 — artificial language learning. `MiniLanguage` (.langA/.langB), concrete `DepTree` instances for SOV with complex NP first/last. `langA_shorter_deps` (TDL 8 < 9), `langA_more_efficient` (lower AUC), `learners_prefer_efficient` (670/1000 > chance). Bridge: `short_deps_implies_efficient`.
- **MemorySurprisal/CrossLinguistic.lean**: Study 2 — 54-language crosslinguistic efficiency. `efficient_tradeoff_hypothesis_holds` (50/54), `exceptions_have_high_entropy`. Bridges: FutrellEtAl2020 shared languages (`many_shared_languages` ≥ 20, `polish_only_shared_exception`), HarmonicOrder (`harmonic_dlm_holds`, `rigid_order_languages_efficient`). Word-order freedom analysis: `exceptions_all_high_entropy` (≥ 720), `high_entropy_not_sufficient`.
- **MemorySurprisal/MorphemeOrder.lean**: Study 3 — Japanese & Sesotho morpheme order. Bybee (1985) relevance hierarchy: `MorphCategory`, `relevanceRank`, `respectsRelevanceHierarchy`. Japanese 7-slot suffix template (`japaneseSuffixSlots`), Sesotho prefix/suffix templates. `sesotho_suffixes_respect_bybee`, `japanese_partial_bybee`. Efficiency: `japanese_morpheme_efficient`, `sesotho_morpheme_efficient`. Bridges: `ik_ase_is_causative` → Japanese/Predicates, `japanese_causative_is_compact` → Causatives/Typology, `relevance_hierarchy_implies_locality`.
- **Phenomena/WordOrder/HahnDegenFutrell2021.lean**: 54-language efficiency data from Study 2 (SI Table 2, Figure 2). `LanguageEfficiency` with `gMean1000` (bootstrapped G × 1000), `branchDirEntropy1000`. 50 efficient + 4 exceptions (Latvian, North Sami, Polish, Slovak). Core theorems: `total_count` (54), `most_languages_efficient` (50), `all_exceptions_have_high_word_order_freedom`, `all_exceptions_below_threshold`, `exceptions_higher_mean_entropy`, `slovak_lowest_g`. Data source: <https://github.com/m-hahn/memory-surprisal>.

## [0.112.0] - 2026-02-08

### Added
- **Phenomena/WordOrder/Typology.lean**: WALS word-order typology data (Dryer 2013) from Gibson (2025) Ch. 5.3 Tables 1–3. `HeadDirection`, `AlignmentCell` (with `.isHarmonic`), `CrossTab` (with `harmonicCount`/`disharmonicCount`/`harmonicDominant`). Three cross-tabulations: VO × Adposition (981 langs), VO × Subordinator (456 langs), VO × Relative clause (665 langs). 12 per-cell verification theorems, 3 per-table `harmonicDominant` theorems, `head_direction_generalization` (all 3 tables). `SingleWordException` for Gibson Table 4 (adj-N, dem-N, intensifier-adj, neg-verb). All by `native_decide`.
- **DependencyGrammar/Formal/HarmonicOrder.lean**: Gibson (2025) Ch. 5.3 harmonic word order via DLM. §1: `chainTDL` (abstract chain dep length over `List Nat`), `isMonotone`/`listSpan`, `chain_tdl_ge_span` (sorry), `monotone_ascending_achieves_span` (sorry), concrete verifications k=2..5. §2: `subtreeMembers`, `interveningSubtreeNodes`, `dep_length_eq_one_plus_intervening` (sorry). §3: `isLeaf`, `leaf_no_intervening` (sorry) — single-word exception, bridge to `single_dep_direction_irrelevant`. §4: 4 concrete `DepTree` instances (HH/FF/HF/FH recursive embedding), `harmonic_hi_beats_disharmonic_hf`, `harmonic_hf_beats_disharmonic_fh`, `direction_irrelevant_consistency_matters` (HH TDL = FF TDL), `harmonic_always_shorter`. §5: `dlm_explains_head_direction_generalization` — DLM predicts harmonic cheaper ∧ WALS confirms harmonic dominant, for all 3 tables. Bridges to Behaghel (`oberstesGesetz`), projectivity, well-formedness.

## [0.111.0] - 2026-02-08

### Changed
- **DependencyGrammar namespace normalization**: All 14 DG files now use `DepGrammar.*` namespace consistently. Coordination.lean: `Coordination.WordGrammarAnalysis` → `DepGrammar.Coordination`. LongDistance.lean: `LongDistanceDependencies.WordGrammarAnalysis` → `DepGrammar.LongDistance`. Inversion.lean: added `DepGrammar.Inversion` namespace (was bare `open DepGrammar`). EnhancedDependencies.lean aliases updated to match.
- **Core/Basic.lean**: Added `Word.mk'` — public featureless word constructor replacing 4 private `mkw`/`w` definitions scattered across Formal/ files.
- **Core/Nominal.lean**: Added Fragment imports and 11 shared test word abbreviations (`john`, `mary`, `himself`, `herself`, etc.) from English Fragments. These were previously duplicated identically in both Coreference.lean and CRDC.lean.
- **Coreference.lean / CRDC.lean**: Removed duplicate private abbrev blocks (11 words each) and 3 Fragment imports each — now use shared words from `Nominal` via `open Nominal`.
- **Catena.lean / VPDivergence.lean / DependencyLength.lean / EnhancedDependencies.lean**: Replaced private `mkw`/`w` helpers with `Word.mk'` from Core/Basic.lean.

## [0.110.0] - 2026-02-08

### Added
- **DependencyGrammar/Formal/VPDivergence.lean**: Osborne (2019, Ch. 2–4) VP divergence — the central empirical disagreement between DG and PSG. Strict containment theorems: `strict_containment_tree9`/`_chain4`/`_star4` (constituents ⊊ catenae for all non-trivial trees), `nonConstituentCatenae` enumeration, `exists_catena_not_constituent` (Prop-level universal witness, sorry). Minimal `PSTree` type for structural comparison (leaf/node, `words`/`constituents`/`hasConstituent`). Three VP divergence examples: "Bill plays chess" (p. 92, ex. 24), "She reads everything" (p. 46, ex. 12), "They will get the teacher a present" (p. 95–97, ex. 30–34) — each with DG `DepTree` + PSG `PSTree`. Core divergence theorems: `vp_is_catena_*` (finite VP is catena), `vp_not_constituent_*` (not constituent in DG), `vp_is_constituent_psg_*` (IS constituent in PSG), `dg_fewer_constituents_*` (DG < PSG constituent count). Constituency test framework: `ConstituencyTest` (5 tests), `TestResult` (DG/PSG predictions vs observed), `finiteVPTests` encoding Osborne's Table 25. `dg_predictions_match_observed` (≥4/5), `psg_predictions_mismatch` (≤2/5), exact counts `dg_matches_exactly_four`/`psg_matches_exactly_one`. Quantitative: `dg_constituent_count_eq_words_*`, catena ratio comparison. Bridges: `vp_catena_dep_length_*` (→ DependencyLength), `constituent_is_catena_billPlaysChess` (→ Catena), `isomorphic_divergence` (structural robustness). All theorems by `native_decide` except `exists_catena_not_constituent`.

## [0.109.0] - 2026-02-08

### Added
- **DependencyGrammar/Formal/Catena.lean**: Osborne, Putnam & Groß (2012, *Syntax* 15:4) catena formalization with mathlib `SimpleGraph` integration. `depsToSimpleGraph` bridges `Dependency` edges to `SimpleGraph (Fin n)`, `DepTree.asSimpleGraph` converts existing trees. Prop-level `IsCatena` uses `SimpleGraph.induce` + `SimpleGraph.Preconnected` on induced subgraphs. Computable `isCatena`/`isConstituent` via BFS enable `native_decide`. `allNonEmptySubsets`, `catenaeCount`, `constituentCount`, `totalCombinations`, `catenaRatio` for enumeration. Paper examples: tree (9) (10 catenae / 5 non-catenae / 4 constituents), tree (22) (6/1/3), chain4 (10 catenae), star4 (11 catenae). Structural theorems: `flatter_more_catenae` (star > chain), `constituent_is_catena_*` (exhaustive verification), `counting_hierarchy_*` (constituents ≤ catenae ≤ 2^n-1), `IsCatena_singleton` (Prop-level, mathlib proof). Linguistic example: "pulled some strings" — idiom {pulled, strings} is catena but not constituent (`idiom_is_catena`, `idiom_not_constituent`). `catenaTotalDepLength` measures catena spread. Bridge theorem `isCatena_iff_IsCatena` connecting Bool ↔ Prop (sorry, TODO: BFS ↔ Preconnected equivalence).

## [0.108.0] - 2026-02-08

### Changed
- **DependencyGrammar/Core/Basic.lean**: Added `DepGraph` structure (multi-head dependency graph) and `DepTree.toGraph` alongside `DepTree`, making both fundamental DG data types available from the core module.
- **DependencyGrammar/Phenomena/Coordination.lean**: Full rewrite — removed 5 workaround types (`CoordStr`, `CoordTree`, `GappingStr`, `RNRStr`, `GappedTree`) and `isCoordWellFormed`. Coordination now uses `DepTree` (basic) + `DepGraph` (enhanced) directly. New: `getConjuncts` (derive conjuncts from `conj` edges), `checkCatMatch`/`checkArgStrMatch` (operate on `DepTree`), `enhanceSharedDeps` (propagate obj/nsubj/iobj from first conjunct → all conjuncts, producing `DepGraph`). Examples: NP/S/VP/Adj coordination + RNR, all as `DepTree` with enhanced `DepGraph` variants. Theorems: `enhanced_has_shared_obj`, `basic_lacks_shared_obj`, `enhanced_not_tree`, `rnr_enhanced_has_shared_obj` — all by `native_decide`.
- **DependencyGrammar/Phenomena/LongDistance.lean**: Full rewrite — removed 2 workaround types (`FillerGapDep`, `LDTree`). Long-distance dependencies now use `DepTree` + `DepGraph` directly. New: `fillGap`/`fillGaps` (add argument edges producing `DepGraph`), `getSLASH` (derive SLASH features from basic-vs-enhanced graph difference), `isInsideIsland`/`checkNoIslandViolation` (operate on `DepTree`). Examples: wh-questions, relative clauses, complement clauses as `DepTree` with enhanced `DepGraph` for gap-filled variants. Theorems: `relclause_enhanced_has_obj`, `relclause_slash_derived`, `relclause_enhanced_not_tree` — all by `native_decide`.
- **DependencyGrammar/Formal/EnhancedDependencies.lean**: Simplified — removed `DepGraph`/`DepTree.toGraph` (moved to Core/Basic.lean), `coordTreeToEnhancedGraph`/`ldTreeToEnhancedGraph` (replaced by Coordination's `enhanceSharedDeps` and LongDistance's `fillGap`), standalone duplicate examples. Now imports Coordination + LongDistance examples via aliases. All cross-cutting theorems preserved: information loss, recovery, superset, unique-heads violation, DependencyLength bridge, NonProjective bridge.

## [0.107.0] - 2026-02-08

### Added
- **DependencyGrammar/Formal/EnhancedDependencies.lean**: de Marneffe & Nivre (2019, §4.2) enhanced dependencies. `DepGraph` (relaxes `DepTree` unique-heads to allow multiple heads per word), `EnhancementType` (coordSharedDep/controlSubject/relClauseGap), `hasUnrepresentedArg` (detects information loss in basic trees). Three concrete examples: coordination ("John sees and hears Mary"), control ("Students forgot to come"), relative clauses ("the book that John read"). Key theorems: `basic_tree_loses_coord_args`/`_control_subject`/`_relclause_gap` (basic trees lose predicate-argument info), `enhanced_recovers_*` (enhanced graphs recover it), `enhanced_not_tree_*` (enhanced graphs violate `hasUniqueHeads`), `basic_is_tree_*`/`enhancement_preserves_basic_*` (basic edges are a subset). Bridges: `coordTreeToEnhancedGraph` converts `CoordStr` workaround → graph edges (→ Coordination.lean), `ldTreeToEnhancedGraph` converts `FillerGapDep` → graph edges (→ LongDistance.lean), `enhancedTotalDepLength` ≥ `totalDepLength` (→ DependencyLength.lean), `basic_relclause_projective` (→ NonProjective.lean). Classification: `classifyEnhancement` maps enhanced edges to enhancement types. All theorems by `native_decide`, no `sorry`.

## [0.106.0] - 2026-02-08

### Added
- **DependencyGrammar/Formal/DependencyLength.lean**: Futrell, Levy & Gibson (2020) dependency length minimization. `depLength` (|headIdx - depIdx|), `totalDepLength` (sum over tree), `meanDepLengthScaled` (× 100 / n), `subtreeSize` (transitive descendant count). Head direction: `isHeadFinal`/`isHeadInitial`, `headFinalCount`/`headInitialCount`, `HeadDirectionProfile`. Behaghel's laws: `oberstesGesetz` (max dep length threshold), `gesetzDerWachsendenGlieder` (short-before-long on each side). Key theorem: `short_before_long_minimizes` (smaller subtree closer → shorter total, proved by `omega`). Example sentences from §2.2: particle placement ("threw out the trash" vs "threw the trash out"), heavy NP shift, all verified by `native_decide`. Bridges: `totalDepLength projectiveReordering ≤ totalDepLength nonProjectiveTree` (→ NonProjective.lean), `depToProcessingLocality` + `longer_dep_harder` (→ ProcessingModel.lean), `single_dep_direction_irrelevant` + consistent vs mixed direction examples (→ HeadCriteria.lean). Additional: `depLength_symmetric`, `adjacent_dep_length`, `empty_tree_dep_length`.
- **Phenomena/DependencyLength/FutrellEtAl2020.lean**: Crosslinguistic dependency length data from Table 2 (32 representative languages from 53). `LanguageDLM` structure (name, ISO code, family, propHeadFinal × 1000, depLength × 100 at lengths 10/15/20). Per-datum head-finality classification verification (Japanese, Korean, Turkish, Hindi, Tamil = head-final; English, Arabic, Indonesian, French, Romanian = head-initial). Empirical generalizations: `headFinal_higher_depLength_10`/`_20` (head-final languages have systematically higher mean dep length), `japanese_highest_depLength_20`, `indonesian_lowest_depLength_10`, `headFinality_gap_increases` (gap widens with sentence length). All verified by `native_decide`.

## [0.105.0] - 2026-02-08

### Added
- **DependencyGrammar/Formal/HeadCriteria.lean**: Zwicky (1985) & Hudson (1990) head determination criteria. `HeadCriterion` structure with 5 concrete criteria (categoryDetermination, obligatoriness, selection, morphologicalDetermination, positionalDetermination), `criterionCount`/`isPrototypicalHead`. `RelationClass` (coreArgument/modifier/functionWord) with `classifyRelation` mapping UD relations. `HeadednessAnalysis` (functionHead/contentHead) with `HeadednessEvidence` for aux and det relations (de Marneffe & Nivre 2019 §4.5). Theorems: `content_head_more_criteria_for_det`, `core_args_most_criteria`, classification proofs.
- **DependencyGrammar/Core/Nominal.lean**: Shared nominal classification and phi-feature agreement extracted from Coreference.lean and CRDC.lean. `NominalType` (reflexive/pronoun/rExpression), `isNominalCat`, `classifyNominal`, `phiAgree`, parameterized `capturesMinimalPair`/`capturesPhenomenonData`.

### Changed
- **Core/UD.lean**: Merged `DepRel.lean` content — UD dependency relation classifiers (`isCoreArg`, `isNominal`, `isClause`, `isSubject`, `isObject`), `DepArc` structure now live alongside UPOS/UDFeatures.
- **DependencyGrammar/**: Reorganized flat directory into Core/, Formal/, Phenomena/ subdirectories (matching CCG pattern). Basic.lean + LexicalRules.lean + Nominal.lean → Core/; NonProjective.lean + HeadCriteria.lean → Formal/; Coordination, Coreference, CRDC, Inversion, LongDistance → Phenomena/.
- **DependencyGrammar/Core/Basic.lean**: Removed 14-label `DepType` in favor of full `UD.DepRel` (37 universal relations). Renamed verbose types: `Direction`→`Dir`, `ArgReq`→`ArgSlot` (with `direction`→`dir`, `category`→`cat`), `ArgStructure`→`ArgStr`.
- **DependencyGrammar/Core/LexicalRules.lean**: Removed duplicate Dir/ArgSlot/ArgStr definitions, now imports from Basic.lean.
- **Comparisons/Mueller2013.lean**: `classifyDepType` now takes `UD.DepRel` instead of `DepGrammar.DepType`.
- **Comparisons/ResultativeArgLicensing.lean**: Updated to use `ArgSlot` field names (`dir`, `cat`).
- **Comparisons/CommandRelations.lean**: Import paths updated for DG reorganization.

### Removed
- **Core/DepRel.lean**: Deleted; content merged into Core/UD.lean.

## [0.104.0] - 2026-02-07

### Added
- **RSA/Implementations/Nouwen2024.lean**: Nouwen (2024) "The semantics and probabilistic pragmatics of deadjectival intensifiers". Extends LassiterGoodman2017 with evaluative measures: `muHorrible` (peaks at extremes), `muPleasant` (peaks at norm), `muUsual` (constant). Sequential Bayesian update (`adverbUpdate` → `sequentialL1`), two-threshold intersecting semantics (Nouwen eq. 45). Goldilocks predictions: `horribly_shifts_high`, `pleasantly_concentrates_moderate`, `goldilocks_height_separation`. Zwicky vacuity: `usual_constant`, `constant_eval_uniform_update`. Grounding: `bare_prior_ratios_preserved` (bare case reduces to LG2017).
- **TruthConditional/Adjective/Intensification.lean**: Evaluative measure semantics for deadjectival intensifiers. `EvaluativeMeasure` structure, `intensifiedMeaning` (Nouwen eq. 45 conjunction). Bridge theorem: `intensified_implies_positive`. Structural Goldilocks: `muHorrible_peaks_at_extreme`, `muPleasant_peaks_at_norm`, `goldilocks_at_extreme`, `goldilocks_at_norm`.
- **Phenomena/Gradability/Intensifiers.lean**: Empirical data for deadjectival intensifiers (Nouwen 2024 Figure 2). `EvaluativeValence` (positive/negative/neutral), `IntensifierClass` (H/M), 15 `IntensifierEntry` items. Per-datum Goldilocks verification (`native_decide`): neg→H, pos→M. Per-datum Zwicky verification: neg modal→attested, pos modal→unattested.

## [0.103.0] - 2026-02-07

### Added
- **Theories/EventSemantics/RootTypology.lean**: Beavers et al. (2021) "States and changes of state" root typology. `RootType` inductive (propertyConcept vs result), `PCClass` (6 Dixon subclasses), `ResultClass` (8 Levin subclasses), `entailsChange` (key semantic distinction), `hasSimpleStative`/`verbalFormIsMarked`/`allowsRestitutiveAgain` morphosyntactic correlates. **Deepest theorem**: `semantic_determines_morphosyntax` — single biconditional deriving all morphosyntactic behavior from `entailsChange`. `bifurcationThesis` + `bifurcation_fails` (anti-bifurcation). Markedness Generalization (eq. 44): `verbalMarkedness`/`stativeMarkedness` with `markedness_complementarity`. `Markedness` inductive, `markedness_from_semantics`. Root denotations: `RootDenotation`, `MeaningPostulateEntailsChange`, `RootSemantics` (typed λ-calculus bridge). Embick (2004) `AdjectivalStructure` (basicStative vs resultStative), `admitsBasicStative_iff_no_change`. Again diagnostic: `AgainReading` (restitutive/repetitive), `againReadings`, `result_no_restitutive`/`pc_has_restitutive`. Template bridges: `requiresBECOME`, `Template.hasBECOME`, `entails_change_implies_become_template`/`no_become_implies_no_change`. Proto-roles bridge: `rootTypeFromChangeEntailment` (← `EntailmentProfile.changeOfState`). `grand_unification` theorem deriving all 7 correlates from `entailsChange`.
- **Phenomena/ChangeOfState/Typology.lean**: Crosslinguistic CoS verb typology (Beavers et al. 2021, 88-language study). `CoSRootClass`/`PCSubclass`/`ResultSubclass` (theory-neutral classification), `ParadigmPosition` (5-position paradigm), `MorphRelation` (8 relationship codes à la Haspelmath 1993). Per-root data: `RootMeaning` structure with `nSimpleStative`/`nLanguages`/`nMarkedVerbal`/`nVerbalLanguages` from Tables A1/A2 (18 roots: 8 PC + 10 result). `TypologicalComparison` for statistical summaries: `simpleStativeComparison` (PC median=95.67%, result=1.59%, U=1266.5, p<0.001) and `verbalMarkednessComparison` (PC=56.01%, result=15.20%, U=1291, p<0.001). Semantic diagnostics: `changeDenialTest`/`restitutiveAgainTest` with `diagnostics_agree`. Per-language profiles for 6 case study languages (Kakataibo, Kinyarwanda, Hebrew, Marathi, Greek, English). `LanguageType` (asymmetric/highMarking/lowMarking — 3 attested, 4th unattested). Verification: `most_pc_roots_have_statives`, `result_roots_rare_statives`.

## [0.102.0] - 2026-02-07

### Added
- **Theories/EventSemantics/EventStructure.lean**: Rappaport Hovav & Levin (1998, 2024) event structure templates. `Primitive` inductive (ACT, CAUSE, BECOME, STATE, MOVE, CONTACT), `Template` inductive (state, activity, achievement, accomplishment, motionContact), template properties (`hasCause`, `hasExternalCauser`, `predicateCount`, `vendlerClass`), argument realization (`subjectProfile`, `objectProfile`), `DeterminingPredicate` (motion vs contact for motionContact verbs), instrument lexicalization (`lexicalizeInstrument`). Bridge theorems: `motionContact_variable_agentivity` (→ sweepBasicSubjectProfile), `contact_determines_implies_effector_subject` (→ isEffector), `lexicalize_increases_agentivity` (→ pAgentScore ordering), `accomplishment_subject_is_agent`.
- **Theories/EventSemantics/ProtoRoles.lean** §12–13: Rappaport Hovav & Levin (2024) variable agentivity + effector/force-recipient. `sweepBasicSubjectProfile` (M+IE, underspecified), `sweepBroomSubjectProfile` (V+S+C+M+IE, obligatory agent), `sweep_broom_more_agentive`, `isEffector`/`isForceRecipient` predicates, `effector_has_pAgent` (≥2 P-Agent), `wind_is_effector`, `kickObject_is_forceRecipient`. Bridge theorems: `sweep_basic_underspecified`/`sweep_broom_agentive` (→ VerbEntry.subjectTheta).
- **Fragments/English/Predicates/Verbal.lean**: `sweep_basic` (underspecified agentivity) and `sweep_broom` (obligatory agent, instrument lexicalized) VerbEntry polysemy pair.

## [0.101.0] - 2026-02-07

### Added
- **Theories/EventSemantics/ProtoRoles.lean**: Dowty (1991) Proto-Roles and Argument Selection. `EntailmentProfile` structure (5 P-Agent + 5 P-Patient Bool entailments), `pAgentScore`/`pPatientScore` counting, `selectsSubject`/`selectsObject` (ASP), `allowsAlternation` (Corollary 1), `predictsUnaccusative`/`predictsUnergative` (Corollary 2). Canonical verb profiles: kick, build, see, run, arrive, die, eat, buy, sell with per-verb ASP verification theorems (`native_decide`). Bridge to Cruse (1973): `passesDoTestFromProfile` derives do-test from {volition, causation, movement}. Bridge to ThetaRole: `ThetaRole.canonicalProfile` mapping + role hierarchy theorems (`agent_outscores_instrument`/`agent_outscores_experiencer`). Bridge to Krifka (1998): `incrementalTheme` = SINC annotation. Bridge to ChangeOfState: `changeOfState` per-verb theorems. Bridge to CausativeBuilder: `causation_entailment_implies_pAgent_ge_one`. Bridge to VerbEntry: `run_unaccusative_agrees`, `arrive_verb_unaccusative`, `run_verb_not_unaccusative`. Alternation: `buy_sell_alternation`.

## [0.100.0] - 2026-02-07

### Added
- **Theories/EventSemantics/Agentivity.lean**: Cruse (1973) agentivity decomposition. `AgentivityFeature` (volitive/effective/initiative/agentive_), `AgentivityProfile` structure (4 Prop-valued predicates over entity–event pairs), `passesDoTest` (do-test as 4-way disjunction), `CruseIndependence` axiom class (4 independence witnesses), `AgentAgentiveLink` class + `agent_implies_passesDo` / `agent_is_agentive_subfeature` (Parsons agent = Cruse agentive_ bridge), `AgentivityFeature.toActionType` mapping to `CoerciveImplication.ActionType` + `coercion_requires_volitive`, `InitiativeCausativeLink` (initiative ↔ CausativeBuilder.make/force), `stative_can_pass_doTest` (volitive statives pass do-test), `agent_selects_action_consistent` (no contradiction with ThematicAxioms), `doTestPrediction` (VendlerClass → DiagnosticResult), `doTest_accepts_durative_dynamic` / `doTest_accept_implies_dynamic` / `doTest_agrees_imperative_for_non_achievements`

## [0.99.0] - 2026-02-07

### Added
- **Theories/EventSemantics/Krifka1998.lean**: Krifka (1998) "The Origins of Telicity" linking theory. `Overlap`, thematic role property hierarchy (`UP`/`CumTheta`/`ME`/`MSE`/`UE`/`MO`/`MSO`/`UO`/`GUE`, eq. 43–52), `SINC` structure (strict incrementality, eq. 51), derived properties (`me_of_mse`/`mo_of_mso`), `VP` formation by existential closure (eq. 53), **CUM propagation theorem** (`cum_propagation`: `CumTheta(θ) ∧ CUM(OBJ) → CUM(VP θ OBJ)`, fully proved), **QUA propagation theorem** (`qua_propagation`: `SINC(θ) ∧ QUA(OBJ) → QUA(VP θ OBJ)`), `ExtMeasure` class (extensive measure functions, eq. 7), `VerbIncClass` enum + `VerbIncrementality` axiom class (eat/push/build/read meaning postulates), `INC` general incrementality (eq. 59), bridge theorems (`sinc_cum_propagation`/`sinc_qua_propagation`/`qua_vendler_telic`/`cum_vendler_atelic`/`roleHom_implies_cumTheta`)

## [0.98.0] - 2026-02-07

### Added
- **Theories/EventSemantics/Mereology.lean**: Champollion (2017) algebraic event mereology over Mathlib's `SemilatticeSup`. `AlgClosure` inductive (*P, closure under ⊔), `CUM`/`DIV`/`QUA`/`Atom` higher-order mereological properties, `algClosure_cum` (closure always cumulative), `qua_cum_incompatible` (QUA+CUM contradiction for non-singletons), `atom_qua`, `IsSumHom` class (join-preserving maps) with monotonicity theorem, `EventCEM` class (enriches EventMereology with `SemilatticeSup (Ev Time)` + τ homomorphism), `LexCum` event-specific cumulativity with `cum_iff_lexCum` bridge, `RoleHom` class (θ preserves ⊕), `vendlerClass_atelic_implies_cum_intent`/`vendlerClass_telic_implies_qua_intent` aspect bridges, `algClosure_mono`/`algClosure_idempotent`
- **Theories/EventSemantics/StratifiedReference.lean**: Champollion (2017) Stratified Reference. `SR` (eq. 62: unified SR_{d,g} over AlgClosure), `SR_univ` (universal quantification), `SDR` (dimension=θ, granularity=Atom → distributivity), `SSR` (dimension=τ, granularity=proper subinterval → atelicity), `SMR` (dimension=μ, granularity=smaller → measurement), `DistConstr` unified distributivity constraint (eq. 68), `eachConstr`/`forConstr` construction instances, `VerbDistributivity` axiom class (see/kill/meet meaning postulates), `ssr_characterizes_atelic_predicates` aspect bridge, `forAdverbial_requires_ssr`, `forAdverbialMeaning`, `in_adverbial_incompatible_with_ssr` (QUA vs SSR)

## [0.97.0] - 2026-02-07

### Added
- **Theories/EventSemantics/Basic.lean**: Neo-Davidsonian event semantics foundation (Davidson 1967, Parsons 1990). `EventSort` (action/state), `Ev` structure (temporal individual + sort), sort predicates with exhaustivity/exclusivity proofs, `EventSort ↔ Dynamicity` isomorphism (roundtrip proofs), `Ev ↔ Eventuality` bridge (forgetful/lifting pair with τ-preservation), `EventMereology` class (partial order with τ-monotonicity and sort-preservation), `EvPred`/`EvPredW` event predicate types, existential closure, concrete ℤ-time examples
- **Theories/EventSemantics/ThematicRoles.lean**: Neo-Davidsonian thematic roles as two-place predicates. `ThematicRel` type alias, `ThematicFrame` structure (9 role fields including Parsons' `holder`), `ThetaRole.toRel` bridge from Fragment enum to frame fields (8 per-role verification theorems), `ThematicAxioms` class (agent-selects-action, holder-selects-state, uniqueness), `agent_holder_disjoint` derived theorem, neo-Davidsonian logical forms (transitive/intransitive/ditransitive), `EventModifier` + `modify` with commutativity and associativity proofs, per-verb VerbEntry grounding theorems (`kick`, `give`, `see`), toy model example with `john_kicked_mary` witness

## [0.96.0] - 2026-02-06

### Added
- **Fragments/English/PolarityItems.lean**: `ScalarDirection` enum (strengthening/attenuating/nonScalar) from Israel (1996, 2011); added `scalarDirection` field to `PolarityItemEntry`; tagged `ever`→strengthening, `any`→strengthening, `atAll`→attenuating, `liftAFinger`→nonScalar
- **TruthConditional/Domain/Degree.lean**: `ModifierDirection` (amplifier/downtoner), `DegreeModifier` structure with threshold-shifting semantics (θ + δ for amplifiers, θ - δ for downtoners); modifier instances (`slightly`, `kindOf`, `quite`, `very`, `extremely`) with Machino et al. (2025) strength hierarchy
- **NeoGricean/Exhaustivity/Chierchia2004.lean**: `StrengthRelation` (strongerThan/weakerThan), `scalarLicensing` parametrized by direction; bridge theorem proving `scalarLicensing .strongerThan` = `krifkaRule`
- **Phenomena/Polarity/NPIs.lean**: `scalarDirection` field on `CrossLingNPI`; `germanSoRecht` (attenuating NPI); tagged `germanJemals`→strengthening
- **Phenomena/Polarity/Studies/Schwab2022.lean**: Schwab (2022) NPI illusion experimental data (2×3 factorial); `IllusionAsymmetry` structure; `illusion_asymmetry_from_scalar_direction` theorem connecting `ScalarDirection` to illusion predictions
- **Phenomena/Politeness/Studies/MachinoEtAl2025.lean**: Machino et al. (2025) cross-cultural modifier interpretation data; 5 modifiers × 2 cultures; cross-cultural "quite" asymmetry (AmE amplifier vs BrE downtoner); politeness ratings

## [0.95.1] - 2026-02-06

### Changed
- **MCB2023/FreeMagmaEquiv.lean**: Added `leafCount_eq_freeMagma_length` and `leafCount_pos` — bridge SO.leafCount to mathlib's `FreeMagma.length` (positivity comes free from `FreeMagma.length_pos`)
- **MCB2023/BinaryOptimality.lean**: Added `freemagmaNodeCount_eq_length_sub` and `nodeCount_eq_freeMagma_length_sub` — bridge nodeCount to `FreeMagma.length - 1`; added `NaryTree.nodeCount` and `nary_leaf_node_relation`; proved `nary_leaf_count_mod` (was sorry) via leaf-node relation; proved `binary_achieves_all` (was sorry) via `NaryTree.expandLeaf`; added `NaryTree.expandLeaf` + `expandLeaf_leafCount`. **BinaryOptimality.lean now has zero sorrys.**
- **MCB2023/Accessible.lean**: Rewrote `numAcc`/`numVertices` using `List.map`/`List.sum` (was `foldl`); added `numAcc_eq_numVertices` replacing `foldl_acc_eq_vert`; added `Multiset`-valued `leafMultisetM` and `accessibleTermsM`; proved `im_b0_preserved` (was sorry) via `length_filter_bne_of_count_one`
- **MCB2023/Coproduct.lean**: Refactored `AdmissibleCut` to use `Finset` + mathlib's `IsAntichain contains` (was `List` + manual pairwise condition); proved `quotientTree_some_of_contains` (was sorry) via structural induction on SO; proved `quotientTree_leafCount` (was sorry) via auxiliary `quotientTree_implies_containsOrEq` and `leafCount_le_of_containsOrEq`; proved `coproduct_size_identity` (was sorry) from `quotientTree_leafCount`. **Coproduct.lean now has zero sorrys.**

## [0.95.0] - 2026-02-06

### Added
- **Minimalism/Formal/MCB2023/FreeMagmaEquiv.lean**: Marcolli, Chomsky & Berwick (2023) §1 — SO ≅ FreeMagma bridge
  - `toFreeMagma`/`fromFreeMagma`: explicit maps between `SyntacticObject` and `FreeMagma LIToken`
  - `soFreeMagmaEquiv`: the type equivalence `SyntacticObject ≃ FreeMagma LIToken`
  - `Mul SyntacticObject` instance: positions Merge as a magma operation
  - `toFreeMagmaMulHom`: magma homomorphism `SO →ₙ* FreeMagma LIToken`
  - `SyntacticObject.liftMagma`: universal property — lift any `LIToken → M` to `SO →ₙ* M`
  - `contains_iff_properSubterm`: proven — containment = proper subterm in free magma
- **Minimalism/Formal/MCB2023/Accessible.lean**: MCB2023 §2 — accessible terms + workspace counting
  - `subtrees`, `properSubtrees`, `internalNodes`: subtree extraction functions
  - `leafMultiset`, `accessibleTerms`: frontier tokens and accessible terms (Def 2.4)
  - `b₀`, `numAcc`, `wsSize`, `wsSizeAlt`: workspace counting functions (eq 2.8–2.9)
  - `wsSize_eq_wsSizeAlt`: proven — σ̂ = σ
  - `SidewardMerge` structure + `sideward_violates_b0`: proven — sideward adds a component
  - Proposition 2.17 counting theorems (EM/IM behavior) stated with sorry
- **Minimalism/Formal/MCB2023/BinaryOptimality.lean**: MCB2023 §4 — binary optimality + Catalan
  - `NaryTree`: n-ary tree type generalizing SyntacticObject
  - `achievableLeafCounts`: achievable leaf counts for n-ary Merge
  - `nary_misses_two`: proven (modulo `nary_leaf_count_mod`) — n≥3 can't achieve leaf count 2
  - `binary_unique_optimal`: proven — binary is the only n≥2 achieving all leaf counts (Lemma 4.4)
  - `tree_shapes_catalan`: binary tree shapes with n nodes = catalan n (via mathlib)
- **Minimalism/Formal/MCB2023/Coproduct.lean**: MCB2023 §2.2–2.3 — coproduct structure
  - `quotientTree`: T with subtree at v contracted to a leaf (Def 2.5)
  - `AdmissibleCut`: admissible cuts as pairwise-incomparable node sets
  - `leadingCoproduct`: Δ₍₂₎(T) = Σᵥ Tᵥ ⊗ T/Tᵥ (eq 2.16)
  - `listExternalMerge`/`listInternalMerge`: Merge lifted to workspace lists
  - `workspace_merge_recovers_merge`: proven — algebraic formulation recovers simple Merge
  - `workspace_merge_partition`: proven — EM/IM partition aligns with containment
- **Linglib.lean**: Registered 4 new MCB2023 files

## [0.94.0] - 2026-02-06

### Added
- **NeoGricean/Exhaustivity/Chierchia2004.lean**: Chierchia (2004) parallel recursive strengthening architecture
  - `StrengthenedMeaning`: plain + strong + alternatives at every compositional node
  - `krifkaRule`: direct implicature introduction at scope sites (Krifka 1995)
  - `strengthCondition`: ‖α‖^S must entail ‖α‖, else fallback
  - `IsDE`, `pneg_isDE`: DE-ness for `Prop' World = World → Prop`
  - `strongApply`: DE-sensitive function application (84) — the formal heart of the paper
  - `si_npi_generalization`: proven — SIs suspended in exactly NPI-licensing (DE) contexts
  - `de_blocks_direct_si`: proven — DE functions weaken Krifka-strengthened arguments
  - `domainExhaustify`: O operator for NPI domain widening (127)
  - `npi_blocked_under_de`: proven — DE reverses NPI strengthening
  - `ScalarStrength`, `intervenes`: intervention effects from strong scalar items (§4.3)
  - `scaleAxiomsSatisfied`: Chierchia's scale axioms (99a–c)
  - `root_ue_bridge`: **proven** — Krifka output entails exhIE on flat scales
- **Linglib.lean**: Registered `Chierchia2004`

## [0.93.0] - 2026-02-06

### Added
- **Core/QUD.lean**: `QUD.ofDecEq` smart constructor using `DecidableEq` instead of `BEq`+`LawfulBEq`
- **Core/CommonGround.lean**: `BContextSet` decidable context set type with `toProp`, `update`, `filterWorlds`, `entails`, and bridge theorems to classical `ContextSet`
- **Core/Proposition.lean**: `FiniteWorlds.ofFintype`/`toFintype` bidirectional bridges between `FiniteWorlds` (47+ files) and `Fintype` (26+ RSA files)
- **Core/Interfaces/FelicityCondition.lean**: Unified felicity/oddness interface (`FelicityCondition` typeclass, `FelicityStatus`, `OddnessSource`, `FelicityResult`) following `ImplicatureTheory` pattern
- **QuestionSemantics/EconomyOddness.lean**:
  - `needlesslyInferiorStrict`: context-aware Answer Condition that also checks dominating alternative is CK-compatible
  - `SemanticModel`, `DiscourseContext`, `Scenario.mk'`: composable scenario infrastructure
  - 5 verification theorems showing `needlesslyInferiorStrict` agrees with `needlesslyInferior` on all scenarios
  - Composability demo: `deModel` reused with two different discourse contexts
- **Linglib.lean**: Registered `FelicityCondition`

### Changed
- Simplified all 5 EconomyOddness QUDs from manual 4-line match blocks to `QUD.ofDecEq id`

## [0.92.0] - 2026-02-06

### Added
- **QuestionSemantics/EconomyOddness.lean**: Katzir & Singh (2015) economy-based oddness
  - `Scenario`: discourse scenario packaging meaning, complexity, context, QUD, alternatives
  - `badQuestion`: Question Condition violation (QUD trivially settled by CK)
  - `atLeastAsGood`, `betterThan`: K&S def 16 combining structural complexity + semantic strength
  - `needlesslyInferior`, `isOdd`: Answer Condition violation + unified oddness predicate
  - Spector (2014) `isTrivialInC`, `allAlternativesTrivial`: triviality definitions for comparison
  - 5 concrete scenarios with `native_decide` verified predictions:
    - Magri/Spector: both some/all odd via Question Condition + Spector bridge theorem
    - Needlessly weak: "some" odd / "all" ok via Answer Condition (grade paradigm)
    - Hurford: "France or Paris" odd via needless complexity
    - DE reversal: opposite oddness verdicts in DE vs UE (`ue_de_oddness_flips`)
    - Maximize Presupposition: "a sun" odd / "the sun" ok from Answer Condition
  - `conditions_independent`: Question and Answer Conditions are logically independent
- **Linglib.lean**: Registered `EconomyOddness`

## [0.91.0] - 2026-02-06

### Added
- **Sentence/Tense/TenseAspectComposition.lean**: Knick & Sharf (2026) tense–aspect composition
  - `evalPres`, `evalPast`, `evalFut`: tense evaluation operators bridging `PointPred` to `W → Prop`
  - `simplePresent`, `simplePast`, `presPerfProg`, `presPerfSimple`, `presPerfProgXN`, `pastPerfProg`: composed tense–aspect forms
  - `simplePresent_unfold`, `presPerfProgXN_unfold`: definitional unfold theorems
  - `u_perf_entails_simple_present`: U-perf(tᵣ) → simple present (K&S Thm 3)
  - `broad_focus_equiv`: U-perf(Set.univ) ↔ simple present (K&S Thm 4)
  - `earlier_lb_stronger_impf`, `later_lb_stronger_prfv`: LB monotonicity (K&S Thms 5–6)
  - `earlier_lb_not_weaker_impf`: converse of Thm 5 is false (K&S Thm 7)
- **Sentence/Tense/TemporalAdverbials.lean**: Temporal adverbials and PTS constraints
  - `PTSConstraint`, `AdverbialType` (durative/inclusive, Iatridou et al. 2001)
  - `everSince`, `forDurationFrom`, `always`, `before`: concrete adverbials
  - `PTSConstraint.toLBDomain`: convert adverbial to LB domain for PERF_XN
  - `PERF_ADV`: perfect with adverbial constraint
  - `perf_adv_eq_perf_xn`, `everSince_specifies_lb`, `before_no_lb_constraint`: bridge theorems
  - `durative_licenses_u_perfect`, `inclusive_no_u_license`: Iatridou classification bridges
- **Linglib.lean**: Registered `ViewpointAspect`, `TenseAspectComposition`, `TemporalAdverbials`

## [0.90.0] - 2026-02-06

### Added
- **Minimalism/Formal/ExtendedProjection/Basic.lean**: Grimshaw (2005) Extended Projection theory
  - `CatFeatures`, `catFeatures`: [±V, ±N] decomposition computed over existing `Cat`
  - `fValue`: functional level (F0–F3) within extended projections
  - `categoryConsistent`, `fMonotone`: EP well-formedness constraints
  - `CatFamily`: verbal/nominal/adjectival/adpositional category families
  - `ExtendedProjection` structure with `computeEPSpine`, `mkExtendedProjection`
  - 12 bridge theorems (chain consistency, F-value monotonicity, family consistency)
- **Minimalism/Formal/ExtendedProjection/Properties.lean**: Derived EP properties
  - `EPSemanticType`: maps EP levels to semantic types (property/proposition/entity/intermediate)
  - `canAssignTheta`: Generalized Theta Criterion (only F0 heads assign theta roles)
  - `isEPInternal`/`isEPExternal`: complement vs specifier in EP terms
  - `argumentDomainCat`, `isInArgumentDomain`: Anand et al. (2025) argument domain boundary
  - Standard/truncated EP spines (`fullVerbalEP`, `infinitivalEP`, small clause variants)
  - 18 bridge theorems connecting EP levels, argument domains, and truncation
- **Minimalism/Formal/Sluicing/FormalMatching.lean**: Anand, Hardt & McCloskey (2025) SIC
  - `ArgumentDomain`, `HeadPair`, `extractHeadPairs`: argument domain structure
  - `lexicallyIdentical`, `structurallyIdentical`: syntactic identity (Defs 5–6)
  - `SluicingLicense` with `isLicensed`: Syntactic Isomorphism Condition
  - Bridge theorems: voice mismatch outside argument domain, case matching, small clause predictions
  - Bridge to `Phenomena/Ellipsis/Sluicing.lean` empirical data

## [0.89.0] - 2026-02-06

### Changed
- **Core/UD.lean** (new): Merged `Core/UPOS.lean` + `Core/UDFeatures.lean` into single file
- **Core/Basic.lean**: Removed `abbrev Cat := UD.UPOS` and `Cat` namespace — all 18 consumer files now use `UD.UPOS` directly with native constructors (`.DET`, `.NOUN`, `.VERB`, `.AUX`, `.SCONJ`, `.PRON`, `.ADP`, `.ADJ`)
- **Phenomena/Coordination/Data.lean**: Converted from `Word`-based `PhenomenonData` to string-based `StringPhenomenonData` — no more feature dictionaries in empirical data

## [0.88.0] - 2026-02-06

### Added
- **Phenomena/FillerGap/Sag2010.lean**: Sag (2010) F-G construction typology — 5 clause types × 7 parameters
  - `FGClauseType`: whInterrogative, whExclamative, topicalized, whRelative, theClause
  - `FGParameters`: fillerWhType, headInversion, headFiniteness, semanticType, isIsland, independence, fillerIsNonverbal
  - `fgParams`: maps each clause type to its parameter values
  - `WhWordProfile` + `whWordProfiles`: Table 1 wh-word × construction participation
  - Per-datum verification: `only_interrogative_requires_inversion`, `all_fillers_nonverbal`, `island_constructions_are`, etc.
  - Bridge to Islands/Data: `islandConstructions` connects island parameter to `ConstraintType`
  - Bridge to ClauseType: `interrogative_maps_to_question_clause`, `topicalized_maps_to_declarative`
- **HPSG/HeadFiller.lean**: GAP restrictions for construction-specific islands (Sag 2010, p.514)
  - `GapRestriction`: unrestricted, npOnly, noGap — derives island effects from GAP feature
  - `SlashValue.satisfiesRestriction`: checks GAP compatibility
  - `empty_satisfies_any_restriction`: empty SLASH always satisfies any restriction
- **Comparisons/Islands.lean**: Sag 2010 bridge connecting grammar-based and processing-based islands
  - `complementary_coverage`: Sag's grammatical islands (topicalization, exclamatives) + H&S processing islands = complete coverage
  - `sag_island_subset`: grammatical islands are a proper subset of all F-G types

## [0.87.0] - 2026-02-06

### Changed
- **Core/ProcessingModel.lean** (new): Shared axiomatic processing model replacing ad hoc cost functions
  - `ProcessingProfile`: 4-dimensional profile (locality, boundaries, referentialLoad, ease)
  - `CompareResult` + Pareto dominance via `ProcessingProfile.compare` — no magic weights
  - `HasProcessingProfile` typeclass: any module claiming processing predictions must provide an instance
  - Monotonicity axioms (stated with `sorry`): locality/boundaries/referentialLoad monotone increasing difficulty, ease monotone decreasing
  - `OrderingPrediction` + `verifyOrdering`: verify empirical orderings via Pareto dominance
- **Comparisons/Islands.lean**: Replaced `IslandProcessingCost`/`estimateIslandCost`/`islandThreshold` with `ProcessingProfile` and Pareto comparison
  - `IslandCondition` enum + `HasProcessingProfile` instance
  - Ordering theorems now use `.compare` returning `.harder`/`.easier` instead of numeric `<`
  - `all_ordering_predictions_verified`: all H&S ordering predictions pass via shared `verifyOrdering`
- **Comparisons/ScopeFreezing.lean**: Replaced `ProcessingComplexity`/`estimateCost`/`inverseThreshold` with `ProcessingProfile` and Pareto comparison
  - `ScopeCondition` enum + `HasProcessingProfile` instance
  - `TheoryPredictions.processing` now `CompareResult` instead of `Bool`
  - `processingPredictsFreezing` uses Pareto dominance against baseline
  - `all_scope_ordering_predictions_verified`: shared verification infrastructure
- **Core/Empirical.lean**: Added `ProcessingDimension`, `taskSensitiveDimensions`, `ProcessingObservation` linking empirical tasks to processing profile dimensions

## [0.86.0] - 2026-02-06

### Added
- **Islands/Data.lean**: Hofmeister & Sag (2010) processing factors and gradient acceptability data
  - `ProcessingFactor`: locality, referentialLoad, clauseBoundary, fillerComplexity
  - `FillerType` (bare/whichN), `IslandNPType` (definite/plural/indefinite)
  - `cnpcAcceptability`: 6 conditions from Experiment 1 (Figure 3)
  - `whIslandAcceptability`: 2 conditions from Experiment 2 (Figure 5)
  - `cnpc_whichN_gt_bare`, `whIsland_whichN_gt_bare`: filler complexity effects
  - `cnpc_indefinite_gt_definite`: NP type effect
  - `best_island_lt_baseline`: islands ameliorated but not eliminated
- **Comparisons/Islands.lean**: Competence vs performance comparison for island effects
  - `IslandProcessingCost`: 4-dimensional cost model with superadditive interaction
  - `filler_reduces_cnpc_cost`, `filler_reduces_whIsland_cost`: filler complexity paradox
  - `cost_matches_acceptability_ordering`: model predictions match empirical data
  - `processing_scores_4_of_4`, `competence_scores_0_of_4`: processing wins on all nonstructural manipulations
  - `cnpc_acceptability_range`: 25+ point gradient within "strong" island — challenges binary classification
  - Parallels `Comparisons.ScopeFreezing` structure

## [0.85.0] - 2025-02-05

### Changed
- **CausalModel.lean**: `causallySufficient`, `causallyNecessary` consolidated from Sufficiency/Necessity
  - Pearl's counterfactual queries now live with the causal model infrastructure
  - New `CausalProfile` structure packages sufficient/necessary/direct properties
  - `extractProfile` computes profile from any `CausalDynamics`
- **Sufficiency.lean / Necessity.lean**: re-export definitions; downstream `open` statements unchanged
- **Integration.lean**: `extractParams` derives from `CausalProfile` via `DeterministicParams.ofProfile`
- **BellerGerstenberg2025.lean**: `causalWorldFromModel` uses `extractProfile`

## [0.84.0] - 2025-02-05

### Changed
- **Resultatives.lean**: Tightness now grounded in causal model semantics, not graph inspection
  - Tightness ≡ `completesForEffect` (runs `normalDevelopment` under counterfactual intervention)
  - Levin (2019) §4 "drink teapot dry" (passive chain): tight despite no direct law
  - Levin (2019) §7 *"kick door open via ball" (active chain): not tight — independent energy source
  - `hasIndependentSource`: formalizes Levin's "intervening causer" criterion
  - `independent_source_disrupts_tightness`: central theorem connecting energy sources to necessity
  - `ContiguityType`: container–contents, contents–container, impingement
  - Moved from `ConstructionGrammar/Studies/GoldbergJackendoff2004/Bridge.lean` to `Causative/`
- **CausalModel.lean**: `hasDirectLaw`, `hasIndependentSource` extracted to shared location
- **BellerGerstenberg2025.lean**: uses shared `hasDirectLaw` from CausalModel
- **Linglib.lean**: Resultatives import grouped with other Causative imports

### Removed
- Dead code from Sufficiency.lean (`sufficientIn`, `makeExtended`, `uncausable`, weak/strong sufficiency)
- Dead code from Necessity.lean (`necessaryIn`, `causeExtended`, `butForCause`)
- Dead code from CoerciveImplication.lean (`CausativeChoice`, `recommendVerb`, `makeVolitional`, etc.)
- Verbose docstrings trimmed across all causative files

## [0.83.0] - 2025-02-05

### Added
- **Causative/Resultatives.lean**: Levin (2019) tightness + cross-module convergence
  - `prevent_incompatible_with_resultative`: prevent builder can't be resultative CAUSE
  - `thick_manner_resultative_convergence`: three independent paths converge on `.make`/`makeSem`
  - `thin_incompatible_with_resultative_cause`: thin → `.cause` ≠ resultative `.make`
- **BellerGerstenberg2025.lean**: Bridge to structural causal models
  - `causalWorldFromModel`: computes B&G's W-H-S from `CausalDynamics` + `Situation`
  - W ≈ `causallyNecessary`, H ≈ `hasDirectLaw`, S ≈ `causallySufficient`
  - `solo_cause_world`/`overdetermination_world`/`chain_world`: three archetypal scenarios
  - `chain_not_caused`/`chain_still_enabled`: indirect causation → "enabled" not "caused"
  - `bg_caused_vs_nl_cause_diverge`: B&G expression semantics vs N&L verb semantics diverge
- **ProductionDependence.lean**: `single_pathway_concrete` (proved P-CAUSE→D-CAUSE for concrete variables)

## [0.82.0] - 2025-02-05

### Added
- **Causative/ProductionDependence.lean** (NEW): Martin, Rose & Nichols (2025) thick/thin causatives
  - `CausationType`: `.production` (P-CAUSE) vs `.dependence` (D-CAUSE)
  - `ThickThinClass`: `.thickManner`, `.thickState`, `.thin` with derived properties
  - Asymmetric entailment: P-CAUSE → D-CAUSE (single-pathway sufficiency implies necessity)
  - Bridges: `CausationType.analogousBuilder`, `productionConstraint`, `strongASRCompatible`
  - Production entails directness (§6, Wolff 2003)
- **Phenomena/Causatives/ThickThin.lean** (NEW): Table 3 corpus survey data (25 of 37 verbs)
  - `ThickThinEntry` structure with 4 binary properties per verb
  - All 13 thick verbs + 12 representative thin verbs
  - Correlation theorems: thick↔ASR, thin↔omission subjects
  - Bridge to `ThickThinClass` and production constraint
- **Fragments/English/Predicates/Verbal.lean**: 5 lexical causative entries
  - `kill`, `break_verb`, `burn_verb`, `destroy_verb`, `melt_verb` (all `.make` builder)
  - Theorems: `lexical_causatives_use_make`, `lexical_causatives_assert_sufficiency`

## [0.81.0] - 2025-02-05

### Changed
- **Causative/Builder.lean**: Redesigned `CausativeBuilder` from binary sufficiency/necessity to 5 force-dynamics-inspired builders (Wolff 2003, Talmy 1988): `.cause`, `.make`, `.force`, `.enable`, `.prevent`
  - N&L's sufficiency/necessity now derived via `assertsSufficiency`/`assertsNecessity`
  - Force-dynamic properties: `isCoercive` (force), `isPermissive` (enable)
  - New `preventSem`: dual of `causeSem` (blocks effect that would otherwise occur)
  - Derivation theorems: `sufficiency_builders_use_makeSem`, `make_force_same_truth_conditions`, `prevent_cause_duality`
- **Fragments/English/Predicates/Verbal.lean**: Updated 6 causative verbs to new builders
  - cause→`.cause`, make/have/get→`.make`, force→`.force`, let→`.enable`
  - New theorems: `force_is_coercive`, `let_is_permissive`, `causative_builders_distinguished`
- **GradedCausation.lean**: Updated bridge to new builders (`make_force_both_assert_sufficiency_different_profiles`)
- **GoldbergJackendoff2004/Bridge.lean**: Updated resultative builder `.sufficiency`→`.make`

### Added
- **Phenomena/Causatives/Typology.lean** (NEW): Song (1996) cross-linguistic causative typology
  - COMPACT/AND/PURP construction types with implicativity property
  - Cross-linguistic data: English *kill*, Turkish *-dür*, Japanese *-(s)ase*, French *faire*, Korean *-ke ha-*, Vata *le*
- **Fragments/Korean/Predicates.lean** (NEW): Korean causative predicates
  - PURP-type *-ke ha-* (`.cause` builder, non-implicative) and COMPACT *-i-* (`.make`)
- **Fragments/French/Predicates.lean** (NEW): French causative predicates
  - *faire* (`.make`) and *laisser* (`.enable`, permissive)
- **Fragments/Japanese/Predicates.lean**: Added causative *-(s)ase-* entries (`.make`)
- **Fragments/Turkish/Predicates.lean**: Added causative *-dür-* entries (`.make`)

## [0.80.0] - 2025-02-05

### Added
- **Causative/GradedCausation.lean** (NEW): Cao, White & Lassiter (2025) graded causative semantics
  - Three causal measures: SUF (sufficiency), INT (intention), ALT (alternatives)
  - `deterministicSuf`: bridges probabilistic SUF to binary `causallySufficient` (grounding theorem)
  - `altToActionType`: bridges graded ALT to binary `ActionType` from `CoerciveImplication`
  - Per-verb interaction profiles (Table 1): unique reliable interactions per verb
  - `make_has_unique_sufInt`: *make* uniquely has SUF×INT interaction
  - `make_force_same_builder_different_profiles`: same CausativeBuilder but different profiles
  - `graded_subsumes_binary`: graded model reduces to binary in deterministic limit
  - Main effect coefficients with `suf_largest_main_effect` theorem
- **Phenomena/Causatives/Data.lean** (NEW): Experimental data from Cao et al. (2025)
  - Acceptance rates: caused (48%) > made (40%) > forced (35%)
  - Regression coefficients from Model I (SUFresidALT, INT, ALT) with reliability checks
  - Acceptability contrasts from examples (5)-(7)

## [0.79.3] - 2025-02-05

### Changed
- **Core/CausalModel.lean**: Moved from `Theories/IntensionalSemantics/Conditional/` to `Core/`
  - Pearl-style structural causal model infrastructure is framework-agnostic, belongs in Core
  - Namespace: `Theories.TruthConditional.Conditional.CausalModel` → `Core.CausalModel`
  - Updated imports/opens across ~12 files (Causative/*, Conditional/Counterfactual, Bridge)

## [0.79.2] - 2025-02-05

### Changed
- **Causative/Builder.lean** (NEW): `CausativeBuilder` in Theory layer, replacing `CausativeType` in Fragment
  - Like `PreferentialBuilder` for attitudes: builder names the semantic analysis, properties are DERIVED
  - `CausativeBuilder.toSemantics`: maps `.sufficiency` → `makeSem`, `.necessity` → `causeSem`
  - Derivation theorems: `sufficiency_implies_causallySufficient`, `necessity_implies_causallyNecessary`
  - `builders_truth_conditionally_distinct`: proved via overdetermination witness
- **Fragments/English/Predicates/Verbal.lean**: Replaced `CausativeType` with `CausativeBuilder`
  - Removed Fragment-level `CausativeType` definition; now imports from Theory layer
  - `causativeType` field → `causativeBuilder` field in `VerbEntry`
  - Grounding theorems: `make_semantics` (→ `makeSem`), `cause_semantics` (→ `causeSem`)
  - Cross-verb consistency: `sufficiency_verbs_share_semantics` (make, let, have, get, force)
- **GoldbergJackendoff2004/Bridge.lean**: Updated to use `CausativeBuilder`
  - `resultativeCausativeBuilder` replaces `resultativeCausativeType`

## [0.79.1] - 2025-02-05

### Changed
- **Theories/ConstructionGrammar/Studies/GoldbergJackendoff2004/Bridge.lean**: Deep causal dynamics integration
  - Concrete `CausalDynamics` models for resultative scenarios (hammer flat, kick into field, laugh silly, freeze solid)
  - Structural `causallySufficient` proofs: verbal subevent → result state via `normalDevelopment`
  - Structural `causallyNecessary` proofs: no overdetermination in canonical resultatives
  - Both `makeSem` and `causeSem` verified for canonical causative resultatives
  - Noncausative resultatives = empty `CausalDynamics` (no causal law, `causallySufficient` = false)
  - CC-selection formalization (Baglini & Bar-Asher Siegal 2025): `CCSelectionMode` with member vs completion
  - `completesForEffect`: BBS2025 completion event in causal model terms (sufficient + necessary)
  - `isCompletionEvent`: combines causal completion with G&J temporal constraint (Principle 33)
  - `resultative_cause_matches_make_verb` / `resultative_cause_differs_from_cause_verb`: cross-module verification

## [0.79.0] - 2025-02-05

### Added
- **Theories/ConstructionGrammar/Studies/GoldbergJackendoff2004.lean**: Goldberg & Jackendoff (2004) "The English Resultative as a Family of Constructions"
  - Four subconstructions (causative/noncausative × property/path RP) with `ResultativeSubconstruction`
  - Dual subevent structure (`DualSubevent`): verbal + constructional subevents linked by typed relations (MEANS, RESULT, INSTANCE, CO-OCCURRENCE)
  - Full Argument Realization (FAR) and Semantic Coherence predicates
  - Aspectual profile derivation: bounded RP → telic (accomplishment), unbounded → atelic (activity)
  - 8 empirical entries with per-datum verification theorems (subconstruction classification, subevent relations, CAUSE/BECOME presence)
  - Inheritance network: all four subconstructions inherit from parent `resultative` in ArgumentStructure.lean
  - Decomposition proofs: causative → [HS, HC, HC], noncausative → [HS, HC]
- **Theories/ConstructionGrammar/Studies/GoldbergJackendoff2004/Bridge.lean**: Cross-theory bridges
  - CxG ↔ Causative/Sufficiency: causative resultatives map to `causallySufficient`
  - CxG ↔ Aspect: resultative telicizes activity verbs (reuses `telicize_activity`)
  - CxG ↔ ChangeOfState: constructional BECOME maps to `CoSType.inception` with presupposition bridge
  - CxG ↔ Müller decomposability: all subconstructions decompose into universal schemata
- **Comparisons/ResultativeArgLicensing.lean**: Cross-theory comparison of argument licensing
  - Three theories: Minimalism (theta criterion), CxG (FAR + Semantic Coherence), DG (valency)
  - Convergence on canonical resultatives: all predict [Agent, Patient, ResultState]
  - Divergence on fake reflexives: CxG handles via construction-licensed roles; Minimalism has role deficit
  - Semantic Coherence generalizes Theta Criterion: proven that CxG's system strictly subsumes theta 1-to-1 mapping
- **Phenomena/Constructions/Resultatives/Data.lean**: Theory-neutral empirical data
  - 14 grammaticality judgments across all 5 resultative types (incl. fake reflexives)
  - 4 aspectual contrast pairs (in/for-adverbial tests for telicity)
  - Per-datum verification theorems

## [0.78.0] - 2025-02-05

### Added
- **Core/Interfaces/CombinationSchema.lean**: Theory-neutral interface for Müller's (2013) three universal combination schemata (Head-Complement, Head-Specifier, Head-Filler) with `HasCombinationSchemata`, `HasHeadFeaturePrinciple`, `HasCoordination` typeclasses
- **Theories/HPSG/HeadFiller.lean**: HPSG's third schema — Head-Filler Schema with SLASH feature infrastructure (`SlashValue`, `SynsemSlash`, `HeadFillerRule`), unified `HPSGSchema` inductive covering all three ID schemata
- **Theories/HPSG/LexicalRules.lean**: Valence-changing lexical rules (passive, resultative, dative shift) with `applyLexRule`, proofs that lexical rules preserve head features and enable coordination
- **Theories/DependencyGrammar/NonProjective.lean**: Non-projective (crossing) dependencies for long-distance phenomena, `depsCross`, `FillerGapDep`, `isWellFormedNonProj` — DG analogue of Internal Merge / Head-Filler
- **Theories/ConstructionGrammar/ArgumentStructure.lean**: Argument structure constructions (Goldberg 1995) with slot decomposition into combination schemata, concrete constructions (ditransitive, caused-motion, resultative), `isDecomposable` predicate, irreducibility proofs for PAL and *let alone*
- **Theories/Minimalism/Bridge/CombinationSchemata.lean**: Classification of Merge into three schemata — External Merge with selection = Head-Complement, without = Head-Specifier, Internal Merge = Head-Filler, with exhaustiveness proof and concrete examples
- **Comparisons/Mueller2013.lean**: Cross-theory comparison formalizing Müller (2013) "Unifying Everything" — classification functions for all five theories, labeling convergence theorem, External Merge ↔ Head-Complement ↔ Application correspondence, Internal Merge ↔ Head-Filler ↔ Composition, coordination diagnostic, "both directions right" theorem

## [0.77.0] - 2025-02-05

### Added
- **Theories/ConstructionGrammar/Studies/KayFillmore1999.lean**: *What's X doing Y?* construction
  - WXDY construction definition (partially open, interrogative form + expressive function)
  - FKO1988 idiom classification bridge: WXDY as formal idiom (encoding, grammatical, formal)
  - CxG inheritance network: inherits from wh-questions, progressive, rhetorical Q family
  - Presupposition bridge: `wxdyPresup` → `PrProp`, projection through negation
  - Two-dimensional semantics bridge: `wxdyTwoDim` → `TwoDimProp`, CI projection + independence
  - Hamblin question bridge: literal = `which`; incredulity = degenerate single-answer Q
  - Left Periphery bridge (deepest): PerspP disambiguates readings via veridical/ignorant models
  - Common ground bridge: presupposition requires CG entailment
  - Aspect bridge: progressive requirement derives from durative ∧ dynamic constraint
  - Domain widening bridge: incongruity = normative alternative source (same as counterexpectational *just*)
  - Polarity bridge: incredulity = rhetorical question requiring polar form
  - ~20 bridge theorems across 10 modules
- **Phenomena/Constructions/Studies/KayFillmore1999.lean**: WXDY empirical data
  - 18 examples: basic incredulity, literal question, progressive requirement, subject referentiality, complement types, ambiguous, embedding/CI projection, FKO1988 comparison
  - Three reading types (literal, incredulity, ambiguous) with verification
  - Progressive requirement verification across all grammatical non-literal examples

## [0.76.0] - 2025-02-05

### Added
- **Theories/ConstructionGrammar/Basic.lean**: Core CxG types (Construction, Constructicon, Specificity, InheritanceMode, InheritanceLink)
- **Theories/ConstructionGrammar/Studies/FillmoreKayOConnor1988.lean**: *Let alone* construction
  - Idiom typology: encoding/decoding, grammatical/extragrammatical, substantive/formal (§1.1–1.2)
  - Scalar model formalization: n-dimensional argument space with monotonicity constraint (Appendix Def A3)
  - *Let alone* construction with semantic conditions (scalar entailment, same polarity, A stronger than B)
  - *Let alone* family (*much less*, *not to mention*, *if not*, *in fact*) with clause-ordering distinction
  - Pragmatic analysis: Gricean Quantity/Relevance conflict (§2.4)
  - NPI trigger inventory (§2.2.4)
  - Bridge 1: NPI triggers → `Polarity.NPIs.LicensingContext` mapping
  - Bridge 2: Phenomena judgment data verification (`barely_licenses_let_alone`, `almost_blocks_let_alone`)
  - Bridge 3: Military rank scalar model with entailment proofs (`general_stronger_than_colonel`)
  - The X-er the Y-er and Incredulity Response constructions
- **Theories/ConstructionGrammar/Studies/GoldbergShirtz2025.lean**: PAL construction analysis
  - PAL construction + 4 conventional subtypes (must-VERB, a simple ⟨PAL⟩, Don't PAL me, the old ⟨PAL⟩ N)
  - Inheritance network from NN compounds and Adj+N modification (Figure 5)
  - Presupposition bridge: `palPresupposition` connects to `Core.Presupposition.PrProp`
  - Two-dimensional meaning: `palTwoDim` connects to `TruthConditional.Expressives.TwoDimProp`
  - 4 core claims with proofs (form-function, familiarity presupposition, rhetorical effects, cross-linguistic)
- **Phenomena/Constructions/Studies/FillmoreKayOConnor1988.lean**: *Let alone* judgment data
  - 24 examples with 4-way judgments (grammatical/ungrammatical/marginal/anomalous)
  - NPI licensing contrasts (barely vs almost vs only)
  - Topicalization, VP ellipsis, IT-cleft asymmetries vs *and*-coordination
  - Scalar anomaly examples (swapped foci)
  - Positive polarity counterexamples
- **Phenomena/Constructions/Studies/GoldbergShirtz2025.lean**: Empirical data
  - Studies 1a/1b (common knowledge), 2 (wit), 3 (sarcasm), 5 (conventional subtypes)
  - Cross-linguistic PAL attestations (German, Dutch, Afrikaans, Turkish, Hebrew, Brazilian Portuguese)
  - Distributional data (PALPosition, PALExample, stress pattern)

## [0.75.0] - 2025-02-05

### Changed
- **RSA/Implementations/EgreEtAl2023.lean**: Close all 5 Appendix A sorrys
  - `no_quality_implies_S1_zero` (A-2a): proved by induction on foldl (ℚ)
  - `softmax_translation_invariant` (A-5): removed; use `Softmax.softmax_add_const` from Core
  - `core_lemma_A6` (A-6): proved over ℝ via `weighted_sum_shift` lemma
  - `same_support_implies_equal_S1` (A-7): proved over ℝ via A-6 + `Softmax.softmax_add_const`
  - `lu_limitation` (A-8): proved as corollary of A-7
  - Added import of `Linglib.Theories.RSA.Core.Softmax.Basic`

## [0.74.0] - 2025-02-05

### Fixed
- **RSA/Implementations/EgreEtAl2023.lean**: Corrected BIR tolerance range
  - `birWeight`: y ∈ {0,...,n} per Section 3.2.2, was incorrectly {0,...,6}
  - `birJoint`, `wirPosterior`: restricted to valid tolerances y ≤ n
  - L0 now produces [1/16, 1/8, 3/16, 1/4, ...] matching paper's closed-form prediction

### Added
- **RSA/Implementations/EgreEtAl2023.lean**: Bridge theorems and strengthened appendices
  - Bridge: `bir_matches_closed_form`, `closed_form_matches_phenomena_center/offset5`
  - Appendix A: proper `U1`, `S1_score`, `softmaxLocal` defs; `no_quality_implies_S1_zero` (A-2a), `core_lemma_A6` (A-6), `same_support_implies_equal_S1` (A-7), `lu_limitation` (A-8) with full type signatures (sorry'd)
  - Appendix C: concrete same-support test with `obs_peaked`/`obs_flat`; `peaked_gets_higher_utility_from_around`, `same_utility_under_uniform_l0` (native_decide)

## [0.73.0] - 2025-02-05

### Added
- **RSA/Implementations/EgreEtAl2023.lean**: Égré, Spector, Mortier & Verheyen (2023) "On the optimality of vagueness"
  - BIR model with tolerance marginalization (parallels LassiterGoodman2017 threshold inference)
  - Triangular posterior, ratio inequality, around-beats-between theorems
  - Appendix A: LU limitation (SameSupport, Quality/Weak Quality, SoftMax TI, A-1 through A-8)
  - Appendix B: WIR alternative model
  - Appendix C: standard utility and Bergen utility variants
  - Grounding: BIR from compositional aroundMeaning
- **Fragments/English/NumeralModifiers.lean**: "around", "approximately", "between", "exactly", "precisely", "roughly"
  - ModifierType (tolerance/interval/exactifier), PragmaticFunction, ModifierScale
- **Phenomena/Imprecision/Studies/EgreEtAl2023.lean**: Empirical data from the paper
  - Shape inference, speaker preference, sorites, LU limitation, closed-form data

## [0.72.0] - 2025-02-05

### Changed
- **Eliminated `Theories/Core/`** — moved all 10 files to `Core/` and `Core/Interfaces/`
  - `CommonGround`, `Presupposition`, `ProductOfExperts`, `QUD`, `Parse` → `Core/`
  - `BindingSemantics`, `CoreferenceTheory`, `ImplicatureTheory`, `ScopeTheory`, `SemanticStructure` → `Core/Interfaces/`
  - Fixes: 6 Phenomena files + 1 Fragments file no longer import from `Theories/`
  - 47 import sites updated mechanically
- **Cleaned up theory leakage from Core/**
  - `SemanticStructure`: parameterized `HasSemanticType S T` over type system (was hardcoded to `Ty`)
  - `CoreferenceTheory`: removed dead `Phenomena.Anaphora.Coreference` import
  - `Parse`: moved `ExhPosition`/`exhParses`/`parseHasExhAt` to `NeoGricean/Exhaustivity/Interface`

## [0.71.0] - 2025-02-05

### Added
- **Core/Conjectures.lean**: Open conjectures as `def : Prop` (no axioms, no unsoundness)
  - BToM ↔ Intensional Logic correspondence (accessibility = positive credence)
  - RSA ≅ EXH characterization conjecture
  - RSA fixed point uniqueness, lexicon refinement monotonicity, tropical limit
  - RSA from coarsened language models
- **README.md**: Documentation of organizing principle (Phenomena vs Theories)
  - Directory overview, conventions, intended audience for collaborators
- **docs/ROADMAP.md**: Speculative formal statements moved to `Core/Conjectures.lean`

## [0.70.0] - 2025-02-05

### Added
- **Core/Intension.lean**: Framework-agnostic intensional logic primitives
  - `Intension W τ`, `rigid`, `evalAt`, `IsRigid`
  - `rigid_isRigid`, `evalAt_rigid`, `rigid_injective`, `proposition_eq_bprop` theorems
- **Core/ModalLogic.lean**: `AgentAccessRel W E` — agent-indexed accessibility relations
- **Bridge theorems** connecting IntensionalSemantics types to Core types:
  - `IntensionalSemantics.proposition_eq_bprop`, `intension_t_eq_core`
  - `Modal.proposition_eq_bprop`
  - `Attitude.Intensional.up_eq_rigid`, `down_eq_evalAt`

### Changed
- **Consolidated 7 local Prop'/Proposition definitions** to alias `Core.Proposition.BProp`:
  - `IntensionalSemantics/Attitude/CDistributivity.lean`
  - `IntensionalSemantics/Attitude/Preferential.lean`
  - `IntensionalSemantics/Modal/Kratzer.lean`
  - `IntensionalSemantics/Modal/Basic.lean`
  - `TruthConditional/Basic.lean`
  - `TruthConditional/Sentence/Focus/Particles.lean`
  - `DynamicSemantics/Probabilistic.lean`
- **Unified `Doxastic.AccessRel`** with `Core.ModalLogic.AgentAccessRel`
- **CLAUDE.md**: Updated Core/ directory listing with Intension.lean, ModalLogic.lean

## [0.69.0] - 2025-02-05

### Changed
- **Major reorganization: Montague/ → TruthConditional/ + IntensionalSemantics/ + QuestionSemantics/**
  - `Theories/Montague/` split into three modules reflecting standard subfield boundaries
  - **TruthConditional/**: Extensional semantics (entities, truth values, sets)
    - Quantifiers, entailment, focus, presupposition, composition, adjectives, nouns, tense, aspect
  - **IntensionalSemantics/**: Possible-worlds semantics (29 files)
    - `Modal/`: Kratzer conversational backgrounds, Simple modal semantics, comparisons (7 files)
    - `Attitude/`: Doxastic, preferential, parasitic attitude verbs (7 files)
    - `Conditional/`: Material, strict, variably strict, causal model conditionals (7 files)
    - `Causative/`: Causative verb semantics (6 files)
    - `Mood/`: Sentence mood (1 file)
    - `Basic.lean`: Core intensional types
  - **QuestionSemantics/**: Hamblin, partition, inquisitive semantics (18 files)
- **Core/Duality.lean, Core/Scales.lean**: Moved from Montague/ to Core/ (framework-agnostic)
- **CLAUDE.md**: Updated architecture documentation for new module structure
- All import paths and namespaces updated across 181 files

## [0.68.0] - 2025-02-05

### Added
- **Theories/Montague/Verb/Attitude/Doxastic.lean**: Roberts & Özyıldız (2025) causal model framework
  - `CausalModel`, `CausalVar`, `CausalEdge` types for Pearl-style causal graphs
  - `hasCausalChain`: BFS reachability for causal paths
  - `beliefFormationModel`: Standard causal model for knowledge/belief formation
  - `satisfiesPLC`: Predicate Lexicalization Constraint check
  - `deriveCGRequirement`: Derive CG requirements from veridicality
  - `contrafactive_gap` theorem: Factives satisfy PLC, strong contrafactives violate it
  - `contrafactive_gap_is_structural` theorem: The gap emerges from belief formation structure
- **Theories/Montague/Verb/Attitude/ContrafactiveGap.lean**: Bridge infrastructure
  - `deriveCGReqFromVerb`: Derive CG requirement from VerbEntry's attitudeBuilder
  - `effectiveCGReq`: Handle exceptions (yǐwéi) while defaulting to derivation
  - Per-verb verification theorems for English attitude verbs
  - `yiwei_exception_justified` theorem: Verifies yǐwéi's exception is necessary
- **Fragments/Mandarin/Predicates.lean**: Add yǐwéi with postsupposition flag
  - `yiwei` VerbEntry with `.doxastic .nonVeridical`
  - `hasExceptionalPostsupposition` function: Theory-neutral flag for exceptional CG behavior

### Changed
- **Fragments/English/Predicates/Verbal.lean**: Remove `cgRequirement` field
  - CG requirements now DERIVED in Theory layer, not stipulated in Fragments
  - Fragments remain theory-neutral (no CGRequirement types)
- **Architecture**: Clean separation of concerns
  - Fragments: Theory-neutral lexical data (`attitudeBuilder`)
  - Theory: Derivation functions (`deriveCGRequirement`)
  - Bridge: Per-verb verification + exception handling

### Design
- **Derive, don't stipulate**: CG requirements follow from veridicality
- **Exceptions in Bridge layer**: yǐwéi's postsupposition handled in ContrafactiveGap.lean
- **Enforcement theorems**: `yiwei_exception_justified` fails if exception becomes derivable

## [0.67.0] - 2025-02-05

### Added
- **Core/UPOS.lean**: Universal POS tags from UD v2
  - 17 UPOS tags: `NOUN`, `VERB`, `ADJ`, `ADV`, `PRON`, `DET`, `ADP`, `AUX`, `CCONJ`, `SCONJ`, `NUM`, `PART`, `INTJ`, `SYM`, `PUNCT`, `X`, `PROPN`
  - Helper predicates: `isOpenClass`, `isClosedClass`, `isNominal`, `isPredicate`, `isModifier`
- **Core/UDFeatures.lean**: UD morphological features
  - `Number`, `Gender`, `Case`, `Definite`, `Degree`, `PronType`, `Person`, `VerbForm`, `Tense`, `Aspect`, `Mood`, `Voice`, `Polarity`
  - `MorphFeatures` structure with `compatible` and `unify` operations
- **Core/DepRel.lean**: Universal dependency relations
  - 37+ relations including core arguments (`nsubj`, `obj`, `iobj`), modifiers (`amod`, `advmod`, `nmod`), function words (`aux`, `det`, `case_`)
  - Helper predicates: `isCoreArg`, `isSubject`, `isObject`, `isModifier`, `isFunctionWord`
  - `DepArc` and `DepTree` types for dependency structures

### Changed
- **Core/Basic.lean**: Alias core types to UD for cross-linguistic compatibility
  - `Number` = `UD.Number` (with `Number.sg`, `Number.pl` compatibility aliases)
  - `Person` = `UD.Person` (uses `.first`, `.second`, `.third` directly)
  - `Case` = `UD.Case` (with `Case.nom`, `Case.acc`, `Case.gen` compatibility aliases)
  - `Voice` = `UD.Voice` (with `Voice.active`, `Voice.passive` compatibility aliases)
  - `VForm` = `UD.VerbForm` (with compatibility aliases)
- **Minimalism reorganization**: Move disconnected formal analyses to Phenomena/ with grounding
  - `Formal/Derivations.lean` → `Phenomena/Derivations.lean` (grounded to WordOrder, Subcategorization)
  - `Formal/HeadMovement/BulgarianLHM.lean` → `Phenomena/HeadMovement/BulgarianLHM.lean` (grounded to VerbPosition)
  - `Formal/HeadMovement/GermanicV2.lean` → `Phenomena/HeadMovement/GermanicV2.lean` (grounded to VerbPosition)

### Removed
- **Core/UDMapping.lean**: Obsolete after aliasing (types are identical, no mapping needed)

## [0.66.0] - 2025-02-05

### Added
- **Core/ModalLogic.lean**: Theory-neutral modal logic infrastructure
  - `ModalForce`, `AccessRel`, `kripkeEval` (Kripke semantics)
  - Frame conditions: `Refl`, `Serial`, `Trans`, `Symm`, `Eucl`
  - Correspondence theorems: `T_of_refl`, `D_of_serial`, `K_axiom`, `four_of_trans`, `B_of_symm`, `five_of_eucl`
  - Lattice of normal modal logics: `Axiom`, `Logic`, named logics (K, T, S4, S5, KD45, etc.)
  - Mathlib integration: `Lattice`, `BoundedOrder` instances for `Logic` (K = ⊥, all axioms = ⊤)
  - `S5_collapse`: M+5 implies all frame conditions
  - Standard frames: `universalR`, `emptyR`, `identityR`
- **Core/OrderTheory.lean**: Generic satisfaction-based orderings
  - `SatisfactionOrdering α Criterion`: preorder by subset inclusion of satisfied criteria
  - `satisfiedBy`, `atLeastAsGood`, `best`, `toPreorder`

### Changed
- **Refactor Montague/Modal/ to use Core**: `SatisfactionOrdering.lean`, `Kratzer.lean`, `PhillipsBrown.lean` now import from `Core/OrderTheory.lean`
- **Refactor Simple.lean to use Core/ModalLogic**: `isReflexive`, `isSerial` are now aliases for `Refl`, `Serial`; standard relations use Core's implementations
- **Refactor Modal/Basic.lean**: `ModalForce` is now an alias for `Core.ModalLogic.ModalForce`
- **Unify World with Core.Proposition.World4**: `Montague.Verb.Attitude.Intensional.World` is now an alias for `Core.Proposition.World4`
- **Rename Examples.lean → Intensional.lean**: `Verb/Attitude/Examples.lean` renamed to `Intensional.lean` (contains infrastructure only)
- **Move toy examples to Phenomena**: `ToyIEntity`, `sleeps`, `morningStar`, etc. moved to `Phenomena/Attitudes/IntensionalExamples.lean`
- **Rename `Ideal` → `Criterion`**: More neutral terminology (field `.ideals` → `.criteria`)
- **CLAUDE.md**: Add "Prefer Unicode `λ` over `fun` in code"

## [0.65.0] - 2025-02-04

### Added
- **Fragments/English/Nouns.lean**: `NounEntry.toWordSg`, `NounEntry.toWordPl` projections
- **Fragments/English/Predicates/Verbal.lean**: `VerbEntry.toWordPl` (base/plural form), `devour` and `read` verb entries
- **Fragments/English/Predicates/Verbal.lean**: `complementToValence` helper mapping `.np_np` → `.ditransitive` (was `.transitive`)

### Changed
- **Move Comparisons/ to top level**: `Theories/Comparisons/` → `Comparisons/` (sibling of Core, Fragments, Phenomena, Theories)
- **Upgrade Theory files to Fragment projections**: Replace `private def` Word literals with `private abbrev` projections from Fragment entries across 11 files (DependencyGrammar/{Coreference,Inversion,Coordination,LongDistance,CRDC,LexicalRules}, HPSG/{Coreference,Inversion}, Minimalism/{Coreference,Inversion}, Comparisons/CommandRelations)
- **Fix dot notation**: Rename `toWord` → `VerbEntry.toWord3sg`/`VerbEntry.toWordBase`, `PronounEntry.toWord`, `AdjModifierEntry.toWord` for proper dot-notation support

## [0.64.0] - 2025-02-04

### Added
- **Core/Empirical.lean**: `ScaleType`, `TaskType`, `MeasureSpec` (moved from Phenomena/Core/EmpiricalData.lean, trimmed)
- **Core/Basic.lean**: `MinimalPair`, `PhenomenonData`, `Grammar.capturesPair`, `Grammar.capturesPhenomenon`, `grammars_agree_on_phenomenon` (moved from Phenomena/Core/Basic.lean)

### Changed
- **Dissolve Phenomena/Core/**: Delete `Basic.lean`, `EmpiricalData.lean`, `Lexicon.lean`; move reusable types to `Core/`
- **Inline lexical entries**: Replace `open Lexicon` with file-local `private def` declarations across 30+ Phenomena and Theory files (Agreement, Case, DetNoun, Anaphora, ArgumentStructure, Coordination, FillerGap, Islands, WordOrder, DependencyGrammar, HPSG, Minimalism, Comparisons)
- Update all Phenomena imports from `Linglib.Phenomena.Core.*` to `Linglib.Core.*`

## [0.63.0] - 2025-02-04

### Added
- **Theories/Montague/Modal/Disjunction.lean**: Geurts (2005) disjunctions as modals
  - `Disjunct`: modal disjunct (domain × force × content), `MDisjunction` as conjunction of modal propositions
  - Three constraints: `exhaustivity`, `disjointness₂`, `nonTriviality`
  - `free_choice`: free choice follows structurally (disjunction IS conjunction of ◇ claims)
  - `disjointness_gives_exclusivity`: exclusive 'or' from Disjointness, not scalar implicature
  - `defaultBinding`: default domain = background C (Geurts p. 394)
  - Bridge to `PrProp.orFlex`: `fromPrProp_presup_eq_orFlex`, `fromPrProp_cell_eq_orFlex`, `conflicting_presups_disjoint`
  - Worked examples: "must here or must there" (□ with partition), "may here or may there" (◇ with free choice)
- **Core/Kleene.lean**: Weak Kleene operators and meta-assertion (Beaver & Krahmer 2001)
  - `TVal.orWeak`, `TVal.andWeak`: weak Kleene (⊥ absorbing)
  - `TVal.metaAssert`: maps ⊥ to 0 (bivalentizes trivalent values)
  - `Prop3.orWeak`, `Prop3.andWeak`, `Prop3.metaAssert`: pointwise lifts
- **Theories/Core/Presupposition.lean**: Flexible accommodation disjunction
  - `PrProp.orFlex`: presup = p ∨ q, assertion = (p.presup ∧ p.assertion) ∨ (q.presup ∧ q.assertion)
  - `orFlex_eq_or_when_both_defined`, `orFlex_presup_weaker`: relationship to classical `PrProp.or`
- **Phenomena/Presupposition/Studies/Yagi2025.lean**: Yagi (2025) conflicting presuppositions in disjunction
  - Buganda scenario (4 worlds: kingOpens, kingDoesnt, presidentConducts, presidentDoesnt)
  - Failure theorems: Strong Kleene never false, classical never defined, filtering wrong presupposition
  - Success: `PrProp.orFlex` gives correct presupposition p ∨ q and allows falsity
  - Meta-assertion analysis: allows falsity but loses presupposition

### Changed
- **Theories/Montague/Expressives/Basic.lean**: Moved from Lexicon/Expressives/ (Lexicon/ was otherwise empty)

## [0.62.0] - 2025-02-04

### Added
- **Phenomena/Complementation/Typology.lean**: Noonan (2007) complementation typology
  - `NoonanCompType`: 6 cross-linguistic complement types (indicative, subjunctive, paratactic, infinitive, nominalized, participle)
  - `CTPClass`: 12 complement-taking predicate classes
  - `RealityStatus`: realis/irrealis split predicting complement selection
  - 36 `CTPDatum` entries across 7 languages (English, Latin, Turkish, Irish, Persian, Hindi-Urdu, Japanese)
  - Verified generalizations: realis/irrealis consistency, equi-deletion restriction, negative raising class restriction, implicational hierarchy
  - First negative raising data in linglib
- **Phenomena/Complementation/Bridge.lean**: Interconnection theorems
  - `deriveCTPClass`: Derives CTP class from VerbEntry fields (40+ per-verb theorems)
  - `ctpToDefaultSelectionClass`: Maps CTP → SelectionClass with consistency checks against `deriveSelectionClass`
  - `ctpToMoodSelector`: Maps CTP → MoodSelector with realis/irrealis alignment theorems
  - `englishToNoonan`: Maps English ComplementType → NoonanCompType
  - `deriveMoodSelector`: Derives MoodSelector from VerbEntry fields (fills gap)
  - Three-way agreement theorems (CTP × SelectionClass × MoodSelector) for key verbs

## [0.61.0] - 2025-02-04

### Added
- **Theories/Montague/Sentence/Focus/DomainWidening.lean**: Deo & Thomas (2025) *just* as domain widening
  - `AlternativeSource` enum: roothian, granularity, causal, elaboration, normative
  - `DiscourseContext`: construals + Quality/Relevance filters
  - `JustSemantics`/`OnlySemantics`: unified vs Roothian lexical entries
  - 4 proven theorems linking theory to empirical data from Phenomena/Focus/Exclusives
- **Fragments/English/FunctionWords.lean**: `ParticleEntry` structure with `just_` and `only_`

### Changed
- **Sentence/ reorganization**: Move loose focus/IS files into new `Sentence/Focus/` subdirectory
  - `Focus.lean` → `Focus/Particles.lean`
  - `FocusInterpretation.lean` → `Focus/Interpretation.lean`
  - `InformationStructure.lean` → `Focus/InformationStructure.lean`
  - Zero loose files remain at `Sentence/` top level

## [0.60.0] - 2025-02-04

### Changed
- Move theory-specific files from Core/ to appropriate Theories/ locations (Analyticity→NeoGricean, TeamSemantics/DiscourseState/Probabilistic→DynamicSemantics, CausalModel/BayesNet→Montague/Conditional, BilateralUpdateSemantics→DynamicSemantics/BilateralUpdate, NadathurLauer2020→Montague/Verb/Causative)

## [0.59.0] - 2025-02-03

### Changed
- **Phenomena/ directory reorganization**: Theory-neutral naming and cleaner structure
  - Renamed `Dependencies/` → `FillerGap/` (theory-neutral: no movement implication)
  - Renamed `Additives/` → `AdditiveParticles/` (more informative)
  - Dissolved `RSAStudies/` - files moved to phenomenon-specific `Studies/` subdirectories
  - Dissolved `Semantics/` - files were duplicates of content in specific phenomena
  - Deleted backwards-compatibility re-export files (`Basic.lean`, `EmpiricalData.lean`, `Lexicon.lean`, `Core.lean`, `Degrees.lean`)
  - Merged `WordOrderAlternations/` into `WordOrder/`
  - Added `Studies/` subdirectories to `Reference/`, `Metaphor/`, `Imperatives/`, `Questions/`, `Quantification/`, `Conditionals/`, `Humor/`

### Removed
- `Phenomena/BasicPhenomena/Proofs.lean` (unit tests, not linguistic content)
- ~1400 lines of duplicate code in `Phenomena/Semantics/`

## [0.58.0] - 2025-02-03

### Added
- **Core/Ordering.lean**: Generic SatisfactionOrdering framework with mathlib Preorder integration
- **Theories/Montague/Modal/Kratzer.lean**: Refactored from Kratzer1981.lean, uses Core.Ordering
- **Theories/Montague/Modal/PhillipsBrown.lean**: Question-based desire semantics (Phillips-Brown 2025), extends BouleticFlavor

### Changed
- Modal semantics now derive preorder properties from generic Core.Ordering framework
- Removed Kratzer1981.lean (split into Kratzer.lean + PhillipsBrown.lean)

## [0.57.0] - 2025-02-02

### Added
- **Theories/Montague/Lexicon/Expressives/Basic.lean**: Potts (2005) two-dimensional semantics
  - `TwoDimProp W`: At-issue + CI content structure
  - CI projection theorems: `ci_projects_through_neg`, `ci_projects_from_antecedent`
  - `CIExprType`: Taxonomy (epithet, honorific, appositive, etc.)
  - `comma`: Type-shift for appositives, `supplementaryAdverb`: Adverb application
  - `ciStrongerThan`: CI informativeness ordering for MCIs!

- **Theories/NeoGricean/ConventionalImplicatures.lean**: Lo Guercio (2025) ACIs
  - `CIAlternativePair`, `MCIsResult`: Alternative pair and MCIs! result types
  - `applyMCIs`: Derive ACIs from CI alternative pairs
  - Key examples: `example_outOfBlue_noACI`, `example_priorMention_ACI`
  - Property theorems: `aci_independent_of_assertion`, `aci_polarity_insensitive`
  - `ScalarInferenceComparison`: Compare SI/antipresup/ACI properties

- **Phenomena/LoGuercio2025/Data.lean**: Empirical ACI judgments
  - Epithet data (ex18-21), honorific data (ex22-23), appositive data (ex31-32)
  - Property tests: ex50 (assertion independence), ex52 (cancellable), ex61 (DE-insensitive), ex63 (reinforceable)
  - `InferenceTypeComparison`: SI vs antipresupposition vs ACI table

## [0.56.0] - 2025-02-02

### Added
- **Theories/DynamicSemantics/**: New unified dynamic semantics infrastructure
  - **Core/**: Shared types (`Possibility`, `InfoState`, `Context`), CCP, bilateral updates, discourse refs
  - **BUS/**: Bilateral Update Semantics (Elliott & Sudo 2025) - reorganized from BilateralUpdateSemantics/
  - **CDRT/**: Compositional DRT with DynamicTy2 integration
  - **DPL/**: Dynamic Predicate Logic (Groenendijk & Stokhof 1991)
  - **DRT/**: Discourse Representation Theory (Kamp 1981)
  - **PLA/**: Probabilistic Language of Attitudes with belief/epistemic operators
  - **IntensionalCDRT/**: Intensional CDRT (Hofmann 2025)
  - **FileChangeSemantics/**: Heim's file change semantics
  - **Comparisons/PLA_BUS.lean**: PLA vs BUS comparison

- **Phenomena/DynamicSemantics/**: Dynamic semantics test cases
  - CrossSententialAnaphora, BathroomSentences, DoubleNegation, ModalSubordination

### Changed
- **Theories/BilateralUpdateSemantics/Basic.lean**: Deprecated, redirects to DynamicSemantics/BUS/

## [0.55.0] - 2025-02-02

### Added
- **Theories/NeoGricean/Exhaustivity/EFCI.lean**: Existential Free Choice Items (Alonso-Ovalle & Moghiseh 2025)
  - Pre-exhaustified domain alternatives: `preExhaustify D d P = P(d) ∧ ∀y≠d. ¬P(y)`
  - EFCI rescue typology: `EFCIRescue` (none/modalInsertion/partialExh/both)
  - Context-dependent readings: `efciReading` maps context → reading
  - Key theorems: `yeki_root_uniqueness`, `deontic_freeChoice`, `epistemic_modalVariation`

- **Theories/NeoGricean/Exhaustivity/EFCIClosure.lean**: Root explanation for EFCI
  - `preExh_pairwise_inconsistent`: Pre-exhaustified alternatives are mutually exclusive
  - `efci_not_closed_witness`: EFCI alternatives fail closure under conjunction
  - `unique_witness_falsifies_allNotPreExh`: Why IE can't negate all domain alts
  - Connection to Spector's Theorem 9 (non-closure explains exh_mw ≠ exh_ie)

- **Phenomena/FreeChoice/FarsiYekI/Data.lean**: Empirical data for Farsi *yek-i*
  - `YekIDatum`: Context-reading pairs (root→uniqueness, deontic→FC, etc.)
  - `EFCITypologyDatum`: Cross-linguistic EFCI comparison (yek-i, irgendein, vreun)

- **Fragments/Farsi/Determiners.lean**: Farsi indefinite lexicon
  - `yeki`: *yek-i* lexical entry with EFCI properties
  - `getReading`: Compute reading from entry and context
  - Cross-linguistic entries: `irgendein_de`, `vreun_ro`

## [0.54.0] - 2025-02-02

### Changed
- **Theories/RSA/Core/Basic.lean**: Make RSAScenario parametric on U (Utterance) and W (World)
  - `RSAScenario U W` instead of opaque `Utterance : Type` / `World : Type` fields
  - Enables clean API: `scenario.evalL1 u` instead of `RSA.evalL1 (U := ...) (W := ...) scenario rfl rfl rfl rfl u`
  - Updated all smart constructors, eval methods, and ~10 implementation files

## [0.53.0] - 2025-02-02

### Added
- **Theories/NadathurLauer2020/**: Causative verb semantics from Nadathur & Lauer (2020)
  - **Basic.lean**: Re-exports, summary theorem `make_cause_truth_conditionally_distinct`
  - **Sufficiency.lean**: Causal sufficiency (Definition 23), `makeSem` for "make"
  - **Necessity.lean**: Causal necessity (Definition 24), `causeSem` for "cause"
  - **Examples.lean**: Fire overdetermination, circuit, causal chain scenarios
  - **CoerciveImplication.lean**: Volitional actions and coercion inference
  - **Integration.lean**: Bridge to Grusdt et al. (2022) probabilistic model
    - `situationToWorldState`: Converts structural situations to WorldState
    - Grounding theorems for structural → probabilistic causation

- **Core/CausalModel.lean**: Pearl-style structural causal models
  - `Variable`, `Situation`: Partial valuations
  - `CausalLaw`: Precondition → effect structural equations
  - `CausalDynamics`: Collections of causal laws
  - `normalDevelopment`: Forward propagation to fixpoint
  - Helper constructors: `disjunctiveCausation`, `conjunctiveCausation`, `causalChain`

- **Fragments/English/Predicates/Verbal.lean**: Causative verb lexical entries
  - `VerbClass.causative`: New verb class
  - `CausativeType`: `.sufficiency` (make) vs `.necessity` (cause)
  - Entries: `cause`, `make`, `let_`, `have_causative`, `get_causative`, `force`
  - Helper functions: `isCausative`, `assertsSufficiency`, `assertsNecessity`

### Key Results
- Sufficiency ⇏ Necessity (overdetermination: `main_sufficiency_not_necessity`)
- Necessity ⇏ Sufficiency (conjunctive causation: `main_necessity_not_sufficiency_empty`)
- "make" and "cause" are truth-conditionally distinct (`make_cause_distinct`)

## [0.52.0] - 2025-02-02

### Added
- **Core/Proposition.lean**: Galois connection for proposition-world duality
  - `GaloisConnection.extension`: Set-based ext(A) = {w : ∀p ∈ A. p(w)}
  - `GaloisConnection.intension`: Set-based int(W) = {p : ∀w ∈ W. p(w)}
  - `galois_connection`: W ⊆ ext(A) ↔ A ⊆ int(W) (fundamental adjunction)
  - `extension_antitone`, `intension_antitone`: Antitonicity theorems
  - `extensionL`, `intensionL`: List-based versions for computation
  - `closure_expanding`, `closure_expanding'`: Closure operator properties

### Changed
- **Montague/Modal/Kratzer1981.lean**: Complete rewrite with full derivations from Kratzer (1981)
  - Correct subset-based ordering relation (was counting-based)
  - `ordering_reflexive`, `ordering_transitive`: Preorder properties PROVEN
  - `kratzerPreorder`: **Mathlib Preorder instance** for ≤_A relation
  - `ordering_transitive'`, `orderingEquiv_trans`: Use mathlib's `le_trans`
  - `totally_realistic_gives_T`: T axiom derived from realistic modal base
  - `D_axiom`: Seriality axiom □p → ◇p (non-empty best worlds)
  - `D_axiom_realistic`: D axiom for realistic bases
  - `K_axiom`: Distribution axiom □(p → q) → (□p → □q)
  - `duality`: Modal duality □p ↔ ¬◇¬p
  - Frame correspondence theorems:
    - `four_axiom`: □p → □□p (transitivity)
    - `B_axiom`: p → □◇p (symmetry)
    - `five_axiom`: ◇p → □◇p (Euclidean)
    - `euclidean_reflexive_implies_symmetric`: T + 5 → B
    - `euclidean_reflexive_implies_transitive`: T + 5 → 4
    - `S5_satisfies_all`: S5 bases satisfy T, D, 4, B, 5
  - Galois connection now uses `Core.Proposition.GaloisConnection`
    - `extension_eq_core`: Kratzer extension = Core extensionL
    - `accessible_is_extension`: Accessibility as Galois extension
  - `comparative_poss_reflexive`: Comparative possibility reflexivity
  - Modal flavors as structures: `EpistemicFlavor`, `DeonticFlavor`, `BouleticFlavor`, `TeleologicalFlavor`
  - Conditionals as modal base restrictors (Kratzer p. 64-66)

- **Montague/Sentence/Conditional/Basic.lean**: Unified with Kratzer1981
  - Updated `kratzerBetter` docstring to reference Kratzer1981's `atLeastAsGoodAs`
  - Both use correct subset-based ordering (Sets vs Lists for different use cases)

### Removed
- **Montague/Modal/Kratzer.lean**: Replaced by Kratzer1981.lean (had flawed cardinality-based ordering)
- **Montague/Modal/ConversationalBackground.lean**: Fully superseded by Kratzer1981.lean
  - `accessibleFrom` predicate moved to Kratzer1981.lean
  - All other content was redundant or used flawed `idealScore` counting

## [0.51.0] - 2025-02-02

### Added
- **Core/HeimState.lean**: Heimian information states for dynamic semantics
  - `Possibility W E`: (world, assignment) pairs
  - `HeimState W E`: Sets of possibilities (Heim's "file cards")
  - Operations: `update`, `randomAssign`, `randomAssignFull`
  - `subsistsIn`: State subsistence relation (s ⪯ s')
  - `definedAt`, `novelAt`: Variable familiarity tracking
  - `supports`, `dynamicEntails`: Dynamic truth and entailment

- **Theories/BilateralUpdateSemantics/Basic.lean**: Elliott & Sudo (2025) BUS framework
  - `BilateralDen W E`: Bilateral denotations with positive/negative updates
  - Logical operations: `neg` (~), `conj` (⊙), `disj` (⊕), `exists_`, `forall_`
  - `neg_neg`: Double Negation Elimination (¬¬φ = φ)
  - `egli`: Egli's theorem (∃xφ ∧ ψ ⊨ ∃x[φ ∧ ψ])
  - Predicate constructors: `atom`, `pred1`, `pred2`

- **Theories/BilateralUpdateSemantics/FreeChoice.lean**: Free Choice derivations
  - Modal operators: `possible`, `necessary`, `impossible`
  - `disjFC` (∨ᶠᶜ): Free Choice disjunction
  - `BathroomConfig`: Cross-disjunct anaphora configuration
  - `fc_basic`: ◇(φ ∨ ψ) → ◇φ ∧ ◇ψ
  - `modified_fc`: ◇(φ ∨ ψ) → ◇φ ∧ ◇(¬φ ∧ ψ)
  - `fc_with_anaphora`: Bathroom disjunction pattern
  - `dual_prohibition`: ¬◇φ ∧ ¬◇ψ → ¬◇(φ ∨ ψ)

## [0.50.0] - 2025-02-01

### Added
- **Core/CausalBayesNet.lean**: Causal Bayes net infrastructure
  - `CausalRelation`: ACausesC, CCausesA, Independent
  - `NoisyOR`: Background rate and causal power parameterization
  - `WorldState`: Probability distributions over atomic propositions A and C

- **Montague/Sentence/Conditional/Basic.lean**: Compositional conditional semantics
  - Material, strict, and variably strict conditionals
  - Kratzer-style conditionals with modal base and ordering source

- **Montague/Sentence/Conditional/Assertability.lean**: Probabilistic assertability
  - `conditionalProbability`: P(C|A) computation
  - `assertable`: Threshold-based assertability (default θ = 0.9)
  - Missing-link detection and causal inference

- **RSA/Implementations/GrusdtLassiterFranke2022.lean**: Conditional RSA model
  - Utterances: literals, conjunction, conditional, likely-literals
  - L0: Samples worlds where conditional is assertable
  - L1: Infers both WorldState AND CausalRelation from utterances
  - Grounding theorem: RSA derives meaning from Montague assertability

- **Phenomena/Conditionals/Data.lean**: Theory-neutral conditional phenomena
  - Conditional perfection (Geis & Zwicky 1971)
  - Missing-link infelicity
  - Douven's puzzle data
  - Indicative/subjunctive split, biscuit conditionals

- **Phenomena/GrusdtLassiterFranke2022/Data.lean**: Paper experimental data
  - Experiment 1: Causal structure inference from conditionals
  - Experiment 2: Conditional perfection rates
  - Experiment 3: Assertability threshold (θ ≈ 0.9)
  - Model fit statistics (r = 0.89-0.94)

## [0.49.0] - 2025-02-01

### Changed
- **Fragments reorganization**: Language-specific content only
  - Moved `Fragments/Determiners.lean` → `Fragments/English/Determiners.lean`
  - Moved `Fragments/Scales.lean` → `Fragments/English/Scales.lean`
  - Moved `Fragments/Pronouns.lean` → `Fragments/English/Pronouns.lean`
  - Moved `Fragments/FunctionWords.lean` → `Fragments/English/FunctionWords.lean`
  - Deleted generic `Fragments/Nouns.lean` (each language has its own)

- **RSA Domains**: Moved RSA-specific infrastructure to `Theories/RSA/Domains/`
  - Moved `Fragments/Quantities.lean` → `Theories/RSA/Domains/Quantities.lean`
  - Moved `Fragments/ReferenceGames.lean` → `Theories/RSA/Domains/ReferenceGames.lean`
  - Moved `Fragments/QUD.lean` → `Theories/RSA/Domains/QUD.lean`
  - Moved `Fragments/Scope.lean` → `Theories/RSA/Domains/Scope.lean`
  - Moved `Fragments/Degrees.lean` → `Theories/RSA/Domains/Degrees.lean`
  - Moved `Fragments/LexicalAmbiguity.lean` → `Theories/RSA/Domains/LexicalAmbiguity.lean`

### Added
- **Fragments/English/Nouns.lean**: English-specific NP with blocking configuration
- **Fragments/Mandarin/Nouns.lean**: Mandarin NP with classifiers, no number
- **Fragments/Japanese/Nouns.lean**: Japanese NP with case particles
- **Fragments/French/Nouns.lean**: French NP with gender and partitive determiners

## [0.48.0] - 2025-02-01

### Added
- **Theories/Montague/Lexicon/Kinds.lean**: Chierchia (1998) kind-level semantics
  - Nominal Mapping Parameter: [+arg,±pred] determines bare argument distribution
  - Domain structure: Link's semilattice with atoms and pluralities
  - ∩ (down): Property → Kind nominalization
  - ∪ (up): Kind → Property predicativization
  - DKP (Derived Kind Predication): existential coercion for object-level predicates
  - Blocking Principle: Type shifting as last resort (articles block covert shifts)
  - Mass/count distinction: why bare singulars are out but bare plurals are in
  - Scopelessness: DKP introduces local existentials that cannot scope out
  - Connection to I-level/S-level predicates and generic interpretation

- **Fragments/Nouns.lean**: NP structure with bare plural tracking
  - `NP` structure: noun + number + isBare + optional determiner
  - `NP.isBarePlural`, `NP.isBareMass` predicates
  - Constructors: `barePlural`, `bareMass`, `theNP`, `aNP`, `withDet`
  - Theory-neutral: no grammaticality judgments (those belong in Phenomena/Theories)

## [0.47.0] - 2025-02-01

### Added
- **Theories/Montague/Questions/EntropyNPIs.lean**: Van Rooy (2003) NPI analysis
  - Shannon entropy for questions: E(Q) = Σ P(q) × inf(q)
  - NPI licensing via entropy increase (Krifka's bias reduction formalized)
  - Rhetorical questions via strong NPIs + EVEN presupposition
  - K&L strengthening: Q' strengthens Q iff Q settled but Q' open
  - Unified principle: assertions use informativity, questions use entropy
  - Connection to decision theory (entropy = expected utility for epistemic DPs)

### Changed
- **Fragments/Determiners.lean**: Unified lexical entry for quantifiers/determiners
  - `QuantifierEntry`: Single source of truth with syntactic AND semantic properties
  - `QuantityWord`: 6-word enum (none, few, some, half, most, all) referencing entries
  - GQT semantics: `gqtMeaning`, `gqtMeaningRat`, `gqtThreshold`
  - PT semantics: `ptMeaning`, `ptPrototype`, `ptSpread`
  - Horn scales: `Scale` structure with `someAllScale`, `someMostAllScale`
  - Non-negativity theorems: `gqtMeaningRat_nonneg`, `ptMeaning_nonneg`

- **Fragments/Quantities.lean**: VanTielQuantity uses unified Determiners
  - `Utterance` is now alias for `Fragments.Determiners.QuantityWord`
  - Removed duplicate type definitions and semantics
  - Domain proofs use theorems from Determiners

- **RSA/Implementations/VanTielEtAl2021.lean**: Uses unified infrastructure
  - `threshold`, `prototype`, `spread` now delegate to Determiners
  - Updated proofs to use `native_decide` for computed values
  - Added note about monotonicity classification (3-way vs 2-way)

## [0.46.0] - 2025-02-01

### Added
- **RSA/Core/ChainComparison.lean**: Chain comparison infrastructure
  - `RSA.ChainVariant`: `.L0Based` (standard) vs `.S0Based` (literal speaker base)
  - `RSA.ChainComparison`: Compare distributions from both chains
  - `RSA.totalVariation`: Measure divergence between chains
  - `RSA.analyzeDivergence`: Find max divergent element

- **RSA/Core/Basic.lean**: Unified chain API
  - `RSA.speaker`: Pragmatic speaker with chain selection (default `.L0Based`)
  - `RSA.listener`: Pragmatic listener with chain selection
  - `utterancePrior` field in RSAScenario for S0 salience

- **RSA/Core/Eval.lean**: List-based chain API
  - `RSA.Eval.runS1`: S1 with ChainVariant parameter
  - `RSA.Eval.runL1`: L1 with ChainVariant parameter

- **RSA/Implementations/VanTielEtAl2021.lean**: van Tiel et al. (2021) replication
  - GQT vs PT semantics for quantity words
  - S0-based chain for production modeling
  - Chain comparison theorems (convergence at extremes, PT diverges more)

- **Fragments/Quantities.lean**: VanTielQuantity domain
  - 6-word scale: none, few, some, half, most, all
  - `gqtMeaning`: Binary threshold semantics
  - `ptMeaning`: Gradient Gaussian semantics
  - `Domain.runS1`/`runL1` with ChainVariant
  - `Domain.compareS1`/`compareL1` for chain comparison

## [0.45.0] - 2025-02-01

### Added
- **Comparisons/RSAExhExpressivity.lean**: Formalizes expressivity gap between standard RSA and EXH
  - Standard RSA is scope-blind: treats utterances atomically, gives ONE distribution
  - EXH is scope-sensitive: different scope positions yield different meanings
  - `expressivity_gap`: Standard RSA cannot express local EXH (embedded implicatures)
  - `ibr_is_global_not_local`: IBR (α→∞ limit) implements GLOBAL EXH only
  - `hierarchy_is_strict`: Compositional RSA (scope as latent variable) is strictly more expressive
  - Classic example: "Every student read some book" - global vs local SI
  - Motivates compositional/lexical RSA approaches (ScontrasPearl2021, LexicalUncertainty)

- **RSA/Implementations/Franke2011.lean**: Expected gain framework (Franke Appendix B.4)
  - `expectedGain`: EG(S, H) = Σ_t prior(t) × Σ_m S(t,m) × H(m,t)
  - `eg_speaker_improvement`, `eg_hearer_improvement`: Monotonicity lemmas (stubs)
  - `eg_bounded`: EG ≤ 1 (stub)
  - `ibr_reaches_fixed_point`: Theorem 3 - IBR converges (stub)
  - `speakerOptionCount`: |S(t)| = number of messages speaker uses at state t
  - `fp_prefers_fewer_options`: Key lemma connecting IBR to alternative minimization (eq. 131)
  - Documentation of proof strategy from Franke's light system (equations 123-131)

- **RSA/Implementations/Franke2011.lean**: Speaker strategy helper lemmas (proved)
  - `bestResponse_nonneg`: Best response gives non-negative probabilities
  - `bestResponse_false_zero`: Best response gives 0 to false messages
  - `bestResponse_sum_le_one`: Best response sums to ≤ 1 (stub)
  - `speaker_options_le_true_messages`: Speaker options bounded by true messages

- **RSA/Implementations/Franke2011.lean**: Fixed point lemmas (partial)
  - `fp_respond_nonneg`: Fixed point listener responses are non-negative (proved)
  - `ibr_equals_exhMW`: Main theorem structure with prejacent direction proved
  - Forward direction (prejacent): If H.respond m s > 0 then m is true at s (proved)
  - Minimality and backward directions remain as stubs

- **RSA/Implementations/Franke2011.lean**: Franke Fact 1 formalization (R₁ ⊆ ExhMW)
  - `r1_subset_exhMW`: States with minimum alternative count are in ExhMW (proved)
  - `altOrderingTotalOnMessage`: Condition for when <_ALT is total on m-worlds
  - `exhMW_subset_r1_under_totality`: Converse direction under totality (proved)
  - `r1_eq_exhMW_under_totality`: Full equivalence R₁ = ExhMW under totality (proved)
  - Helper lemmas: `ltALT_implies_trueMessages_ssubset`, `trueMessages_ssubset_implies_ltALT`
  - Characterizes exactly when Franke's containment becomes equality

## [0.44.0] - 2025-02-01

### Added
- **Core/Softmax/Basic.lean**: Softmax function with key properties (Franke & Degen tutorial)
  - Definition: softmax(s, α)ᵢ = exp(α·sᵢ) / Σⱼ exp(α·sⱼ)
  - Fact 1: Valid probability distribution (sum to 1, positive)
  - Fact 2: Odds from differences: pᵢ/pⱼ = exp(α(sᵢ - sⱼ)) - THE key property
  - Fact 3: Binary case = logistic function
  - Fact 6: Translation invariance
  - Fact 8: Scale trading
  - Monotonicity properties
- **Core/Softmax/Limits.lean**: Limit behavior as α varies (proofs use Mathlib analysis)
  - `tendsto_softmax_zero`: α → 0 gives uniform distribution
  - `softmax_ratio_tendsto_zero`: ratio → 0 as α → ∞ (via `tendsto_exp_atBot`)
  - `tendsto_softmax_infty_unique_max`: concentration on unique max as α → ∞
  - `tendsto_softmax_neg_infty_unique_min`: concentration on min as α → -∞
  - `softmax_tendsto_hardmax`: softmax → hardmax (RSA → IBR limit)
  - Entropy bounds (placeholder)
- **Core/Softmax/MaxEntropy.lean**: Entropy-regularized optimization
  - Fact 5: Softmax = max entropy distribution subject to expected score
  - Entropy-regularized objective: argmax_p [⟨s, p⟩ + (1/α) H(p)]
  - Free energy / Boltzmann interpretation
  - Exponential family characterization
  - KL divergence connections
- **RSA/Core/Convergence.lean**: Integrated softmax into RSA
  - `speakerSoftmax`: RSA speaker defined as softmax(utility, α)
  - Properties inherited directly: sum to 1, positivity, odds, monotonicity
  - `speakerSoftmax_zero`: α = 0 gives uniform distribution
  - Uses existing `utility` function - no fragmentation

### Changed
- **RSA/Implementations/Franke2011.lean**: Fully proved `rsa_to_ibr_limit` theorem
  - Connects softmax limits to IBR via `tendsto_softmax_infty_at_max`
  - Uses principled floor score `falseMessageScore` based on state space size
  - Complete proof that RSA S1 → IBR S1 as α → ∞

## [0.43.0] - 2025-01-31

### Added
- **RSA/Implementations/Franke2011.lean**: Iterated Best Response (IBR) model (S&P 4(1):1-82)
  - Game-theoretic foundation for quantity implicatures
  - IBR algorithm: L₀ → S₁ → L₂ → ... converging to fixed point
  - **Key theorem**: IBR fixed point = exhMW (exhaustive interpretation)
  - Connection to Spector's Theorem 9: under closure, IBR = exhIE
  - RSA → IBR as α → ∞ (softmax → argmax limit)
  - Working examples: scalar implicature game, free choice game

## [0.42.0] - 2025-01-31

### Added
- **RSA/Implementations/WaldonDegen2021.lean**: Continuous-Incremental RSA (CI-RSA) for cross-linguistic referring expressions (SCiL 2021)
  - Synthesizes incremental RSA (Cohn-Gordon et al. 2018) with continuous semantics (Degen et al. 2020)
  - Predicts color/size asymmetry in redundant modification
  - Models cross-linguistic word order variation (English prenominal vs Spanish postnominal)
  - Grounding theorem connecting to unified noise theory (`lexContinuous_as_noiseChannel`)

## [0.41.0] - 2025-01-31

### Added
- **RSA/Implementations/ChampollionAlsopGrosu2019.lean**: Free choice disjunction as RSA (SALT 29)
- **RSA/Implementations/Alsop2024.lean**: Free choice *any* with Global Intentions model
- **NeoGricean/Implementations/BarLevFox2020.lean**: Innocent Inclusion (II) for free choice (NLS)
- **Comparisons/FreeChoice.lean**: Theory comparison for free choice phenomena
- **Phenomena/FreeChoice/Data.lean**: Free choice *any* (universal FCI) empirical data

## [0.40.1] - 2025-01-31

### Added
- **RSA/Implementations/ScopeFreezing.lean**: Two-quantifier scope freezing RSA model
  - `rsa_can_rescue_frozen`: World priors rescue "frozen" ∀>∃ reading (16% → 96%)
- **RSA/Implementations/ScontrasPearl2021.lean**: `priors_shift_negation_scope` (renamed from rescue proof)

## [0.40.0] - 2025-01-31

### Added
- **Phenomena/ScopeFreezing/Data.lean**: Scope freezing phenomena (15 examples, 6 contexts)
- **Theories/Minimalism/Scope.lean**: QR + Scope Economy + Locality constraints
- **Theories/Comparisons/ScopeFreezing.lean**: Three-way theory comparison (Minimalism vs CCG vs Processing)

### Changed
- **Theories/SDS/**: Moved from Comparisons/SDS/ to top-level theory
  - SDS is now a peer of RSA at Theories/SDS/

## [0.39.0] - 2025-01-31

### Added
- **Theories/Montague/Basic.lean**: Type `s` for possible worlds, intensional Model
- **Theories/Montague/Conjunction.lean**: Partee & Rooth (1983) key theorems
  - `genConj_pointwise`, `genConj_distributes_over_app`, `genConj_lambda_distribution`
- **Theories/Montague/Frames/Basic.lean**: Frame semantics infrastructure
- **Core/ProductOfExperts.lean**: Multiplicative probability combination
- **Theories/RSA/Core/Noise.lean**: Unified noise channel theory
- **Phenomena/Degrees.lean**: Degree phenomena (split from Vagueness)
- **Phenomena/KursatDegen2021/Data.lean**: Perceptual difficulty data
- **Phenomena/Generics/Data.lean**: Generic sentence phenomena
- **Phenomena/Ellipsis/FragmentAnswers.lean**: Fragment answer data
- **Phenomena/Focus/ProsodicExhaustivity.lean**: Prosodic exhaustivity phenomena
- **Theories/Comparisons/SDSandRSA.lean**: SDS ↔ LU-RSA correspondence
- **Theories/Comparisons/ThresholdSemantics.lean**: Threshold semantics comparison
- **Theories/RSA/Implementations/BergenGoodman2015.lean**: Pragmatic reasoning via semantic inference
- **Theories/RSA/Implementations/TesslerGoodman2019.lean**: Flexible negation RSA
- **Fragments/LexicalAmbiguity.lean**: Lexical ambiguity infrastructure
- **Theories/Montague/Lexicon/GradableNouns.lean**: Gradable noun semantics
- **Theories/Montague/Lexicon/SelectionalPreferences.lean**: Selectional restriction semantics
- **Conjectures.lean**: Open conjectures and work-in-progress

### Changed
- **Theories/RSA/DegenEtAl2020.lean**: Product of Experts semantics, noise decomposition theorems
- **Phenomena/Vagueness/Data.lean**: Trimmed to vagueness-only (degrees moved out)
- **Questions/ConjoinableTypes.lean** → **Questions/Hamblin.lean**: Renamed

## [0.38.0] - 2025-01-31

### Added
- **Theories/Montague/Lexicon/Attitudes/Preferential.lean**: Veridical preferential predicates
  - `mkVeridicalPreferential`: Constructor for veridical predicates (be happy, be surprised)
  - `beHappy`, `beSurprised`, `beGlad`, `beSad`: Veridical predicate instances
  - `veridical_breaks_triviality`: Core U&S (2019) theorem - veridicality breaks triviality
  - `veridicalPreferential_isCDistributiveAt`: C-distributivity for world-sensitive semantics

- **Fragments/English/Predicates/Adjectival.lean**: Adjectival predicate entries (Kennedy & McNally 2005)
  - Predicative uses: "John is tall", "John is happy"
  - Scale types, antonym relations (contrary/contradictory)

- **Fragments/English/Modifiers/Adjectives.lean**: Adjective modifier entries
  - Attributive uses: "a tall man", "the taller candidate"
  - Morphology: comparative (taller), superlative (tallest)
  - Antonym forms and relations

### Changed
- **Fragments reorganization**: `Verbs.lean` → `Predicates/Verbal.lean` + `Predicates/Adjectival.lean`
  - Verbal predicates: know, believe, hope, fear, run, kick...
  - Adjectival predicates: tall, happy, full... (predicative 1-place)
  - Adjective modifiers: tall, happy, full... (attributive with morphology)
  - Organizes by grammatical function, not semantic mechanism

### Architecture
- **Veridical breaks triviality**: Non-veridicality is NECESSARY for anti-rogativity
  - C-dist + positive + TSP → trivial ONLY IF non-veridical
  - Veridical predicates (be happy) can take questions despite C-dist + positive
- **Predicates vs Modifiers**: Separate entries for predicative vs attributive adjective uses

## [0.37.0] - 2025-01-31

### Added
- **Theories/Montague/Lexicon/Attitudes/CDistributivity.lean**: C-distributivity as derived property
  - `IsCDistributive`: Definition of C-distributivity for predicates
  - `degreeComparison_isCDistributive`: Proof that degree-comparison semantics yields C-distributivity
  - Instantiations: `hope_isCDistributive`, `fear_isCDistributive`, etc.
  - `exists_nonCDistributive_worry`: Axiom for uncertainty-based non-C-distributivity

- **Theories/Montague/Lexicon/Attitudes/Preferential.lean**: TSP derived from degree semantics
  - `SignificanceContent`: Distinguishes positive (desiredExists = TSP) vs negative (threatIdentified)
  - `significanceFromValence`: Derives significance type from valence
  - `positive_hasTSP`, `negative_lacks_TSP`: TSP distribution as theorems, not stipulation
  - `toHamblin`, `fromHamblin`: Conversions between List and Hamblin question representations
  - `roundtrip_preserves_membership`, `triviality_representation_independent`: Equivalence theorems

- **Fragments/{English,Japanese,Mandarin,Turkish}/Verbs.lean**: PreferentialBuilder architecture
  - `PreferentialBuilder`: Links Fragment entries to Montague predicate constructors
  - `PreferentialBuilder.isCDistributive`: Derived from semantic structure (proved in Montague)
  - `VerbEntry.nvpClass`, `VerbEntry.cDistributive`: Derived properties, not stipulated fields
  - Cross-linguistic coverage: hope/fear/worry (English), qidai/xiwang (Mandarin), tanosimi/kitai (Japanese), kork-/um- (Turkish)

- **Phenomena/QingEtAl2025/Data.lean**: Empirical data from Qing et al. (2025)
  - NVP observations across 4 languages with question-taking judgments
  - Links to Fragment verb entries for verification

### Architecture
- **Grounding principle**: C-distributivity and TSP are DERIVED from semantic structure, not stipulated
- **Derivation chain**: Degree semantics (Villalta) → Significance presup (Kennedy) → TSP (U&S) → Triviality → Anti-rogativity
- **Hamblin connection**: Documents link between List representation and full intensional Hamblin semantics
- **Promissory note**: Full Rooth focus semantics integration planned for future work

### References
- Qing, Özyıldız, Roelofsen, Romero, Uegaki (2025). When can NVPs take questions?
- Uegaki & Sudo (2019). The *hope-wh puzzle. Natural Language Semantics.
- Kennedy (2007). Vagueness and grammar. Linguistics & Philosophy.
- Villalta (2008). Mood and gradability. Linguistics & Philosophy.

## [0.36.0] - 2025-01-31

### Added
- **Theories/Comparisons/SDS/**: Unified SDS (Situation Description Systems) framework
  - `Core.lean`: `SDSConstraintSystem` typeclass for factored constraint combination
    - Product of Experts: `unnormalizedPosterior(θ) = selectionalFactor(θ) × scenarioFactor(θ)`
    - `normalizedPosterior`, `expectation`, `softTruth` via marginalization
    - `hasConflict`, `conflictDegree`: detect when factors disagree (predicts ambiguity)
  - `ThresholdInstances.lean`: Threshold semantics as SDS instances
    - Gradable adjectives, generics, gradable nouns all satisfy SDSConstraintSystem
  - `Marginalization.lean`: Equivalence theorems between threshold semantics and SDS
  - `Examples.lean`: Worked examples (gradable adjectives, concept disambiguation)
  - `MeasureTheory.lean`: Placeholder for continuous SDS with Mathlib measures
  - `Humor.lean`: Connection to Kao, Levy & Goodman (2016) pun humor model
    - SDS conflict ≈ Kao's distinctiveness (different evidence → different interpretations)
    - `posteriorUncertainty`: Gini impurity as log-free entropy proxy
    - TODO for full KL divergence formalization

- **Phenomena/Humor/KaoEtAl2016/Data.lean**: Empirical data from Kao et al. (2016)
  - `PhoneticPun`, `NonPunSentence` structures with funniness/ambiguity/distinctiveness
  - Example puns: "magician hare", "dentist tooth"
  - Regression coefficients and key statistical results

- **Core/ProductOfExperts.lean**: Standalone PoE combinators

### Architecture
- SDS unifies: gradable adjectives (Lassiter & Goodman), generics (Tessler et al.), concept disambiguation (Erk & Herbelot), LU-RSA (Bergen et al.)
- Key insight: **Boolean semantics + parameter uncertainty = soft/graded meanings**

### References
- Erk & Herbelot (2024). How to Marry a Star. Journal of Semantics.
- Kao, Levy & Goodman (2016). A Computational Model of Linguistic Humor in Puns.
- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.

## [0.35.0] - 2025-01-31

### Changed
- **Unified QUD and GSQuestion**: `GSQuestion` is now an abbreviation for `QUD`
  - Single source of truth for partition/equivalence semantics in `Core/QUD.lean`
  - Added `trans` field to `QUD` to enforce full equivalence relation (reflexive, symmetric, transitive)
  - All theorems proven for QUD now apply to GSQuestion automatically

- **Removed invalid `disjGSQuestion`**: Disjunction of equivalence relations violates transitivity
  - Proper solution uses lifted types (continuation monad): `LiftedQuestion W = (GSQuestion W → Prop) → Prop`
  - `LiftedTypes.LiftedQuestion.disj` correctly handles question disjunction
  - Updated `Coordination.lean` and `ScopeReadings.lean` to use lifted types for disjunctive readings

### Architecture
- **Deep integration**: QUD = Partition = Decision Problem theorem chain now unified
- **Barker & Shan connection**: Lifted question types form continuation monad with proper monad laws

### References
- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Partee & Rooth (1983). Generalized Conjunction and Type Ambiguity.
- Barker & Shan (2014). Continuations and Natural Language.

## [0.34.0] - 2025-01-30

### Added
- **Core/ProbabilisticDynamics.lean**: Grove & White PDS monad infrastructure
  - `ProbMonad`: Abstract probability monad with monad laws
  - `PState`: Parameterized state monad for discourse dynamics
  - `CondProbMonad`: Conditioning via `observe` and `fail`
  - `ChoiceProbMonad`: Softmax choice for speaker models
  - `probProp`: Probability of Boolean property under distribution
  - Threshold semantics showing graded = Boolean + uncertainty

- **Theories/Comparisons/RSAandPDS.lean**: RSA as special case of PDS
  - `BooleanRSA`: Boolean literal semantics structure
  - `MonadicRSA`: RSA with explicit monadic operations
  - `ThresholdAdjective`: Lassiter & Goodman threshold semantics
  - Theorems: L0 = observe, S1 = choose, L1 = marginalize

### References
- Grove & White. Probabilistic Dynamic Semantics.
- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.

## [0.33.1] - 2025-01-30

### Changed
- **RSA.Eval cleanup**: Removed duplicate utility functions across implementations
  - SumersEtAl2023, YoonEtAl2020 now delegate to RSA.Eval
  - Removed unnecessary `[DecidableEq W]` constraints from simplified APIs
- **Float-based softmax**: RSA.Eval.softmax now uses real `Float.exp` for accurate computation
- **Distribution bridges**: Added `ExactDist.toList` and `ExactDist.toListWith` for representation conversion

## [0.33.0] - 2025-01-30

### Changed
- **RSA API Migration**: Fintype-based RSA is now the primary API
  - `RSAScenarioF` → `RSAScenario` (Fintype-based with compile-time guarantees)
  - `RSAF` namespace → `RSA` namespace (returns `Option (ExactDist α)`)
  - Removed list-based `RSAScenarioL`/`RSAL` from core `Basic.lean`
  - Added non-negativity proof fields to `RSAScenario` for `ExactDist` construction

- **New RSA.Eval module**: List-based helpers for `#eval` demonstrations
  - `Linglib/Theories/RSA/Core/Eval.lean`: Provides `basicL0`, `basicS1`, `L1_world`, etc.
  - All downstream files (~35) migrated to use `RSA.Eval.*` for kernel reduction
  - Maintains backward compatibility: same computational results, different API

- **Updated implementations**: All RSA paper replications migrated
  - FrankGoodman2012, GoodmanStuhlmuller2013, LassiterGoodman2017
  - KaoEtAl2014_Hyperbole, KaoEtAl2014_Metaphor, PottsEtAl2016
  - ScontrasPearl2021, ScontrasTonhauser2025, TesslerGoodman2022
  - YoonEtAl2020, TesslerFranke2020, DegenEtAl2020, and others

### Architecture
- **Dual-representation design** now fully realized:
  - `RSAScenario` + `RSA.L0/S1/L1` → `ExactDist` with sum-to-1 proofs (for theorems)
  - `RSA.Eval.*` → `List (α × ℚ)` (for `#eval` and `native_decide`)
  - `ExactDist.toPMF` bridges to Mathlib's PMF for measure-theoretic guarantees

### References
- Frank & Goodman (2012), Goodman & Frank (2016) for RSA foundations
- Mathlib PMF for probability distribution guarantees

## [0.32.0] - 2025-01-29

### Added
- **Theories/Montague/Anaphora.lean**: Binding semantics with categorical foundations
  - H&K assignment-based interpretation via `HasBindingConfig` interface
  - B&S continuation-based interpretation via W combinator
  - **Categorical connection**: Reader ↔ Continuation adjunction
    - `cpsTransform`: CPS transform between frameworks
    - `binding_is_contraction`: W = diagonal/contraction morphism
  - VPE strict/sloppy ambiguity

- **Core/Interfaces/BindingSemantics.lean**: Abstract interface for binding
  - `HasBindingConfig`: What syntax theories must provide for semantic binding
  - `BindingConfig`: Binder-bindee relations with variable indices
  - Theory-neutral: Minimalism, HPSG, CCG each satisfy differently

- **Phenomena/Anaphora/DonkeyAnaphora.lean**: Donkey anaphora data
  - Classic examples: Geach donkey, conditional donkey, bathroom sentences
  - Weak vs strong readings, proportion problem, paycheck pronouns

- **Theories/Montague/Questions/LiftedTypes.lean**: B&S tower notation documentation
  - Continuation monad laws, tower semantics for scope-taking

### Architecture
- Binding semantics separates syntax (what binds what) from semantics (how to interpret)
- Categorical perspective shows H&K assignments and B&S continuations are related via CPS
- Both reduce to "contraction" — using one entity in multiple positions

### References
- Heim & Kratzer (1998). Semantics in Generative Grammar. Ch. 5.
- Barker & Shan (2014). Continuations and Natural Language. Ch. 15.
- Geach (1962). Reference and Generality.

## [0.31.0] - 2025-01-29

### Added
- **Theories/Montague/Questions/**: G&S 1984 partition semantics for questions
  - `Basic.lean`: Core types (Question, Answer, Cell as W → Bool)
  - `Partition.lean`: GSQuestion structure with equivalence relation, refinement ⊑
  - `PragmaticAnswerhood.lean`: G&S Ch. IV pragmatic answerhood (information sets J)
    - `InfoSet`: Questioner's factual knowledge J ⊆ I
    - `isPragmaticAnswer`, `givesPragmaticAnswer`: Two notions of answerhood
    - Pragmatic term properties: `pragmaticallyRigid`, `pragmaticallyDefinite`, `pragmaticallyExhaustive`
    - Key theorems: `semantic_is_pragmatic_limit`, `exhaustive_rigid_gives_complete_answer`
  - `DecisionTheory.lean`: Van Rooy 2003 decision-theoretic semantics
  - `SignalingGames.lean`: Credibility and strategic communication (RSA bridge)
  - `Polarity.lean`: Van Rooy & Šafářová 2003 polar question pragmatics (PPQ/NPQ/Alt)

- **Phenomena/Questions/**: Empirical data for question-answer phenomena
  - `Basic.lean`: Core question data types
  - `WhComplement.lean`: Wh-complement clause data
  - `FocusAnswer.lean`: Focus-sensitive answer patterns
  - `Exhaustivity.lean`: Exhaustive interpretation data
  - `MultipleWh.lean`: Multiple wh-question data
  - `PolarAnswers.lean`: Yes/no answer patterns, conditional→biconditional, disjunction→exclusive
  - `PragmaticAnswerhood.lean`: G&S pragmatic rigidity/definiteness examples

- **Montague/Modification.lean**: Generic `predMod` for arbitrary entity types
  - Enables RSA implementations to use H&K predicate modification without full Montague infrastructure

- **RSA/Implementations/HawkinsGweonGoodman2021.lean**: Pedagogy RSA model
- **Phenomena/HawkinsGweonGoodman2021/Data.lean**: Pedagogy experiment data

### Architecture
- Question semantics connects to RSA via SignalingGames (speaker-listener recursion)
- Pragmatic answerhood relativizes semantic answerhood to information sets J
- When J = I (total ignorance), pragmatic answerhood reduces to semantic answerhood

### References
- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Van Rooy (2003). Questioning to Resolve Decision Problems.
- Van Rooy & Šafářová (2003). On Polar Questions.
- Hawkins, Gweon & Goodman (2021). Pedagogy and the pragmatics of examples.

## [0.30.0] - 2025-01-29

### Added
- **RSA/Implementations/GoodmanStuhlmuller2013.lean**: Grounding in Montague semantics
  - Imports `Montague.Quantifiers` and `Montague.Lexicon.Numerals.Compare`
  - `some_meaning_from_montague`, `all_meaning_from_montague`: Quantifier semantics grounded
  - `scalar_implicature_grounded`: Shows "some" has more compatible worlds than "all"
  - `lowerBound_grounded`, `exact_grounded`: Number word meanings match Montague theories
  - `grounding_enables_empirical_adjudication`: Full grounding chain from Montague to predictions
  - **UnifiedAPIVersion**: Demonstration using `RSAScenario.mentalStateBool`
    - `knowledgeStateUnified`: Boolean approximation of knowledge-state model
    - Documents connection to unified mental state API (BeliefState = Observation)
    - Notes limitation: unified API uses Boolean membership, G&S needs graded hypergeometric

### Architecture
- GoodmanStuhlmuller2013 RSA predictions now derive from Montague compositional semantics
- Numeral semantics (lower-bound vs exact) grounded in `Montague.Lexicon.Numerals`
- Empirical adjudication between semantic theories enabled by grounding
- Knowledge-state model: custom implementation preserves graded hypergeometric probabilities
  - The unified `mentalStateBool` API provides a Boolean approximation
  - G&S's model-specific hypergeometric remains in the custom implementation

## [0.29.0] - 2025-01-29

### Added
- **Theories/Montague/Lexicon/Degrees.lean**: Refactored from Fragments, now canonical location for degree semantics
  - `Degree`, `Threshold`, `NegationType`, `ThresholdPair`: Core types
  - `HasDegree` typeclass: measure functions μ : Entity → ℚ
  - Threshold semantics: `positiveMeaning`, `negativeMeaning`, `contraryNeg`, `contradictoryNeg`
  - Rounding/precision semantics (Lasersohn 1999 pragmatic halo):
    - `roundToNearest`: Round value to nearest multiple of base
    - `PrecisionMode`: exact vs approximate interpretation
    - `numeralWithPrecision`: Numeral meaning under precision mode
  - Compositional sentence semantics:
    - `MeasurePredicate`: Measure verbs like "cost"
    - `DegreePhrase`: Semantic value of "u dollars"
    - `measureSentence`: Full sentence "The X cost u dollars"
- **Theories/NeoGricean/Core/Markedness.lean**: Markedness computation from objective properties
- **Theories/RSA/Implementations/TesslerFranke2020.lean**: "Not unreasonable" flexible negation model

### Changed
- **Fragments/Degrees.lean**: Now imports from Montague, keeps RSA-specific domains (Price, Height, Temperature)
- **RSA/Implementations/KaoEtAl2014_Hyperbole.lean**: Full 5-QUD model matching paper
  - Goals: price, valence, priceValence, approxPrice, approxPriceValence
  - Item-specific priors (electricKettle, laptop, watch)
  - Grounding via `MeasurePredicate` and `measureSentence`
  - QUD equivalence with rounding for approximate goals
- **Montague/Lexicon/Adjectives/Theory.lean**: Updated imports to use Montague.Lexicon.Degrees

### Architecture
- Degree primitives now live in Montague (semantic theory), RSA domains in Fragments (experimental building blocks)
- Rounding semantics grounded in formal semantic theory (pragmatic halo, precision modes)

## [0.28.0] - 2025-01-29

### Added
- **Montague/Lexicon/Features.lean**: `HasColor`, `HasShape` typeclasses for generic feature predicates
  - Enables selectional restriction modeling (entities must implement typeclass to receive predicate)
  - Generic `featureMeaning {E} [HasColor E] [HasShape E]` works for any entity type
- **Fragments/Degrees.lean**: `HasDegree` typeclass for entities with numerical magnitudes
  - `numeralExact`, `numeralAtLeast`, `numeralApprox` for numeral expression semantics
  - Domain types: `Price.World`, `Height.World`, `Temperature.World`
  - Grounding for Kao et al. (2014) hyperbole model
- **docs/ROADMAP.md**: Note on selectional restrictions / category mistakes as future phenomenon

### Changed
- **Fragments/ReferenceGames.lean**: Now defines `Object` locally with `HasColor`/`HasShape` instances
  - Cleaner separation: Montague provides vocabulary, Fragment provides domain entity type
  - `featureMeaning` and `Feature.appliesTo` derived from generic Montague definitions
- **RSA/Implementations/FrankGoodman2012.lean**: Uses Montague-grounded reference game infrastructure
  - Grounding theorem: `meaning_from_compositional` shows RSA φ derives from Montague
- **RSA/Implementations/KaoEtAl2014_Hyperbole.lean**: Uses `HasDegree` from Degrees.lean
  - `Price` implements `HasDegree` via `Price.value`
  - `literal` uses `numeralExact` for grounded semantics
  - Grounding theorem: `literal_uses_degree`

### Architecture
- Feature predicates: theory-neutral vocabulary (Montague) vs domain-specific entities (Fragments)
- Degree/magnitude semantics: `HasDegree` typeclass unifies prices, heights, temperatures
- "John is tall" and "John is 6 feet" use the same underlying degree scale

## [0.27.0] - 2025-01-28

### Added
- **Theories/RSA/DegenEtAl2020.lean**: Continuous semantics RSA (cs-RSA) for referring expressions
  - Color/size asymmetry via semantic noise parameters (color ≈ 0.99, size ≈ 0.8)
  - Typicality effects (blue banana vs yellow banana)
  - Scene variation effects on redundant modifier use
  - Uses `ReferenceGame.Color` from Fragments library
- **Theories/RSA/Implementations/HeKaiserIskarous2025.lean**: Sentence polarity asymmetry models
  - Standard RSA, fuzzyRSA, wonkyRSA, funkyRSA variants
  - `toContextPolarity`: Maps sentence polarity → `Core.Polarity.ContextPolarity`
  - Proves cost asymmetry reflects UE/DE distinction
- **Phenomena/HeKaiserIskarous2025/Data.lean**: Domain types for polarity experiments

### Changed
- **Theories/RSA/Core/GradedSemantics.lean**: Removed (merged into LassiterGoodman2017.lean)
- LassiterGoodman2017.lean already contains graded semantics + threshold inference equivalence

### References
- Degen et al. (2020). "When redundancy is useful: A Bayesian approach to 'overinformative' referring expressions"
- He, Kaiser & Iskarous (2025). "Modeling sentence polarity asymmetries"

## [0.26.0] - 2025-01-28

### Added
- **NeoGricean/Exhaustivity/Unified.lean**: Unified exhaustification interface
  - `ExhOperator` enum (.IE, .MW) for selecting exhaustification strategy
  - `applyExh`: Single entry point for applying EXH operators
  - `applyExhAtParse`: Parse-guided EXH application (I → O → M order)
  - `Exhaustifiable` typeclass with position-dependent alternatives
  - Connects Spector 2007 (Gricean derivation), Spector 2016 (operators), and parse positions

### Changed
- **Core/Parse.lean**: Now contains `exhParses` and `scopeParses` as special cases of `Parse`
- **NeoGricean/Exhaustivity/Interface.lean**: Re-exports from Unified.lean
- **RSA/Implementations/FrankeBergen2020.lean**: Uses unified `Exhaustifiable` interface with position-dependent alternatives

### Architecture
- Any theory invoking EXH in a parse now uses the same machinery
- Clear separation: scope ambiguity uses `scopeParses` directly; EXH phenomena use `Exhaustifiable`

## [0.25.0] - 2025-01-28

### Added
- **Theories/Minimalism/MergeUnification.lean**: Formalization of Internal/External Merge unification
  - `ExternalMerge`, `InternalMerge`, `GeneralMerge` structures with containment preconditions
  - `harizanov_unification`: Both merge types satisfy same three properties (operation, labeling, projection)
  - `complete_harizanov_unification`: Main theorem connecting to HeadMovement types
  - Proves head-to-spec and head-to-head are both instances of InternalMerge

### References
- Chomsky (2004). "Beyond Explanatory Adequacy"
- Harizanov (2019). "Head movement and morphological realization"

## [0.24.0] - 2025-01-28

### Changed
- **Theories/NeoGricean/**: Restructured from flat to organized hierarchy
  - `Core/`: Basic.lean, Alternatives.lean, AlternativeGeneration.lean, Competence.lean
  - `Exhaustivity/`: Basic.lean
  - `ScalarImplicatures/`: Basic.lean, Operations.lean
  - `Implementations/`: Spector2007.lean, FoxSpector2018.lean, MontagueExhaustivity.lean
  - Top-level: NegationScope.lean, Presuppositions.lean

## [0.23.0] - 2025-01-28

### Changed
- **Theories/RSA/**: Restructured from flat to phenomenon-first organization
  - `Core/`: Basic.lean, BasicQ.lean, Examples.lean, Intensional.lean, Model.lean, GradedSemantics.lean, Convergence.lean
  - `ScalarImplicatures/`: Basic.lean, Hurford.lean, Embedded/{Basic,Attitudes,Conditionals,Questions}.lean
  - `Extensions/`: LexicalUncertainty/{Basic,Compositional}.lean, InformationTheory/{Basic,UtilityDynamics,UtilityNonMonotonicity,PhaseTransition,RateDistortion}.lean
  - `Implementations/`: Paper replications (FrankGoodman2012, GoodmanStuhlmuller2013, ScontrasPearl2021, KaoEtAl2014_{Hyperbole,Metaphor}, PottsEtAl2016, ScontrasTonhauser2025, LassiterGoodman2017, TesslerGoodman2022)
  - Updated all imports throughout codebase

## [0.22.0] - 2025-01-28

### Changed
- **Theories/RSA/Core.lean**: Unified RSAScenario to support 5 latent variable categories
  - World (epistemic), BeliefState (speaker's private assumptions), Goal (QUD), Interp (scope), Lexicon (LU)
  - `φ` now takes 4 args: `φ : Interp → Lexicon → Utterance → World → ℚ`
  - Renamed `QUD` → `Goal` with backward compatibility aliases
  - New smart constructors: `mentalState`, `mentalStateBool`, `lexicalUncertainty`
  - L0, S1, L1 now take all 5 latent parameters (use `()` for unused dimensions)

- All RSA models updated to unified API:
  - FrankGoodman2012, GoodmanStuhlmuller2013, GradedSemantics
  - KaoEtAl2014_Hyperbole, KaoEtAl2014_Metaphor, LassiterGoodman2017
  - InformationTheory/Basic, Fragments/Quantities, Fragments/ReferenceGames

### Removed
- **Theories/RSA/BToM/**: Removed deprecated compatibility layer
  - BToM functionality integrated into unified RSAScenario
  - `ScontrasTonhauser2025.lean` moved to `Theories/RSA/`

### References
- Unifies: Frank & Goodman (2012), Scontras & Pearl (2021), Kao et al. (2014), Bergen et al. (2016), Scontras & Tonhauser (2025)

## [0.21.0] - 2025-01-28

### Added
- **Theories/RSA/ScontrasTonhauser2025.lean**: Scontras & Tonhauser (2025) projection model
  - Formalizes "Projection without lexically-specified presupposition: A model for know"
  - Verifies all three empirical predictions:
    - (a) know > think in projection strength
    - (b) Higher prior P(C) → stronger projection
    - (c) BEL? QUD → stronger projection than C? QUD

- **Phenomena/Factives/DegenTonhauser2021.lean**: Empirical data on factive predicates

### References
- Scontras, G. & Tonhauser, J. (2025). Projection without lexically-specified presupposition
- WebPPL model: https://github.com/judith-tonhauser/SuB29-Scontras-Tonhauser

## [0.20.0] - 2025-01-27

### Changed
- **Core/Proposition.lean**: Integrate Mathlib BooleanAlgebra infrastructure
  - Added imports: `Mathlib.Order.BooleanAlgebra.Basic`, `Mathlib.Order.Monotone.Basic`
  - Correspondence theorems: `pand_eq_inf`, `por_eq_sup`, `pnot_eq_compl`, `entails_eq_le`
  - Documents that `Prop' W` and `BProp W` inherit `BooleanAlgebra` from Mathlib's Pi instance

- **Montague/Entailment/Polarity.lean**: Use Mathlib Monotone/Antitone for polarity
  - `IsUpwardEntailing` is now abbreviation for `Monotone`
  - `IsDownwardEntailing` is now abbreviation for `Antitone`
  - Composition rules now come from Mathlib for free:
    - `Monotone.comp`: UE ∘ UE = UE
    - `Antitone.comp`: DE ∘ DE = UE (double negation rule)
    - `Monotone.comp_antitone`: UE ∘ DE = DE
    - `Antitone.comp_monotone`: DE ∘ UE = DE

- **Montague/Derivation/Basic.lean**: Consolidate ContextPolarity
  - Now imports and re-exports `ContextPolarity` from `Core.Polarity`
  - Removes duplicate definition (was defined in both Core and Derivation)

### References
- Mathlib `Order.Monotone.Defs` for Monotone/Antitone composition lemmas

## [0.19.0] - 2025-01-27

### Added
- **Theories/Comparisons/CommandRelations.lean**: Complete B&P Theorem 9 (Union Theorem)
  - `nonminimal_in_maximalGenerator`: Non-minimal upper bounds are in maximal generators
  - `relation_union_theorem_reverse`: C_{R̂∩Ŝ} ⊆ C_R ∪ C_S (uses CAC)
  - Both directions of Union Theorem now fully proved

### Changed
- Updated documentation to reflect completed theorems and remaining sorries

## [0.18.0] - 2025-01-27

### Added
- **Theories/Montague/Variables.lean**: Heim & Kratzer Ch. 5 assignment function infrastructure
  - `Assignment m`: Structure mapping variable indices to entities
  - `Assignment.update` (notation: `g[n ↦ x]`): Modified assignment
  - `DenotG m ty`: Assignment-relative denotations
  - `interpPronoun`, `lambdaAbsG`: Pronoun interpretation and λ-abstraction
  - Key lemmas: `update_same`, `update_other`, `update_update_comm`, `update_self`

- **Theories/Montague/Modification.lean**: Heim & Kratzer Ch. 4 Predicate Modification
  - `predicateModification` (notation: `⊓ₚ`): Intersect two ⟨e,t⟩ predicates
  - Algebraic properties: commutativity, associativity, idempotence, identity, annihilator
  - `predicateModification_extension`: PM = set intersection

- **Theories/Minimalism/Semantics/Interface.lean**: Trace interpretation for movement
  - `interpTrace n`: Traces as variables (H&K insight: traces = pronouns semantically)
  - `predicateAbstraction n body`: λ-binding at movement landing sites
  - `relativePM`: Combines predicate abstraction with Predicate Modification

- **Theories/Minimalism/Semantics/RelativeClauses.lean**: Full worked example
  - "the book that John read _" derivation
  - `the_book_correct`: Proves ιx[book(x) ∧ read(j,x)] = book1
  - `np_assignment_independent`: Bound variables don't leak

### References
- Heim & Kratzer (1998) "Semantics in Generative Grammar", Chapters 4, 5, 7

## [0.17.0] - 2025-01-27

### Added
- **Theories/RSA/InformationTheory/**: Zaslavsky et al. (2020) rate-distortion formalization
  - `Basic.lean`: G_α objective, H_S entropy, E[V_L] utility, RSA dynamics with rational α
  - `UtilityNonMonotonicity.lean`: Prop 2 counterexample with graded lexicon (α < 1)
  - `PhaseTransition.lean`: Prop 3 critical point at α = 1

- **Theories/RSA/CoreQ.lean**: RSAScenarioQ with rational α parameter
  - `S1Q`, `L0Q`, `L1Q` using `powApprox` for x^α
  - Smart constructors: `RSAScenarioQ.basic`, `basicBool`

- **Core/RationalPower.lean**: Newton-Raphson n-th root approximation
  - `nthRootApprox`: Computes x^(1/n) via iteration
  - `powApprox`: Computes x^(p/q) for rational exponents

### Changed
- **Theories/Comparisons/RSANeoGricean.lean**: Added information-theoretic perspective on NeoGricean limit

## [0.16.0] - 2025-01-27

### Changed
- **Core/RSA.lean**: Unified RSA API - renamed `UnifiedRSA` namespace to `RSA`, consolidated all RSA computations
  - Smart constructors: `RSAScenario.basic`, `basicBool`, `ambiguous`, `ambiguousBool`, `qud`, `qudBool`
  - Updated signatures: `RSA.L0 S u i`, `RSA.S1 S w i q`, `RSA.L1_world`, `RSA.L1_interp`, `RSA.L1_qud`
  - Legacy `SimpleRSAScenario` and `ParametricRSAScenario` kept for backward compatibility

- **Core/Fragments/Quantities.lean**, **ReferenceGames.lean**: Migrated to unified RSA API

- **Theories/RSA/**: All paper replications migrated to unified API
  - `Basic.lean`: `SimpleRSAScenario.ofBool` → `RSAScenario.basicBool`
  - `FrankGoodman2012.lean`, `GoodmanStuhlmuller2013.lean`, `ScalarImplicatures.lean`: `RSA.L1` → `RSA.L1_world`
  - `GradedSemantics.lean`: Updated to `RSAScenario.basic`
  - `LassiterGoodman2017.lean`, `ScontrasPearl2021.lean`: `ParametricRSA` → `RSAScenario.ambiguousBool`
  - `KaoEtAl2014.lean`, `KaoMetaphor.lean`: `UnifiedRSA` → `RSA`

- **Core/LexicalUncertainty.lean**: Updated `Lexicon.ofRSA` → `Lexicon.ofScenario`, `LUScenario.toRSA` → `LUScenario.toRSAScenario`

## [0.15.0] - 2025-01-26

### Added
- **Theories/NeoGricean/MontagueExhaustivity.lean**: Bridge connecting Montague compositional semantics to exhaustivity operators
  - World-indexed Montague models with `Student` entities
  - `somePassedMontague`, `allPassedMontague`: Compositionally computed via `some_sem`/`every_sem`
  - `somePassed_eq_handcrafted`, `allPassed_eq_handcrafted`: Grounding theorems
  - `exhMW_somePassed_at_w1`, `exhIE_somePassed_at_w1`: Exhaustivity on compositional meanings
  - Closes CLAUDE.md gap: "Entailment ungrounded" → now grounded in Montague

- **Theories/NeoGricean/ScaleSemantics.lean**: Semantic structures for scalar implicature phenomena
  - `HornScale World`: Scale with semantic content and entailment proofs
  - `HurfordSemantic`, `SinghSemantic`: Structures for disjunction phenomena
  - Concrete scales: `someAllScale`, `orAndScale`, `possibleNecessaryScale`
  - World types: `QuantWorld`, `ConnWorld`, `ModalWorld`

- **Theories/NeoGricean/Spector2007.lean**: Formalization of Spector (2007) "Scalar implicatures: exhaustivity and Gricean reasoning"
  - Valuations as Finsets of true atoms
  - Propositions as sets of valuations
  - Literal favoring and positive propositions
  - Exhaustification via minimal valuations
  - Main result: For positive P, Max(P) = {Exhaust(P)}

- **Phenomena/ScalarImplicatures/**: Theory-neutral empirical data
  - `Scales.lean`: Horn scale examples (some/all, or/and, possible/necessary)
  - `Hurford.lean`: Hurford's constraint data (rescued vs unrescued violations)
  - `Singh.lean`: Singh's asymmetry data (weak-first vs strong-first)

### Changed
- **Theories/NeoGricean/Exhaustivity.lean**: Completed Theorem 9 proofs
  - `someAll_exhMW_iff_exhIE`: Full proof that exhMW ≡ exhIE for some/all scale
  - `orAnd_exhMW_iff_exhIE`: Full proof for or/and scale
  - Added Section 6: Worked examples with `w1`, `w3`, `wSang`, `wBoth`
  - Key lemmas proving `¬stronger ∈ IE` via MC-set maximality

- **Theories/NeoGricean/FoxSpector2018.lean**: Completed Singh asymmetry proofs
  - `singh_weak_exh_nonvacuous`: Proves exh on weak is non-vacuous when it excludes
  - `singh_strong_exh_vacuous`: Proves exh on strong is vacuous when strong ⊆ weak
  - Full proofs via MC-set analysis (no `sorry`s)

### References
- Spector (2007) "Scalar implicatures: exhaustivity and Gricean reasoning"
- Spector (2016) "Comparing exhaustivity operators"
- Fox & Spector (2018) "Economy and embedded exhaustification"

## [0.14.0] - 2025-01-26

### Added
- **Theories/NeoGricean/Exhaustivity.lean**: Formalization of Spector (2016) "Comparing exhaustivity operators"
  - Core definitions: `exhMW` (minimal worlds), `exhIE` (innocent exclusion)
  - `≤_ALT` preorder on worlds, MC-sets, innocent excludability
  - Lemmas 1-3: Connection between minimal worlds and MC-sets
  - Propositions 6-7, Corollary 8: Relationships between operators
  - **Theorem 9**: When ALT closed under ∧, exh_mw ≡ exh_ie
  - Theorem 10: Disjunction closure vacuous for exh_ie
  - Corollary 11: If ALT∨ closed under ∧, then exh_mw ≡ exh_ie

- **Core/QUD.lean**: QUD (Question Under Discussion) infrastructure for RSA
  - `QUD` structure: Represents communicative goals via meaning equivalence
  - `QUDRSAScenario`: RSA scenario with multiple possible QUDs
  - `QUDRSA.L0`: Literal listener (QUD-unaware)
  - `QUDRSA.L0_projected`: L0 probability projected onto QUD equivalence classes
  - `QUDRSA.S1`: QUD-sensitive speaker (optimizes w.r.t. projected meaning)
  - `QUDRSA.L1`: QUD-marginalizing listener
  - `QUDRSA.L1_joint`: Joint distribution over (Meaning × Goal)
  - `QUDRSA.L1_goal`: Marginal goal distribution
  - `ProductQUD`: Common patterns for product meaning spaces (fst, snd, both)
  - `PrecisionProjection`: Approximate vs exact communication patterns

- **Theories/RSA/KaoEtAl2014.lean**: Hyperbole model (Kao et al. 2014)
  - Models "Nonliteral understanding of number words" (PNAS 111(33))
  - Multi-dimensional meaning space: Price × Affect
  - QUDs: "price", "affect", "both"
  - Extended semantics with utterance arousal
  - Key predictions verified:
    - S1 prefers hyperbole under "affect" QUD
    - S1 prefers literal under "price" QUD
    - L1 infers high affect from hyperbolic utterances
    - L1 infers "affect" QUD from hyperbole

- **Core/Fragments/**: Building blocks for RSA scenarios
  - `ReferenceGames.lean`: Reference game components
    - `Color`, `Shape`, `Object`, `Feature`: Standard types
    - `TypedContext`: Objects with features
    - `fromPairs`, `colorsOnly`, `shapesOnly`: Context builders
    - `l0`, `s1`, `l1`: Convenience wrappers
  - `Quantities.lean`: Quantity/scalar domain components
    - `Domain n`: Parameterized by size (n+1 worlds)
    - `Utterance`: none/some/all
    - `ExtUtterance`: Adds "most"
    - `standard n`, `withPrior`: Domain builders
  - `Scales.lean`: Reusable scale definitions
    - `Scale α`: Ordered alternatives from weak to strong
    - Horn scales: `someAll`, `someMostAll`, `orAnd`
    - Modal scales: `mightMust`, `possibleNecessary`
    - Degree scales: `warmHot`, `goodExcellent`
    - `numerals n`: Build numeral scale 1..n

## [0.13.0] - 2025-01-26

### Changed
- **Core/RSA.lean**: Made `RSAScenario` typed with explicit type parameters
  - Old: `RSAScenario` with `Utterance : Type` and `World : Type` as fields
  - New: `RSAScenario (U : Type) (W : Type)` with type parameters
  - Removes `TypedRSAScenario` structure (now redundant)
  - `L0_dist`, `S1_dist`, `L1_dist` take non-negativity proofs as explicit parameters
  - Added helper theorems `ofBool_prior_nonneg`, `ofBool_φ_nonneg`

### Added
- **Theories/RSA/AttitudeEmbedding.lean**: Semantic grounding proofs
  - `somePassedProp`, `someNotAllPassedProp`, `allPassedProp`: Compositional semantics
  - `global_grounded`, `local_grounded`, `believes_all_grounded`: Grounding theorems
  - `local_entails_global_grounded`: Entailment derived from semantics
- **Theories/RSA/QuestionEmbedding.lean**: Scalar implicatures in yes/no questions
- **Theories/Comparisons/RSANeoGricean.lean**: RSA vs NeoGricean comparison

### Fixed
- Updated all RSA models to use typed `RSAScenario (U W : Type)` syntax

## [0.12.0] - 2025-01-26

### Added
- **Core/FormalLanguageTheory.lean**: Chomsky hierarchy infrastructure
  - `FourSymbol` alphabet for cross-serial patterns (a, b, c, d)
  - `isInLanguage_anbncndn`: Membership predicate for {aⁿbⁿcⁿdⁿ}
  - `makeString_anbncndn`: Generator function
  - Pumping lemma (axiom) and `anbncndn_not_context_free` theorem
  - `MildlyContextSensitive` structure with `CCG_MCS`, `TAG_MCS` instances

- **Theories/CCG/GenerativeCapacity.lean**: CCG vs CFG expressiveness
  - `ccg_strictly_more_expressive_than_cfg`: Main theorem (infrastructure)
  - `cross_serial_requires_mcs`: Proven by rfl
  - Connects CCG cross-serial derivations to formal language theory

- **Theories/RSA/PottsLU.lean**: Full Potts et al. (2016) Lexical Uncertainty model
  - 10 world classes (3 players × 3 outcomes)
  - 4 lexica (2 refinable items: quantifier + predicate)
  - 11 utterances (quantifier × predicate combinations)
  - `potts_model_derives_de_blocking`: Global > Local in DE contexts
  - `potts_model_derives_ue_implicature`: Local > Global in UE contexts
  - Regression tests: `simplified_model_fails`, `world_space_is_critical`

- **Theories/RSA/EmbeddedScalars.lean**: Simplified model documentation
  - Documents why reduced 3-world model gives inverted predictions
  - Points to PottsLU.lean for full model

- **Core/LexicalUncertainty.lean**: LU infrastructure for RSA
- **Core/CompositionalLU.lean**: Compositional LU integration
- **Phenomena/Imprecision/Basic.lean**: Haslinger (2024) imprecision data

### References
- Potts, Lassiter, Levy & Frank (2016) "Embedded implicatures as pragmatic inferences under compositional lexical uncertainty"
- Steedman (2000) "The Syntactic Process" Ch. 2 & 6
- Joshi (1985) "Tree Adjoining Grammars"

## [0.11.0] - 2025-01-26

### Added
- **Core/Distribution.lean**: Typed probability distributions with compile-time guarantees
  - `ExactDist α`: Structure with `mass : α → ℚ`, `nonneg`, `sum_one` fields
  - `ExactDist.normalize`: Build distribution from unnormalized scores
  - `ExactDist.tryNormalize`: Returns `Option` for degenerate cases
  - `ExactDist.uniform`: Uniform distribution over finite type
  - `ExactDist.pure`: Point mass distribution
  - `ExactDist.toPMF`: Noncomputable bridge to Mathlib's PMF
  - `support_nonempty`, `mass_le_one`: Derived theorems

- **Core/RSA.lean**: Typed distribution API
  - `TypedRSAScenario`: RSAScenario with Fintype instances and non-negativity proofs
  - `TypedRSAScenario.ofBool`: Constructor for Boolean semantics
  - `L0_dist`, `S1_dist`, `L1_dist`: Return `Option (ExactDist _)` with sum-to-1 guarantee

- **Theories/RSA/FrankGoodman2012.lean**: Migrated to typed distributions
  - `refGameTyped`: TypedRSAScenario version of reference game
  - `l0_square_typed`, `l1_square_typed`, etc.: Typed distribution examples
  - `typed_reference_game_inference`: Theorem with `native_decide` proof

### Architecture
- **Dual-representation design**: Keep exact ℚ for computation (`native_decide`), bridge to Mathlib PMF for measure-theoretic theorems
- Distributions carry compile-time proof that `∑ x, mass x = 1`
- Legacy `List (α × ℚ)` API preserved for backward compatibility

### References
- Frank & Goodman (2012) "Predicting Pragmatic Reasoning in Language Games"
- Goodman & Frank (2016) "Pragmatic Language Interpretation as Probabilistic Inference"

## [0.10.0] - 2025-01-25

### Added
- **Montague/Lexicon/Modals/**: Modal theory infrastructure (Kratzer vs Simple/Kripke)
  - `Theory.lean`: `ModalTheory` structure for competing modal analyses
  - `Kratzer.lean`: Conversational backgrounds (modal base + ordering source)
  - `Simple.lean`: Primitive accessibility relations (Kripke semantics)
  - `Compare.lean`: Theory comparison and divergence theorems

### Changed
- **Montague directory restructure**: Organized into subdirectories
  - `Derivation/`: Basic.lean, Scope.lean, TruthConditions.lean
  - `Entailment/`: Basic.lean, Monotonicity.lean, ScaleInteraction.lean
  - `Intensional/`: Basic.lean
  - `Interface/`: SemanticBackend.lean, SyntaxInterface.lean
  - `Lexicon/`: Basic.lean, Modals/, Numerals/

### Removed
- Old flat Montague files (replaced by new directory structure)

## [0.9.2] - 2025-01-25

### Added
- **Montague/Lexicon/Numerals/DeFregean.lean**: Kennedy (2015) de-Fregean semantics
  - Bare numerals mean =n (like Exact), but derived via maximality operator
  - Key insight: DeFregean = Exact for bare numerals; difference is with modifiers
  - RSA role shifts: derives ignorance implicatures for Class B modifiers, not exact readings
  - Placeholder for Degree/ module which will handle Class A/B modifier distinction

### Architecture
- Numeral theories (LowerBound, Exact, DeFregean) stay in `Numerals/`
- Degree expressions ("more than", "at least") will go in `Degree/` (not numeral-specific)

## [0.9.1] - 2025-01-25

### Added
- **NeoGricean/Operations.lean**: Horn (1972) §1.22 implicature operations
  - `ImplicatureOperation` type: assert, contradict, suspend
  - Felicity conditions based on ambiguity (operations require implicature to target)
  - Proves lower-bound predicts felicitous operations, exact predicts infelicitous

- **NeoGricean/NegationScope.lean**: Negation scope asymmetry (Jespersen/Horn)
  - `NegationScope` type: internal (targets lower bound) vs external (targets exact)
  - "doesn't have 3" (internal) = <3 vs "doesn't have THREE" (external) = ≠3
  - Proves asymmetry predicted by lower-bound, collapses in exact semantics

### Architecture
- Operations and NegationScope are NeoGricean theory-internal concepts
- They're currently applied to numerals but could generalize to any scalar items
- Kept in `NeoGricean/` namespace, import numeral theories for concrete examples

### Key Insight
These patterns provide empirical evidence for lower-bound semantics:
- Operations (assert/contradict/suspend) require an implicature to operate on
- Negation scope distinction requires a lower bound to negate internally

## [0.9.0] - 2025-01-25

### Added
- **Montague/Lexicon/Numerals/**: Parameterized lexicon infrastructure
  - `Theory.lean`: `NumeralTheory` structure for competing semantic analyses
  - `LowerBound.lean`: Lower-bound semantics ("two" = ≥2, Horn 1972)
  - `Exact.lean`: Exact semantics ("two" = =2)
  - `Compare.lean`: Comparison infrastructure and key theorems
  - Each theory produces an `RSAScenario` for pragmatic reasoning
  - Theorems proving theories diverge: `lowerBound_exact_differ_on_two`
  - Ambiguity analysis: Lower-bound has it, Exact doesn't

### Removed
- **Montague/Numbers.lean**: Replaced by `Montague/Lexicon/Numerals/`

### Architecture
- Competing semantic analyses as explicit structures, not typeclasses
- Each analysis derives `toScenario : RSAScenario` for RSA integration
- Pattern ready to extend to Modals (Kratzer vs Simple)

## [0.8.0] - 2025-01-25

### Changed
- **Core/RSA.lean**: Simplified to direct ℚ arithmetic
  - Removed `RSAScore` typeclass - all computation now uses Mathlib's `ℚ` directly
  - Enables direct use of Mathlib lemmas (`Rat.mul_zero`, `Rat.div_def`, etc.)
  - Added `getScore_normalize_zero` helper lemma for proof composition

### Added
- **Core/RSA.lean**: Grounding theorems fully proven
  - `L0_prob_zero_when_false`: L0 assigns zero probability when φ = 0
  - `S1_zero_when_false`: S1 assigns zero probability when φ = 0
  - Both use `LawfulBEq` constraint to convert `==` to `=`

- **RSA/Intensional.lean**: Fixed grounding proofs
  - `l0_uses_compositional_meaning`: L0 nonzero → Montague meaning true
  - `l0_zero_when_false`: False meaning → zero probability
  - Uses `Option.map_eq_some_iff` + `List.find?_some` pattern from Mathlib

### Architecture
- RSA now uses exact rational arithmetic throughout
- Boolean semantics: φ ∈ {0, 1} via `boolToRat`
- Graded semantics: φ ∈ [0, 1] ⊂ ℚ (constraint as Prop, not enforced by type)
- Distribution type planned for Phase 2.4 to add compile-time probability guarantees

## [0.7.0] - 2025-01-25

### Added
- **Core/RSA.lean**: `RSAScore` typeclass for score types
  - Provides arithmetic operations: `zero`, `one`, `add`, `mul`, `div`, `lt`
  - Instance `RSAScore Frac`: Exact rational arithmetic for proofs
  - Instance `RSAScore Float`: Floating-point for empirical work

- **Core/RSA.lean**: Unified `RSAScenario Score` structure
  - Replaces `FiniteSemanticBackend` (Boolean) and `SemanticBackend` class (Float)
  - `φ : Utterance → World → Score` (generalized from Boolean)
  - `prior : World → Score` (P(w) distribution)
  - `α : Score` (rationality parameter)
  - `RSAScenario.ofBool`: Helper to build from Boolean satisfaction relation

- **Core/RSA.lean**: Unified `ParametricRSAScenario Score` structure
  - `Interp` type for scope/interpretation ambiguity
  - `interpPrior : Interp → Score` for P(i) distribution
  - `L1_joint`, `L1_world`, `L1_interp` for joint/marginal inference

- **Type aliases**: `ExactRSAScenario` (Frac) and `SoftRSAScenario` (Float)

- **Theories/RSA/GradedSemantics.lean**: New module demonstrating non-Boolean φ
  - Vague adjectives example: "tall"/"short" with degrees in [0,1]
  - `tallDegree : Height → Frac` (e.g., 190cm → 9/10, 170cm → 5/10)
  - Shows RSA naturally handles vagueness without hard thresholds
  - References: Lassiter & Goodman (2017), Qing & Franke (2014)

- **Core/Frac.lean**: Added helper operations
  - `Frac.sub`: Subtraction (saturating at zero)
  - `Frac.toFloat`: Conversion to Float

### Changed
- **Core/SemanticBackend.lean**: Gutted to minimal re-exports
  - Now just re-exports RSA types for backward compatibility
  - `LiteralBackend` = `ExactRSAScenario`, `GradedBackend` = `SoftRSAScenario`

- **Theories/RSA/Basic.lean**: Migrated to `RSAScenario.ofBool`
  - `scalarScenario` replaces old `scalarBackend`
  - Legacy alias preserved for compatibility

- **Theories/RSA/FrankGoodman2012.lean**: Migrated to new API
  - `refGameScenario` with `RSAScenario.ofBool`

- **Theories/RSA/ScalarImplicatures.lean**: Updated imports
  - Uses `RSA.L0`, `RSA.L1` with explicit scenario

- **Theories/RSA/GoodmanStuhlmuller2013.lean**: Updated references
  - `scalarBackend` → `scalarScenario`

- **Theories/RSA/ScontrasPearl2021.lean**: Migrated to `ParametricRSAScenario`
  - `scopeScenario` via `ParametricRSAScenario.ofBool`
  - Grounding theorem preserved: `rsa_meaning_from_montague`

- **Theories/Montague/Numbers.lean**: Migrated both backends
  - `LowerBound.scenario`, `Exact.scenario` via `RSAScenario.ofBool`

### Why This Matters
This unification enables:
1. **Graded semantics**: φ ∈ [0,1] for vagueness, not just Boolean
2. **Single interface**: One structure for exact proofs AND empirical work
3. **Priors and rationality**: P(w), P(i), and α built into the structure
4. **Cleaner architecture**: No more parallel SemanticBackend class hierarchy

### Key Insight
RSA's meaning function should be *flexible* in score type:
- `Frac` for proofs with `native_decide`
- `Float` for fitting empirical data
- Non-Boolean for graded phenomena (vagueness, gradable adjectives)

The same `RSAScenario` interface works for all.

### References
- Lassiter & Goodman (2017) "Adjectival vagueness in a Bayesian model"
- Qing & Franke (2014) "Gradable adjectives, vagueness, and optimal language use"

## [0.6.5] - 2025-01-25

### Changed
- **Core/RSA.lean**: Refactored to mathlib-style architecture
  - Changed `FiniteSemanticBackend` from class to structure for explicit parameterization
  - Renamed `meaning` field to `satisfies` for clarity (satisfies relation: World → Utterance → Bool)
  - Renamed `L0_scores`/`S1_scores`/`L1_scores` to `L0`/`S1`/`L1`
  - All RSA functions now take the backend as explicit first argument
  - Added `L0_prob`, `S1_prob`, `L1_prob` convenience functions
  - Proved `L0_zero_when_false` theorem (L0 assigns zero to false worlds)

- **Core/RSA.lean** (`ParametricRSA` namespace): Same refactoring
  - `ParametricSemanticBackend` is now a structure
  - Renamed `L1_joint_scores`/`L1_world_scores`/`L1_interp_scores` to `L1_joint`/`L1_world`/`L1_interp`

- **Theories/RSA/*.lean**: Updated all RSA modules to use new structure-based API
  - `Basic.lean`: `scalarBackend` replaces instance
  - `FrankGoodman2012.lean`: `refGameBackend` replaces instance
  - `ScalarImplicatures.lean`: Updated to use `RSA.L0`/`RSA.L1`
  - `ScontrasPearl2021.lean`: `scopeBackend` replaces instance

- **Theories/Montague/Numbers.lean**: Updated semantic backends
  - `LowerBound.backend` and `Exact.backend` replace instances

### Why This Matters
The mathlib-style architecture (structures over classes, explicit parameters) enables:
1. Multiple backends in the same scope without ambiguity
2. Grounding by construction: building the backend IS the proof
3. Cleaner dependency tracking between semantics and pragmatics

## [0.6.4] - 2025-01-25

### Added
- **Theories/Montague/Intensional.lean**: World-parameterized meanings for RSA integration
  - `IntensionalModel`: Model with explicit World type
  - `Intension m τ`: World → Extension(τ) type family
  - `Proposition m`: World → Bool (propositions as intensions of type t)
  - `IntensionalDerivation`: Derivation with world-varying meaning
  - `someIntensional`, `everyIntensional`: Quantifiers over intensional properties
  - `phi`: RSA's literal semantics function (φ(u, w) = ⟦u⟧(w))
  - Example: `someStudentsSleep_intensional` with proven truth conditions per world
  - Key theorems: `some_false_at_none`, `some_true_at_someNotAll`, `every_true_at_all`, etc.

- **Theories/RSA/Intensional.lean**: RSA with compositional Montague semantics
  - `PropDerivation`: Propositional derivation (type t) for RSA
  - `L0_from_derivation`: L0 computed by evaluating Montague meaning
  - `S1_from_derivations`, `L1_from_derivations`: Full grounded RSA pipeline
  - `IntensionalScenario`: RSA scenario built from compositional derivations
  - Grounding theorem: `l0_uses_compositional_meaning`
  - Key result: `scalar_implicature_from_grounded_rsa` - implicature emerges from compositional semantics

### Changed
- **docs/ROADMAP.md**: Reorganized with phased priority structure
  - Phase 1: Intensional Grounding (all three tasks now complete)
  - Phase 2: Type Safety & Robustness
  - Phase 3: Competing Analyses Infrastructure
  - Phase 4: Syntax Expansion

### Key Insight
RSA's scalar implicature now emerges from compositional Montague semantics, not stipulation:
1. Montague provides: `⟦some students sleep⟧(w) = ∃x.student(x) ∧ sleep(w)(x)`
2. L0 evaluates: `P(w | u) ∝ δ⟦u⟧(w)` (indicator from Montague)
3. S1 prefers informative utterances: speaker says "every" in all-worlds
4. L1 infers: "some" → probably someNotAll world (scalar implicature!)

Verified by #eval: `L1("some") = {someNotAll: 1/1, all: 1/3}`

### References
- Montague (1973) "The Proper Treatment of Quantification in Ordinary English"
- Gallin (1975) "Intensional and Higher-Order Modal Logic"
- Goodman & Frank (2016) "Pragmatic Language Interpretation as Probabilistic Inference"

## [0.6.3] - 2025-01-25

### Added
- **Theories/Montague/Conjunction.lean**: Partee & Rooth (1983) generalized conjunction
  - `Ty.isConjoinable`: Recursive predicate for types that "end in t"
  - `genConj`, `genDisj`: Pointwise conjunction/disjunction over any conjoinable type
  - Algebraic properties: commutativity, associativity at type t
  - Example: "tall and happy" computed via `genConj (e→t)`
  - Documentation of limitations: collective readings, non-Boolean coordination

- **Theories/CCG/CrossSerial.lean**: Real CCG derivations for Dutch cross-serial
  - `InfSubj` category: `(S\NP)/NP` for verb-raising infinitives
  - 2-verb derivation (`jan_zag_zwemmen_piet`): Uses forward composition + application
  - `derivation_2v_yields_S`, `derivation_3v_yields_S`: Theorems proving derivations work
  - `ccg_crossSerial_complete`: Combined theorem for well-formedness and data matching

- **Theories/CCG/Equivalence.lean**: Catalan numbers and bracketing enumeration
  - `BinTree`: Full binary trees representing bracketings
  - `allTreesWithLeaves n`: Enumerates all binary trees with n leaves
  - `countBracketings n`: Counts bracketings (matches Catalan recurrence)
  - `catalan`: Catalan numbers via closed formula
  - Key theorems:
    - `tree_count_eq_catalan_*`: Tree enumeration count = Catalan(n-1)
    - `catalan_counts_bracketings_*`: Bracketing count = Catalan number
    - `bracketings_eq_tree_count_*`: bracketings function matches tree enumeration

### Changed
- Removed generalized conjunction from `CCG/Semantics.lean` (was misplaced; it's Montague semantics, not CCG-specific)
- Cleaned up CrossSerial.lean: removed experimental code, kept working derivations

### Key Insights
1. **Generalized conjunction** is Montague semantics, not CCG. CCG provides syntax; Montague provides semantic combination.
2. **Catalan numbers count bracketings**: n words with purely compositional derivation have C_{n-1} structurally distinct derivations, all semantically equivalent due to associativity of B.

### References
- Partee & Rooth (1983) "Generalized Conjunction and Type Ambiguity"
- Steedman (2000) "The Syntactic Process" Chapters 6, 9

## [0.6.2] - 2025-01-25

### Added
- **Phenomena/Gapping/Data.lean**: Gapping and word order typology (Steedman 2000 Ch. 7)
  - `WordOrder`: SOV, SVO, VSO, VOS, OVS, OSV
  - `WordOrderProfile`: main vs subordinate clause orders
  - `GappingDirection`: forward vs backward
  - `GappingPattern`: which directions a language allows
  - `rossOriginal`, `rossRevised`: Ross's generalization (original and Steedman's revision)
  - Examples: Japanese (SOV), Irish (VSO), English (SVO), Dutch (mixed)
  - `EllipsisType`: gapping, stripping, VP ellipsis, sluicing
  - Key theorems: `sov_backward_only`, `vso_forward_only`, `svo_forward_only`, `mixed_allows_both`

- **Theories/CCG/Gapping.lean**: CCG analysis of gapping (Steedman 2000 Ch. 7)
  - `GappedTV`: S\((S/NP)/NP) - gapped transitive category
  - `GappedSubj`: S\(S/NP) - stripping category
  - `BackwardRaisedNP`, `ForwardRaisedNP`: type-raised NP categories
  - `hasBackwardRaising`, `hasForwardRaising`: what type-raising a word order allows
  - `predictedGappingPattern`: CCG prediction from word order
  - Key theorems:
    - `ross_from_ccg_principles`: Ross's generalization emerges from CCG
    - `svo_patterns_with_vso`: SVO patterns with VSO (forward gapping)
    - `no_backward_gapping_in_english`: Why *SO and SVO fails
    - `gapped_tv_is_leftward`: Gapped category direction determines pattern
    - `dutch_allows_both_gapping`: Mixed-order languages allow both

### Key Insight
Gapping is NOT ellipsis - it's ordinary constituent coordination! The "gapped" right conjunct (e.g., "Warren, potatoes") IS a CCG constituent with category S\((S/NP)/NP). Ross's generalization about gapping direction emerges from the Principles of Consistency and Inheritance: gapped constituents inherit directionality from verb categories, so SVO patterns with VSO (forward gapping) rather than SOV (backward gapping).

### References
- Steedman (2000) "The Syntactic Process" Chapter 7
- Ross (1970) "Gapping and the order of constituents"
- Maling (1972) "On 'Gapping and the order of constituents'"

## [0.6.1] - 2025-01-25

### Added
- **Phenomena/CrossSerialDependencies/Data.lean**: Dutch cross-serial dependency data (Steedman 2000 Ch. 6)
  - `Dependency`: NP-verb pairings (which NP binds to which verb)
  - `DependencyPattern`: crossSerial (Dutch) vs nested (German)
  - `DutchExample`/`GermanExample`: Empirical data structures
  - `crossSerialDeps`, `nestedDeps`: Generate dependency patterns
  - Examples: 2, 3, 4 NP-V clusters with cross-serial bindings
  - `FormalLanguageType`: contextFree vs mildlyContextSensitive

- **Theories/CCG/CrossSerial.lean**: CCG analysis of cross-serial dependencies
  - `forwardComp2` (B²): X/Y (Y/Z)/W → (X/Z)/W
  - `forwardComp3` (B³): X/Y ((Y/Z)/W)/V → ((X/Z)/W)/V
  - Dutch lexicon: perception verbs (zag), control verbs (helpen, laten)
  - `AnnotatedDerivation`: Derivation with NP-V binding annotations
  - Key theorems:
    - `ccg_produces_crossSerial_2`: 2-NP case matches Dutch data
    - `ccg_produces_crossSerial_3`: 3-NP case matches Dutch data
    - `ccg_is_mildly_context_sensitive`: CCG > CFG
    - `ccg_handles_both_patterns`: CCG handles Dutch AND German

### Key Insight
CCG's generalized composition allows arguments to be "threaded through" multiple verbs, naturally producing cross-serial dependencies. This is the "right" level of power for natural language: more than CFG (handles Dutch), less than full CSG (polynomial parsing).

### References
- Steedman (2000) "The Syntactic Process" Chapter 6
- Bresnan et al. (1982) "Cross-serial dependencies in Dutch"
- Shieber (1985) "Evidence against the context-freeness of natural language"

## [0.6.0] - 2025-01-24

### Added
- **Core/InformationStructure.lean**: Abstract interface for Information Structure
  - `Alternatives`: Focus semantic values (actual + alternatives, Rooth-style)
  - `QUD`: Question Under Discussion as partition of context set
  - `Theme`/`Rheme`: Topic-comment partition
  - `Focus`/`Background`: Contrast structure
  - `InfoStructure`: Complete IS analysis
  - Typeclasses: `HasInfoStructure`, `HasAlternatives`, `QUDSemantics`

- **Theories/CCG/Intonation.lean**: CCG implementation of Information Structure (Steedman 2000 Ch. 5)
  - `PitchAccent`: H* (rheme), L+H* (theme), null (background)
  - `BoundaryTone`: L, LH% (continuation), LL% (finality)
  - `InfoFeature`: θ (theme), ρ (rheme), φ (unmarked)
  - `ProsodicCat`: CCG categories with INFORMATION feature
  - Prosodic combination rules with feature unification
  - Implements `HasInfoStructure` typeclass

- **Core/Interfaces/ScopeTheory.lean**: Abstract interface for scope availability (Steedman 2000 Ch. 6)
  - `ScopeReading`: Ordering of scope-taking elements
  - `AvailableScopes`: Set of available readings for a form
  - `ScopePreference`: Ranked preferences (connects to RSA)
  - Typeclasses: `HasAvailableScopes`, `HasScopePreference`, `HasBinaryScope`

- **Theories/Montague/Scope.lean**: Implements `HasAvailableScopes` interface
  - `ScopedForm`: Form with available scopes (no world semantics)
  - `ScopeConfig.toScopeReading`: Convert binary scope to abstract reading
  - `MontagueScopeTheory`: Marker type for instance

- **Theories/RSA/ScontrasPearl2021.lean**: Separated world-parametric meaning
  - `WorldMeaning`: Truth conditions parameterized by (Interp, World)
  - Clean separation: grammar determines scope, RSA handles worlds

- **Theories/CCG/Scope.lean**: CCG implementation of scope availability
  - `DerivationType`: directApp, typeRaised, composed
  - `analyzeDerivation`: Classify derivation by structure
  - `ScopedDerivation`: Derivation annotated with scope-takers
  - `CCGScopeTheory`: Implements `HasAvailableScopes`
  - Key insight: Derivational structure determines scope possibilities

- **Phenomena/ScopeWordOrder/Data.lean**: Dutch/German scope-word order interactions
  - `VerbOrder`: verbRaising vs verbProjectionRaising
  - German examples (Bayer 1990, 1996; Kayne 1998)
  - West Flemish examples (Haegeman & van Riemsdijk 1986)
  - Dutch examples (Steedman 2000 §6.8)
  - Theorems proving word order predicts scope availability

### Architecture
- Information Structure connects to Scope via QUD:
  - QUD influences scope preferences
  - `QUDSemantics.informativity` provides what RSA needs for scope disambiguation
- Two-level design: Core interface + theory implementations
  - `ScopeTheory` (abstract) ← `Montague.Scope` (implements interface)
  - `InformationStructure` (abstract) ← `CCG.Intonation` (implements interface)

### References
- Steedman (2000) "The Syntactic Process" Chapters 5-6
- Rooth (1992) "A theory of focus interpretation"
- Roberts (1996/2012) "Information structure in discourse"

## [0.5.2] - 2025-01-24

### Added
- **CCG/Semantics.lean**: Compositional interpretation for CCG derivations
  - `DerivStep.interp`: Recursively computes meanings from derivations
  - `SemLexicon`: Maps words to semantic interpretations
  - `Interp`: Category paired with its meaning (sigma type)

- **CCG/TruthConditions.lean**: CCG → Montague → Empirical data pipeline
  - Derivations for test sentences (john_sleeps, mary_sleeps, etc.)
  - `ccgTruth`: Extract truth value from CCG derivation
  - `ccg_predicts_all_cases`: Universal theorem proving CCG predicts all test cases correctly

### Key Theorems
- `ccg_predicts_all_intransitive`: CCG correct on all 4 intransitive tests
- `ccg_predicts_all_transitive`: CCG correct on all 2 transitive tests
- `ccg_predicts_all_cases`: CCG correct on entire test suite

### Architecture
- Second complete pipeline (after Scontras & Pearl 2021)
- Demonstrates syntax → semantics → empirical data connection
- CCG categories map to Montague types via `catToTy`

## [0.5.1] - 2025-01-24

### Added
- **First complete pipeline analysis**: `complete_analysis_scontras_pearl` theorem
  - Proves RSA predictions match empirical data from Scontras & Pearl 2021
  - Demonstrates full semantics → pragmatics → data pipeline

### Changed
- **Renamed** `Theories/RSA/ScopeAmbiguity.lean` → `Theories/RSA/ScontrasPearl2021.lean`
  - Creates clear correspondence: `Phenomena/X/Data.lean` ↔ `Theories/Y/X.lean`
- **Moved** `everyHorseDidntJump_parametric` from Montague/Scope to RSA/ScontrasPearl2021
  - Keeps phenomenon-specific derivations with their proofs
  - Montague/Scope now contains only general infrastructure

## [0.5.0] - 2025-01-24

### Added
- **Core/Pipeline.lean**: Dependency-based theory composition architecture
  - `TheoryComponent`: declares what a theory provides and requires
  - `GroundedTheory`: components where all requirements are satisfied
  - `CompleteAnalysis`: grounded theory + predictions match empirical data
  - Key insight: no fixed syntax→semantics→pragmatics levels; just require dependency graph bottoms out

- **Core/RSA.lean**: `ParametricSemanticBackend` for lifted-variable RSA
  - Meaning function parameterized by interpretation (e.g., scope reading)
  - `L1_joint_scores`, `L1_world_scores`, `L1_interp_scores` for joint inference

- **Theories/Montague/Scope.lean**: Scope ambiguity infrastructure
  - `ScopeConfig`, `QNScope`: scope reading enumeration
  - `WorldParametricScopeDerivation`: meaning parameterized by scope AND world
  - `everyHorseDidntJump_parametric`: compositional truth conditions

- **Theories/RSA/ScopeAmbiguity.lean**: RSA model grounded in Montague
  - `meaningFromDerivation`: RSA meaning derived from Montague, not stipulated
  - `rsa_meaning_from_montague`: theorem proving connection
  - `rsa_prefers_inverse_scope`, `rsa_partial_world_possible`: key predictions

- **Phenomena/ScontrasPearl2021/Data.lean**: Empirical data (Scontras & Pearl 2021)
  - `JumpOutcome`, `ScopeReading`, `scopeTruth`
  - Experiment 1 results: 92%, 59%, 18% for 0/1/2 horses jumped

- **Core/Interfaces/ImplicatureTheory.lean**: Interface for comparing implicature theories
- **Theories/Comparisons/Implicature.lean**: NeoGricean vs RSA comparison

### Architecture
- RSA meaning functions should be **derived from compositional semantics**, not stipulated
- Pipeline ensures pragmatic predictions are grounded (no floating stipulations)
- Theories can cross traditional levels (CCG couples syntax-semantics, etc.)

## [0.4.6] - 2025-01-24

### Added
- **Core/Interfaces/CoreferenceTheory.lean**: Theory-neutral interface for coreference predictions (Mathlib pattern)

### Key Design
- `CoreferenceTheory` typeclass: what it means to be a theory that makes coreference predictions
- Theory-neutral: interface captures predictions, not mechanisms (c-command, o-command, etc.)
- `CoreferenceStatus`: obligatory, possible, blocked, unspecified
- Comparison functions: `theoriesAgreeOn`, `theoriesAgreeOnAll`, `theoriesAgreeOnPhenomenon`

### Interface Implementations
- **Minimalism.Coreference**: `instance : CoreferenceTheory MinimalismTheory`
- **HPSG.Coreference**: `instance : CoreferenceTheory HPSGTheory`
- **DepGrammar.Coreference**: `instance : CoreferenceTheory DepGrammarTheory`

### Key Theorems (using interface)
- `all_theories_pairwise_equivalent`: All three theories agree on test sentences
- `interface_all_agree_on_reflexive_data`: Agreement on phenomenon dataset

### Architecture Pattern (Mathlib-style)
- Define abstract interface in Core/Interfaces/
- Theories implement interface in their own terms
- Comparisons use interface for uniform testing
- Same pattern can extend to implicature, presupposition, etc.

## [0.4.5] - 2025-01-24

### Added
- **Theories/Comparisons/CommandRelations.lean**: Unified file formalizing Barker & Pullum (1990) "A Theory of Command Relations" + metatheorems about c-command ↔ o-command equivalence

### Key Formalizations (Barker & Pullum 1990)
- **Parameterized command relations**: C_P = {(a, b) | ∀x ∈ UB(a, P) → x ≥ b}
- **Upper bounds**: UB(a, P) = {x | x properly dominates a ∧ P(x)}
- **Intersection Theorem**: C_P ∩ C_Q = C_{P∪Q}
- **IDc-command is minimal**: Most restrictive command relation (bottom of lattice)
- **Specific relations as instances**: S-command, c-command, MAX-command

### Key Metatheorems
- `command_equivalence_subject_object`: C-command ↔ o-command on standard clauses
- `locality_correspondence`: Phase/LOCAL/path-length locality coincide
- `minimalist_hpsg_translation`: Minimalist and HPSG binding constraints extensionally equivalent

### Architecture
- Single unified file covering: algebraic framework → metatheorems → divergence examples
- Position-based c-command and GramFunction-based o-command
- Picture NP example showing where theories may diverge

## [0.4.4] - 2025-01-24

### Added
- **Theories/HPSG/Coreference.lean**: HPSG coreference via o-command (obliqueness hierarchy)
- **Theories/DependencyGrammar/Coreference.lean**: Dependency Grammar coreference via d-command
- **Theories/Comparisons/Coreference.lean**: Cross-theory comparison proving all three theories (Minimalism, HPSG, Dep Grammar) make identical predictions on coreference data

### Key Theorems
- `all_theories_capture_reflexive_coreference`: All 3 theories capture reflexiveCoreferenceData
- `all_theories_capture_complementary_distribution`: All 3 theories capture complementaryDistributionData
- `all_theories_capture_pronominal_disjoint_reference`: All 3 theories capture pronominalDisjointReferenceData
- `theories_equivalent_on_simple_transitives`: Pointwise equivalence on all minimal pairs

### Architecture
- Each theory imports PhenomenonData and proves it captures each MinimalPair
- Comparisons/ subfolder for cross-theory agreement proofs

## [0.4.3] - 2025-01-24

### Added
- **Phenomena/Coreference/Data.lean**: Theory-neutral coreference patterns (reflexive coreference, pronominal disjoint reference, referential expression freedom)
- **Phenomena/Islands/Data.lean**: Theory-neutral filler-gap dependency constraints (embedded question, complex NP, adjunct, coordinate structure, subject constraints)
- **Theories/Minimalism/XBar.lean**: X-Bar structure with `BarLevel` enum, `XBarPhrase`, specifier/complement extraction
- **Theories/Minimalism/Workspace.lean**: Derivational workspace (`Numeration`, `Workspace`, `select`, External/Internal Merge operations)
- **Theories/Minimalism/Agree.lean**: Activity Condition, `ActiveGoal`, `MultipleAgree`, Case Filter theorems, defective intervention

### Changed
- **Lexicon expanded**: Reflexive pronouns (himself, herself, themselves, myself, yourself, ourselves), temporal/causal words (before, after, because, although), coordination (and_, or_)
- **Theory-neutral terminology**: "Coreference patterns" instead of "Binding Theory"; "filler-gap constraints" instead of "extraction/movement"

### Design Decisions
- Phenomena files use framework-neutral descriptions compatible with CxG, HPSG, DG, and Generative approaches
- Minimalism infrastructure follows Adger (2003) Chapters 2-4

## [0.4.2] - 2025-01-24

### Changed
- Use λ instead of fun for lambda expressions throughout codebase

## [0.4.1] - 2025-01-24

### Changed
- **Renamed** `Phenomena/HeadMovement/` → `Phenomena/WordOrderAlternations/VerbPosition/` (theory-neutral naming)
- **Fixed** specifier-head labeling: in `{Spec, XP}` configurations, the phrase XP now correctly projects

### Fixed
- Labeling in specifier-head structures: previously defaulted to leaf; now correctly chooses phrase
- All `#eval` tests pass: V in Spec-CP yields C label, V doesn't project in specifier position

## [0.4.0] - 2025-01-24

### Added
- **Harizanov's Head Movement Theory** (first pass formalization)
- **Minimalism/SyntacticObjects.lean**: Lexical Items (simple & complex), LI tokens, Syntactic Objects, Merge
- **Minimalism/Containment.lean**: Immediate containment, transitive containment (dominance), c-command, sisters
- **Minimalism/Labeling.lean**: Labels, projection, maximality/minimality (relational properties), heads vs phrases
- **Minimalism/HeadMovement/Basic.lean**: Two movement types (head-to-spec, head-to-head), complex LI formation
- **Minimalism/Constraints/HMC.lean**: Head Movement Constraint, violations, Amalgamation distinction
- **Phenomena/WordOrderAlternations/VerbPosition/Data.lean**: Concrete phrase structures for testing
- **docs/MILESTONE_HEAD_MOVEMENT.md**: Detailed roadmap for full formalization

### Key Formalizations
- **Definition 10-11**: Lexical Items as ⟨CAT, SEL⟩ pairs; complex LIs for head-to-head movement
- **Definition 13-14**: Immediate containment and transitive containment (dominance)
- **Definition 16-22**: Labeling, projection, maximality/minimality, heads/phrases
- **Two movement types**: Head-to-specifier (mover becomes +max) vs head-to-head (mover stays +min)
- **HMC**: Both syntactic head movement types violate HMC (distinguishes from Amalgamation)

### Architecture
- Harizanov's definitions live in `Minimalism.Harizanov` namespace (separate from existing Minimalism)
- Core insight formalized: maximality is RELATIONAL, not intrinsic
- Phenomena use theory-neutral names (`WordOrderAlternations/VerbPosition/`)

## [0.3.0] - 2025-01-24

### Added
- **End-to-end scalar implicature pipeline**: CCG → Montague → NeoGricean/RSA
- **Montague/Lexicon.lean**: Lexical entries with semantic denotations and scale membership
- **Montague/SemDerivation.lean**: Syntax-agnostic interface for pragmatics (`SemDeriv.Derivation`)
- **CCG/Interpret.lean**: Converts CCG derivations to semantic derivations
- **RSA/ScalarImplicatures.lean**: RSA derivation of "some → not all"
- **PragmaticComparison.lean**: Agreement theorem proving NeoGricean and RSA derive same implicature
- **docs/ROADMAP.md**: Technical debt and future work tracking

### Changed
- Consolidated `ContextPolarity` (was duplicated in SemDeriv and Alternatives)
- Extended `NeoGricean/ScalarImplicatures.lean` with `deriveFromDerivation` consuming `SemDeriv.Derivation`

### Architecture
- Pragmatics imports from Montague's `SemDerivation`, not from specific syntax theories
- Any syntax theory (CCG, HPSG, Minimalism) can produce derivations for pragmatics

## [0.2.0] - 2025-01-24

### Added
- **Mathlib integration**: Use `Set` for predicate extensions with proper set lemmas (`Set.mem_setOf_eq`, `Set.mem_singleton_iff`)
- **Montague/Attitudes.lean**: Propositional attitudes (believe, know, want) with accessibility relations
- **Montague/Modality.lean**: Possible worlds semantics, necessity/possibility operators
- **Montague/Derivations.lean**: Proofs that Montague predicts correct truth conditions
- **Montague/SyntaxInterface.lean**: Documents what Montague requires from syntax vs is agnostic to
- **Montague/SemanticBackendInstance.lean**: Shows Montague implementing RSA's SemanticBackend interface
- **Phenomena/Semantics/TruthConditions.lean**: Theory-neutral empirical truth judgments
- **CCG/Semantics.lean**: Type preservation theorems, homomorphism principle (compositionality)
- **docs/MATHLIB_INTEGRATION.md**: Documents Mathlib usage and design decisions

### Changed
- Moved `Theories/Semantics/{Entailment,Numbers,Scales}.lean` under `Theories/Montague/`
- `Basic.lean` now uses Mathlib's `Set` for characteristic function correspondence
- Keep custom `FiniteModel` class (not Mathlib's `Fintype`) for `#eval` computability

### Design Decisions
- **Phenomena vs Theories**: Phenomena contain only empirical data; proofs stay in Theories
- **Horn Sets not Scales**: Following Geurts (2010), use sets where ordering is derivable from semantics
- **Sentence-level strength**: Alternatives are stronger sentences, not words (handles DE environments)

## [0.1.0] - 2025-01-23

### Added
- Core infrastructure: `Frac`, `Word`, basic types
- **Theories**: CCG, HPSG, Minimalism syntax; Montague semantics; NeoGricean pragmatics; RSA
- **Phenomena**: CCG coordination, Geurts (2010) quantity implicatures
- SemanticBackend interface connecting syntax to pragmatics
