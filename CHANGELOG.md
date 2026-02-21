# Changelog

## [0.224.97] - 2026-02-20

### Changed
- **Split `Core/Basic.lean` → `Core/Word.lean` + `Core/Grammar.lean`**: `Word.lean` (158 lines) has UD morphological aliases, `Valence`, `HeadDirection`, `Features`, `Word`; `Grammar.lean` (135 lines) has `ClauseType`, `Grammar` typeclass, `MinimalPair`, `PhenomenonData`, `SentencePair`, capture predicates, agreement theorems. 86 downstream imports updated
- **Move `ThetaRole` → `Theories/Semantics/Events/ThematicRoles.lean`**: Co-located with `ThematicFrame` and `ThetaRole.toRel` where it belongs
- **Move `WhSemanticType` → `Phenomena/Questions/Basic.lean`**: Moved to its sole consumer

### Removed
- **`Core/Basic.lean`**: Replaced by `Core/Word.lean` + `Core/Grammar.lean`
- **`GrammarWithParsing`**, `capturesStringPair`, `capturesStringPhenomenon`: Dead code (0 instantiations)

## [0.224.96] - 2026-02-20

### Added
- **`Core/Epistemicity.lean`**: Epistemic profile layer (Gawne & Spronck 2024 glossary integration). `EpistemicAuthority` (ego/allocutive/nonparticipant) fills the egophoricity gap; `EpistemicProfile` bundles evidential source, authority, and mirativity; `epistemicAuthority` bridges to `KContext`
- **`Comparisons/TenseModalEvidentiality.lean` §4**: Bridge theorems connecting `EpistemicProfile` to `Kernel` semantics — strong assertions (ego+direct) map to settling kernels, inferential claims (nonparticipant+inference) to `must`-defined kernels

## [0.224.95] - 2026-02-20

### Added
- **`Phenomena/Focus/Rooth1992Bridge.lean` §10–§15**: Full end-to-end derivational chain from Fragment entries through Montague composition to FIP. Adds `focusModel` (4-entity model), world-parameterized lexicon, `SynTree` derivations for "Fred ate beans"/"Mary ate beans"/"Fred ate rice", `interpTree` composition, `SemDeriv` bundles, grounding theorems (`comp_grounds_*`), Fragment connection (linking `Fragments.English.Nouns.fred`/`bean` and `Predicates.Verbal.eat` to the model), and `endToEnd_question_grounded` proving compositionally-derived question = hand-defined question
- **`Fragments/English/Nouns.lean`**: Add `fred` (proper name) and `bean` (count noun, irregular plural "beans") to English noun lexicon

## [0.224.94] - 2026-02-20

### Added
- **`Phenomena/Focus/Rooth1992Bridge.lean`**: Bridge file connecting `Focus/Basic.lean` data to `Focus/Interpretation.lean` theory. Exercises 7 previously unexercised `Core.InformationStructure` definitions in Phenomena: `AltMeaning.unfeatured`, `Focus`, `Background`, `Theme`, `Rheme`, `InfoStructure`, `HasInfoStructure`. Q-A congruence model (4 worlds) proves FIP holds for subject focus and fails for object focus; "only" association model (3 worlds) proves focus determines exclusion domain

## [0.224.93] - 2026-02-20

### Added
- **`Phenomena/Reference/Studies/QingFranke2015.lean`**: Full RSA implementation of Qing & Franke (2015) "Variations on a Bayesian Theme". Formalizes the 3-dimensional decomposition of Bayesian reference games (belief × goal × listener action): 4 speaker models (σ_bU, σ_aU, σ_bS, σ_aS), action-oriented listener (ρ_a via softmax ∘ L1), and 6 qualitative findings all proved via `rsa_predict` — including the salience reversal result where uniform and salience priors make opposite L1 predictions

### Removed
- **`Theories/Pragmatics/RSA/Implementations/QingFranke2013.lean`**: Replaced by `Phenomena/Reference/Studies/QingFranke2015.lean` (correct directory per dependency discipline; all 5 `sorry` theorems now proved; uses concrete parameters for `rsa_predict`)

## [0.224.92] - 2026-02-20

### Changed
- **Move K&S-specific machinery from `Core/InformationStructure.lean` to `Theories/Semantics/Focus/KratzerSelkirk2020.lean`**: `ISFeature`, `isNew`, `applyFoC`, `foc_preserves_oValue`, `isGiven`, `applyG`, `g_preserves_oValue`, `g_preserves_aValue`, `foc_g_exclusion` — all K&S §8 theory. `DiscourseStatus` stays in Core (used broadly as a descriptive type by Arnold et al. 2000, BackgroundedIslands, BiasedPQ)

## [0.224.91] - 2026-02-20

### Removed
- **Delete `Core/Alternatives.lean`**: Merge live definitions into `Core/InformationStructure.lean`; delete dead code (`Alternatives α` struct, `Alternatives.singleton`, `Alternatives.mk'`, `HasAlternatives` — all unused outside the file). Eliminates naming conflict with `NeoGricean/Core/Alternatives.lean`

### Changed
- **`Core/InformationStructure.lean`**: Absorbs `AltMeaning`, `AltMeaning.unfeatured`, `CatItem`, `categoryMatchAlts`, `typeTheoAlts` from deleted `Core/Alternatives.lean`. `Focus.alternatives` field simplified from `Alternatives α` to `List α`
- Updated imports in `Focus/Interpretation.lean`, `Focus/KratzerSelkirk2020.lean`, `Fragments/Turkish/QuestionParticles.lean`, `Phenomena/Questions/Studies/TurkHirschInce2026Bridge.lean`
- Deleted dead `FocusValue` alias from `Focus/Interpretation.lean` (0 downstream uses)

## [0.224.90] - 2026-02-20

### Changed
- **`PointPred` → `Situation W Time → Prop`**: Make situation structure explicit in the tense-aspect pipeline. `PointPred W Time` was `W → Time → Prop` (threading world and time separately); now `Situation W Time → Prop`, closing the gap between aspect operators and situation semantics (Elbourne, Percus, Kratzer)
- **`WorldHistory` → `Situation W Time → Set W`**: Same principle applied to branching-time modal bases — `WorldHistory` was `W → Time → Set W`, now takes a `Situation` directly
- **`PointPred.toSitProp`**: Now the identity (retained as `abbrev` for backward compatibility) since `PointPred` already is `Situation → Prop`
- Updated `PERF`, `PERF_XN`, `PERF_ADV`, `PERF_open`, `IntervalPred.atPoint`, `evalPres`, `evalPast`, `evalFut`, `historicalBase`, `WorldHistory.reflexive`, `WorldHistory.backwardsClosed` to use situation-threaded signatures
- All downstream theorems updated: K&S Theorems 3–7, monotonicity, unfold lemmas, pipeline bridges, mood proof

## [0.224.89] - 2026-02-20

### Removed
- **Delete 10 RSA/Core stub files**: `Basic.lean`, `BasicQ.lean`, `ChainComparison.lean`, `Discourse.lean`, `DiscourseIntegration.lean`, `Distribution.lean`, `DistributionPMF.lean`, `Eval.lean`, `Intensional.lean`, `RationalPower.lean` — 5-14 line docstring-only files left over from the old ℚ-based RSAScenario API, replaced by `RSAConfig`

### Fixed
- **Broken imports in `Linglib.lean`**: `PracticalReasoning` → `PracticalReasoningBridge`, `InformationalBackgrounds` → `InformationalBackgroundsBridge` (files were renamed during an earlier migration but imports weren't updated)

## [0.224.88] - 2026-02-20

### Added
- **Kratzer (1998) deep integration**: Enrich `Theories/Semantics/Tense/Kratzer.lean` from ~130 lines (SOT deletion only) to ~330 lines covering all four contributions: aspect decomposition (English simple past = PRESENT + PERFECT), zero forms & locality, reflexive ↔ simultaneous parallel, cross-linguistic predictions
- **Core/Tense.lean**: `Overtness` type and `fromBinding` function — bound + local → zero, free → overt; unifies zero tense, reflexive reduction, and pro-drop under one mechanism
- **`KratzerDecomposition`** structure linking surface morphology to underlying tense head + aspect; `canBeDeictic`, `tenseOvertness` derived methods
- **Fragments/German/Tense.lean**: New file — Preterit (anaphoric PAST) and Perfekt (indexical PRESENT + PERF) decomposition entries with contrast theorems
- **Fragments/English/Tense.lean**: `kratzerSimplePast`, `kratzerPresentPerfect` decomposition entries; `lakoff_kratzer_diverge` theorem (surface past ≠ underlying present)
- **Phenomena/TenseAspect/Data.lean**: `TenseDeicticDatum` structure + cross-linguistic deictic data (English simple past, German Preterit, German Perfekt); `deictic_tracks_indexical` theorem
- **Phenomena/TenseAspect/Bridge.lean**: Full derivational chain theorems (`kratzer_english_chain`, `kratzer_german_preterit_chain`, `kratzer_german_perfekt_chain`, `kratzer_zero_tense_chain`) — each connects Fragment → Theory → Pipeline → Reichenbach → Data so changes at any layer break the theorem
- **Comparisons/Partee1973.lean**: § 8 zero forms (Kratzer 1998) — `overtness_classification`, `zero_tense_parallels_reflexive`, `two_coarsenings` proving Elbourne's {free,bound} and Kratzer's {overt,zero} are two natural coarsenings of Partee's three-way classification

## [0.224.87] - 2026-02-20

### Removed
- **Delete `Theories/Pragmatics/RSA/Domains/`**: Remove entire directory (5 files). `QUD.lean`, `LexicalAmbiguity.lean`, `Scope.lean` were dead code (only imported by `Linglib.lean`). `Degrees.lean` was nominally imported by `TesslerFranke2020` and `Evaluativity` but neither used any of its definitions — they relied on it only for transitive imports they already had. `Quantities.lean` (the only genuinely-used file) relocated to `Theories/Pragmatics/RSA/Quantities.lean`

## [0.224.86] - 2026-02-20

### Added
- **Kao, Levy & Goodman (2015) Irony**: Full RSA implementation in `Phenomena/Nonliteral/Irony/KaoEtAl2015.lean` — 3 weather states × 2 valence × 2 arousal = 12 world states, rpow-based QUD-projected S1 with α=1, fitted QUD prior [3,3,4] + valence-only ablation [1,1,0], all 6 qualitative findings proved via `rsa_predict`. Core finding: `no_irony_without_arousal` proves that removing the arousal QUD eliminates the valence flip that defines irony, leaving only hyperbole — the paper's central mechanistic claim

## [0.224.85] - 2026-02-20

### Added
- **Theories/Sociolinguistics/PropertySpace.lean**: Burnett (2019) Defs. 3.1–3.3 — `PropertySpace` (incompatibility relation), `Persona` (maximal consistent subset), `BipolarDimension`, `allPersonaeSets` enumeration
- **Theories/Sociolinguistics/SCM.lean**: Stereotype Content Model — `SCMProperty` (6 poles), `SocialDimension` (3 axes, moved from Core), `scmSpace`, `scm_persona_count` (= 8 via `native_decide`)
- **Theories/Sociolinguistics/EckertMontague.lean**: Burnett Def. 3.4 — `GroundedField`, `emField` (Eckert-Montague lift), `emField_antitone`, `fromIndexicalField` bridge from sign-valued `IndexicalField` to SCM grounded field
- **Theories/Sociolinguistics/SMG.lean**: Burnett Defs. 4.1–4.4 — `SocialMeaningGame`, `toInterpGame` (bridge to Franke IBR), `naiveListener` + `naiveListener_eq_L0` (grounding by `rfl`), `strategicSpeaker`, `uncoveringListener`

### Changed
- **Core/SocialMeaning.lean**: Move `SocialDimension` to `Theories/Sociolinguistics/SCM.lean` (theory-specific, not framework-agnostic)
- **BSB2022.lean, BeltramaSchwarz2024.lean**: Add `import Linglib.Theories.Sociolinguistics.SCM` + `open Sociolinguistics.SCM` for `SocialDimension`

## [0.224.84] - 2026-02-20

### Changed
- **Elbourne.lean refactoring**: Remove Theories→Fragments dependency violation (was importing `Fragments.English.Determiners` and `Fragments.English.Pronouns`); delete tautological theorems (`familiarity_is_restricted_situation`, `refAttr_not_ambiguity`, `situationToUseMode`); move empirical data (`hansGhost`, `ponceFountain`, pronoun examples) and Fragment bridge theorems to Phenomena file; implement `pronoun_is_definite_article` properly via `pronounDenot` (was `True` placeholder); add `@cite{elbourne-2013}` tag
- **Core/Situation.lean**: Strip 7 unused wrappers (`τ`, `w`, `mk'`, `sameWorld`, `sameTime`, `before`, `after`, `contemporaneous`) — all dead code, field accessors `.world`/`.time` used directly everywhere

### Added
- **Elbourne.lean**: `the_sit_presup_depends_on_filter` (presupposition determined by filter result), `the_sit_assertion_implies_presup` (Frege/Strawson: assertion entails presupposition), `pronounDenot` + `pronoun_is_definite_article` (⟦it⟧ = ⟦the⟧), `pronoun_assertion_implies_presup`
- **Elbourne2013.lean**: Phenomena file for Elbourne (2013) with 6 concrete examples exercising `the_sit'`, `SituationFrame`, `isMinimal`, `SitVarStatus`, `DonkeyConfig`, `pronounDenot`, plus Fragment bridges and moved empirical data

## [0.224.83] - 2026-02-20

### Added
- **Kao, Bergen & Goodman (2014) Metaphor**: Full RSA implementation in `Phenomena/Nonliteral/Metaphor/KaoEtAl2014.lean` — 2 categories × 8 feature combos = 16 world states, rpow-based QUD-projected S1 scoring, parametric goal prior (vague + specific), all 6 qualitative findings proved via `rsa_predict` including cross-config context sensitivity
- **`rsa_predict` cross-config support**: Generalize `L1_sum_gt_of_precomputed` bridge axiom from single config to `(cfg₁ cfg₂ : RSAConfig U W)`; new `GoalForm.l1CrossConfig` case with two `reifyS1Scores` calls and normalized policy comparison; single-world cross-config routed through sum path via singleton arrays

### Removed
- `Theories/Pragmatics/RSA/Implementations/KaoEtAl2014_Metaphor.lean` (old stub, replaced by consolidated file)
- `Phenomena/Nonliteral/Metaphor/Studies/KaoBergenGoodman2014.lean` (old data file, replaced by consolidated file)

## [0.224.82] - 2026-02-20

### Added
- **Beltrama, Solt & Burnett (2022) formalization**: `BeltramaSoltBurnett2022.lean` — three-way variant type (precise/underspecified/approximate), cell means from both experiments (N=72, N=400), core indexical orderings proved from data, underspecified-as-diagnostic theorems (dimension-dependent clustering + crossover), context modulation (high-demand amplifies competence, low-demand amplifies warmth), roundness gating for variant collapse
- **Fragment→Variant derivation chain**: `classifyVariant` composes `Core.Roundness.roundnessScore` with `NumeralModifiers.about.modType` to classify stimuli end-to-end; bridge theorems verify 49→precise, bare 50→underspecified, "about 50"→approximate
- **`about` numeral modifier**: `Fragments.English.NumeralModifiers.about` (tolerance modifier, peakedSignal) — the most common English approximator, used in BSB2022 stimuli
- **`SocialDimension.antiSolidarity`**: third constructor in `Core.SocialMeaning.SocialDimension` (pedantic, uptight); BSB2022's PCA Factor 3; B&S 2024 `precisionField` extended with `.antiSolidarity` cases

## [0.224.81] - 2026-02-20

### Changed
- **Beltrama & Schwarz (2024) cleanup**: Merge `Data.lean` + `Bridge.lean` into single `BeltramaSchwarz2024.lean` (follows GS2013 single-file pattern); remove 8 fluff theorems (definition read-backs); fix hallucinated "Beltrama 2018" reference → Beltrama, Solt & Burnett (2022); move `personaDimension` from data section to bridge section (theoretical interpretation, not raw data)

## [0.224.80] - 2026-02-20

### Changed
- **Kao et al. (2014) Hyperbole consolidation**: Merge three files (Theories implementation + Phenomena data + Phenomena bridge) into single `Phenomena/Nonliteral/Hyperbole/KaoEtAl2014.lean`; delete `Theories/Pragmatics/RSA/Implementations/KaoEtAl2014_Hyperbole.lean` and `Studies/KaoEtAl2014.lean`; all 6 `rsa_predict` proofs preserved

## [0.224.79] - 2026-02-20

### Added
- **FG2012 parameterized context types**: `ContextSpec` (4-boolean distractor overlap), `mkRefGame` constructor, all 7 FG2012 context types (1/1, 1/2, 1/3, 2/2a, 2/2b, 2/3, 3/3) with `Obj3`/`Dim2Feature` types; 9 L1 predictions proved via `rsa_predict` covering pragmatic narrowing (2/2b), symmetric non-narrowing (1/2), uniform informativity (1/3), and featural indistinguishability (2/2a, 2/3, 3/3)

## [0.224.78] - 2026-02-20

### Added
- **Percus (2000) situation variable constraints**: `Theories/Semantics/Intensional/Situations/Percus.lean` — `SituationAssignment` (specializes `VarAssignment` to `Situation W Time`), `interpSitVar`, `updateSitVar`, `sitLambdaAbs`, `believeSit` (attitude verb with situation binding), `alwaysAt` (adverbial quantifier with situation binding), `PredicateBinding`, `genXWellFormed` (Generalization X), `genYWellFormed` (Generalization Y for adverbial quantifiers), `genXYWellFormed` (combined)
- **Percus (2000) empirical predictions**: `Phenomena/Reference/Studies/Percus2000.lean` — end-to-end Fragment→Theory→Phenomena chain; Fragment bridge derives situation-binder introduction from `VerbEntry.opaqueContext` and quantification type from `attitudeBuilder`; per-entry verification theorems for `believe`, `think`, `always`, proper/common nouns; three examples with `rfl` proofs: Ex 1 ("Mary believes John is Canadian") Gen X blocks de re predicate; Ex 2 ("Mary believes my brother is a spy") Gen X allows NP-de-re but blocks pred-de-re; Ex 3 ("Mary thinks my brother always won the game") Gen Y has independent bite — Gen X satisfied by both readings, Gen Y alone distinguishes them
- **Adverbial quantifiers in Fragment lexicon**: `Fragments/English/FunctionWords.lean` — `AdvQuantForce` enum (universal/existential/proportional/negative), `AdvQuantEntry` structure, entries for `always`, `usually`, `sometimes`, `never`
- **Fragment noun additions**: `Fragments/English/Nouns.lean` — `brother`, `spy` entries

## [0.224.77] - 2026-02-20

### Added
- **Kennedy exact semantics in GS2013**: `KennedyInterp` (exact vs type-lowered), `KennedyUtt` (bare/moreThan/atLeast), `gsCfgK` RSA config with `Latent = Obs × KennedyInterp`; 8 Kennedy theorems (findings 4–11) proved via `rsa_predict`; `kennedy_numeral_findings_verified` omnibus theorem showing both lower-bound and Kennedy exact semantics account for all numeral data

### Changed
- **Merge `UtteranceContext` into `Context`**: `KContext.toReichenbachFrame` replaces standalone `UtteranceContext`; deleted `Core/UtteranceContext.lean`
- **Extract `Core/Situation.lean`**: `Situation` (World × Time) moved from `Core/Time.lean` to its own root file (`Core.Situation`); `Core/Time.lean` imports and re-exports it; 4 downstream `open` statements updated

## [0.224.76] - 2026-02-20

### Changed
- **Truthmaker refactor**: `bilAnd`/`bilOr` now defined in terms of `tmAnd`/`tmOr` (duality explicit: conjunction fuses verifiers + unions falsifiers, disjunction vice versa; De Morgan laws still `rfl`); removed redundant coherence section (§10); dropped `subjectMatterFinite`
- **Monotonicity refactor**: Removed per-verb signature defs (`believeSig`, `knowSig`, etc.) that duplicated fragment data; per-verb classifications live solely on `VerbCore.complementSig`; `#guard` checks now test `EntailmentSig` values directly

## [0.224.75] - 2026-02-20

### Added
- **TAME unification infrastructure**: Shared types for tense, aspect, mood, evidentiality, and mirativity
  - `Core/Context.lean`: `KContext.toReichenbachFrame` projection — speech time S = context time, P = S root-clause default; `KContext` is the unified root, `ReichenbachFrame` is the per-clause temporal projection
  - `Core/Evidence.lean`: `MirativityValue` enum (expected/unexpected/neutral) with `isMirative` predicate (DeLancey 1997, Aikhenvald 2004)
  - `Phenomena/TenseAspect/Typology.lean`: WALS Ch 78 `EvidentialityCoding` enum, `TAMEProfile` structure bundling all TAME parameters, 5 sample language profiles (Turkish, Quechua, Korean, English, Mandarin), Generalization 11 (evidentiality co-occurs with tense/aspect marking)

### Changed
- **Rename `TenseEvidentialParadigm` → `TAMEEntry`** in `Theories/Semantics/Tense/Evidential.lean`: Added optional `mood : Option GramMood` and `mirative : Option MirativityValue` fields (both defaulting to `none`). Updated all downstream references in `Fragments/English/Tense.lean`, `Fragments/Korean/Evidentials.lean`, `Fragments/Bulgarian/Evidentials.lean`, `Phenomena/TenseAspect/Studies/Cumming2026/Bridge.lean`

## [0.224.74] - 2026-02-20

### Added
- **Bilateral truthmaker semantics** (Fine 2017 §§5–6) in `Truthmaker/Basic.lean`: `BilProp` (verifier + falsifier pairs), `bilNot` (swap), `bilAnd`/`bilOr` with verification/falsification duality (fusion ↔ union), De Morgan laws (`rfl`), modalized state space (`Possibility` with downward closure), Exclusivity/Exhaustivity, `exclusive_bilAnd` propagation, subject-matter (`sSup` of verifiers)

## [0.224.73] - 2026-02-20

### Changed
- **Merge Tense/ + Aspect/ → TenseAspect/**: Unified `Phenomena/Tense/` (10 files) and `Phenomena/Aspect/` (5 files) into `Phenomena/TenseAspect/` (15 files). Motivated by Typology.lean's Generalization 3: no tense-vs-aspect typological divide. Added 3 previously missing imports to `Linglib.lean` (Typology, AgentivityBridge, Studies.AlstottAravind2026).

### Fixed
- **StankovaSimik2024 build error**: Fix `open Phenomena.Negation.CzechThreeWayNeg` → `CzechThreeWayNegTypologyBridge` (wrong namespace in both Data.lean and parent .lean)

## [0.224.72] - 2026-02-20

### Added
- **Bondarenko & Elliott (2026) monotonicity via mereology**: Truthmaker semantics + attitude verb monotonicity classification
  - `Theories/Semantics/Truthmaker/Basic.lean`: State-based propositions grounded in `Core/Mereology.lean`; conjunction via fusion, content parthood, `mono_att_distrib_and` (conjunction distribution from `le_sup_left`/`le_sup_right` — no sorry)
  - `Theories/Semantics/Attitudes/Monotonicity.lean`: Attitude complement positions classified by `EntailmentSig`; neg-raising derived from monotonicity + EMP; bridge theorems showing agreement with veridicality-based derivation in `NegRaising.lean`
  - `Phenomena/Complementation/Attitudes/ConjunctionDistribution/Data.lean`: Empirical data for 8 verbs (6 distributing, 2 non-distributing)
  - `VerbCore.complementSig : Option EntailmentSig` field with derived `distribOverConj`/`isComplementUE`; populated for 10 attitude verbs in English fragment
- **Bibliography**: `bondarenko-elliott-2026`, `fine-2017` added to `references.bib`

## [0.224.71] - 2026-02-20

### Added
- **Aissen (2003) DOM hierarchy** in `Case/Typology.lean` (818→1210 lines): Formalize two prominence scales (animacy: Human > Animate > Inanimate; definiteness: Pronoun > Proper Name > Definite > Indefinite Specific > Non-specific), bidimensional DOM grid, 8 language profiles (Spanish, Russian, Turkish, Hebrew, Persian, Catalan, Hindi, No-DOM), and the DOM monotonicity universal verified by `native_decide`

## [0.224.70] - 2026-02-20

### Added
- **Tier 3 WALS typology files**: Complete WALS coverage for remaining gaps
  - `Alignment/Typology.lean` (818 lines, 20 languages): WALS Ch 98--100 — NP/pronoun case alignment, verbal person marking; Dixon's split-ergative hierarchy
  - `FillerGap/Typology.lean` (943 lines, 19 languages): WALS Ch 122--123 — relativization strategies, Keenan-Comrie accessibility hierarchy
  - `Numerals/Typology.lean` (816 lines, 19 languages): WALS Ch 53--56 — classifiers, ordinals, distributive numerals; Sanches-Slobin generalization, Greenberg suppletion hierarchy
  - `Morphology/Typology.lean` extended (178→1109 lines, 18 languages): WALS Ch 20--27 — fusion, exponence, locus of marking, prefix/suffix, reduplication; Greenberg Universal 27
  - `Complementation/Typology.lean` extended (~700→1614 lines, 20 languages): WALS Ch 94--95 — subordination strategies, complementizer position, head-direction harmony
- **12 new verified universals** across 5 files (see typology-roadmap.md)

## [0.224.69] - 2026-02-20

### Fixed
- **`extractRat` fraction bug**: Fix `extractRat` dropping denominators from ℝ fractions like `2/3 : ℝ` — after `whnf`, these reduce to internal `Real.mul`/`Real.inv` forms (not `Real.ofCauchy`), causing `findEmbeddedNat` to return only the numerator
  - Add `extractRatFromCauchy`: evaluates Cauchy sequences at index 0 to extract exact ℚ
  - Add `extractIntExpr`: extracts ℤ from `Int.ofNat`/`Int.negSucc` constructor forms
  - Guard `findEmbeddedNat` to only run for `Real.ofCauchy` heads (not internal ops)
  - Add unary `Inv.inv`/`Neg.neg` isDefEq fallbacks in `extractRat` step 5
  - Add `Inv.inv` handling to `matchArithOp`
- **Interval precision for exact values**: Skip `roundBounds` for point intervals (`lo == hi`), preventing unnecessary widening of exact ℚ values through binary rounding
- **S1 policy normalization**: Return exact `[1, 1]` in `metaQINormalize` when target is the only non-zero S1 score, preventing interval widening from `a/a` division

### Changed
- **Rewrite GS2013 implementation**: Replace 631-line hand-rolled evaluator with ~220-line `RSAConfig` formalization using compositional `s1Score = exp(α · E_belief[log L0(s|u)])` and explicit quality filter; eliminate all ℚ-duplicate definitions (`affectPrior_q`, `L0_policy_q`, `S1_score_qi`, etc.)
- **Rewrite GS2013 bridge**: All 11 empirical findings from Goodman & Stuhlmuller (2013) now proved via `rsa_predict` — 5 positive (`>`) and 6 negation (`¬(>)`) theorems, plus `all_findings_verified` summary theorem

## [0.224.64] - 2026-02-20

### Changed
- **Phenomena naming normalization**: 10 renames enforcing the `Typology.lean`/`TypologyBridge.lean` and `*Bridge.lean` conventions
  - Typology: `PersonMarkingTypology` → `Agreement/Typology`, `PronounTypology` → `Anaphora/Typology`, `ChangeOfStateTypology` → `Causatives/Studies/BeaversEtAl2021`
  - Bridge suffix: `CzechThreeWayNeg` → `CzechThreeWayNegBridge`, `Composition` → `CompositionBridge`, `DegreeComposition` → `DegreeCompositionBridge`, `ActualityInferences` → `ActualityInferencesBridge`, `Evaluativity` → `EvaluativityBridge`
  - Move to Studies/: `Modality/Aloni2022` → `Modality/Studies/Aloni2022Bridge`
  - Split: `Questions/Typology.lean` → data-only `Typology.lean` + theory-importing `TypologyBridge.lean`
- All namespaces, imports, and `open` statements updated across 16 files

## [0.224.62] - 2026-02-20

### Changed
- **Close `logPoint_containsReal` axiom** (LogInterval.lean): Full proof via bisection invariant `exp(lo) ≤ q ≤ exp(hi)` + monotonicity of log; 4 helper lemmas (`nat_le_exp`, `logBisectCore_sound`, `initial_lower_bound`, `initial_upper_bound`)
- All 3 core interval axioms (`mul_containsReal`, `expPoint_containsReal`, `logPoint_containsReal`) now have full proofs; only `pade_error_bound` and `reductionSteps_spec` k>0 remain as `sorry`

## [0.224.61] - 2026-02-20

### Changed
- **Close 2 interval axioms**: Replace `axiom mul_containsReal` (QInterval.lean) and `axiom expPoint_containsReal` (PadeExp.lean) with full theorem proofs; `pade_error_bound` converted from axiom to `sorry`-ed theorem with proof sketch
- **mul_containsReal**: 4-corner method via sign case analysis with `mul_le_mul_of_nonneg/nonpos_left/right`
- **expPoint_containsReal**: Padé containment + argument reduction + repeated squaring; 7 helper lemmas (`padeDen_pos`, `abs_le_one_of_natAbs_le_den`, `reductionSteps_spec`, `repeatedSq_containsReal`, `exp_pow_reduction`, `exp_le_three_pow`, `rat_le_natAbs_num`)
- **RSA Config**: Make `latentPrior` world-dependent (`W → Latent → ℝ`), supporting models where latent variable distribution depends on world state (e.g., observation probability in Goodman & Stuhlmuller 2013)
- **rsa_predict tactic**: Extend to handle world-dependent latent priors

## [0.224.60] - 2026-02-20

### Added
- **Typology Tier 1**: Five new WALS-based cross-linguistic typology files covering 20 chapters and ~86 languages:
  - `Tense/Typology.lean` (Ch 65–69): aspect marking, past/future/perfect tense, affix position; 19 languages, 11 verified generalizations
  - `Negation/Typology.lean` (Ch 112–115): negative morpheme types, symmetric/asymmetric negation, negative indefinite strategies; 17 languages, 10 theorems
  - `Plurals/Typology.lean` (Ch 33–36): plural coding, occurrence, pronoun plurality, associative plurals, animacy hierarchy; 16 languages, 14 theorems
  - `Reference/Typology.lean` (Ch 37–38, 41–43): definite/indefinite articles, demonstrative distance systems, pronoun-demonstrative relationship, grammaticalization cline; 16 languages, 10 theorems
  - `ArgumentStructure/Typology.lean` (Ch 106–111): reciprocals, passives, antipassives, applicatives, causative morphology; 18 languages, 8 theorems
- **`docs/typology-roadmap.md`**: Roadmap mapping WALS chapters to linglib phenomena, codifying the `Typology.lean`/`TypologyBridge.lean` convention and five-part phenomenon directory anatomy

## [0.224.59] - 2026-02-20

### Changed
- **DG infrastructure cleanup**: Eliminate `LexFeatures`; `LexEntry.features` now uses shared `Features` from Core/Basic.lean with DG-specific `inv` field on `LexEntry` directly; passive rule checks `voice` instead of `passive` boolean
- **Fragment-grounded lex entries**: `lex_kicked`, `lex_can`, `lex_does` now derive features from Fragment (`kick.toWordPast`, `FunctionWords.can.toWord`, `FunctionWords.does.toWord`) instead of manually duplicating field values
- **Move standard ArgStr to Core/Basic.lean**: `argStr_V0`/`VN`/`VNN`/`VPassive` and `satisfiesArgStr` moved from LexicalRules.lean to Core/Basic.lean alongside the types they operate on
- **Add `valenceToArgStr`**: Maps `Valence` → `Option ArgStr`, connecting `checkVerbSubcat` (count-based) to `satisfiesArgStr` (slot-based); grounding theorem `lex_kicked_from_fragment` proves the connection
- **Make `checkVerbSubcat` wildcard explicit**: Enumerate `clausal`/`copular`/`dative`/`locative`/`none` instead of catch-all `_`
- **Add `FunctionWords.toInf`**: Infinitival marker "to" (PART) in Fragment; DG_ControlBridge uses it instead of hardcoded `Word.mk'`
- Remove 14 lines of `#eval` tests from LexicalRules.lean (duplicated by formal theorems)

## [0.224.58] - 2026-02-20

### Added
- **DG ValencyBridge**: Full derivation chain from Fragment lexicon through DG valency theory to ArgumentStructure phenomena (Osborne 2019 Ch 6); 6 levels: frame satisfaction → subcategorization → passive rule → catena analysis → data match; all theorems by `rfl`/`native_decide`
- **DG ControlBridge**: Enhanced dependency analysis for control/raising (Osborne 2019 Ch 6 §6.8–6.9); proves information loss in basic trees, recovery in enhanced graphs, edge classification, and bridge to CTPDatum equi-deletion for all 7 English control verbs
- **Fragment infrastructure**: Add `toWordPast`, `toWordPastPart`, `toWordPresPart` methods to VerbEntry; add `Word.asPassive` compositional modifier; add 4 verb entries (buy, meet, sell, leave)

### Changed
- **`complementToValence` fix**: Clause-embedding types (finiteClause, infinitival, gerund, question, smallClause) now map to new `Valence.clausal` instead of misleading `.transitive`; `.np_pp` maps to `.locative`
- **VerbCore alternate frames**: Add `altComplementType`/`altControlType` fields for verbs with two complement types (e.g., hope: finiteClause + infinitival with subject control)
- **Features.tense**: Add `tense : Option Tense` field; `toWord3sg`/`toWordPl` set present, `toWordPast` sets past; `Tense` aliased to `UD.Tense`

## [0.224.57] - 2026-02-20

### Fixed
- **Close 5 sorries in ReflectInterval.lean**: Add `evalValid` precondition to `eval_sound` — the fallback intervals (div by non-positive, log of non-positive, inv, rpow of negative) were genuinely unsound (unbounded results in finite intervals); `evalValid` is verified via `native_decide` in the tactic; update `RSADecide.lean` to produce validity proofs; all 104 `rsa_decide`/`rsa_predict` invocations pass

## [0.224.56] - 2026-02-20

### Changed
- **Goodman & Stuhlmuller (2013) Data/Bridge split**: Add `Finding` inductive (11 findings from Experiments 1-2) to Data file; create Bridge file with `formalize : Finding → Prop` and `all_findings_verified` (all 11 native_decide proofs); move experiment-specific theorems from Theory to Bridge; make `getScore`/`normalize`/`sumScores` public

## [0.224.55] - 2026-02-20

### Changed
- **Kao et al. QUD refactor**: Replace manual `qudProject` match arms with declarative `project : World → Goal → ℕ` + `Finset.univ.filter.sum`; equivalence classes are derived from `project`, not hand-enumerated; remove `PriceState.sharp`; verified against memo reference implementation (all 12 values agree to ~7 significant figures)

## [0.224.54] - 2026-02-20

### Fixed
- **qudProject bug in Kao et al. (2014)**: approxPrice/approxPriceValence projections didn't include both round and sharp members of the equivalence class for round states; all 6 findings now agree numerically with the Python reference (ratio error < 0.01%)

### Changed
- **Verified.lean cleanup**: Reduce from ~300 lines to 60 — keep only 3 bridge axioms (`L1_gt_of_precomputed`, `L1_latent_gt_of_precomputed`, `L1_sum_gt_of_precomputed`); remove all dead Gen 1/Gen 2 evaluator infrastructure
- **Kao Data/Bridge redesign**: Replace `HyperbolePrediction`/`LiteralPrediction`/`HaloPrediction` Bool structures with `Finding` inductive (6 constructors); add `formalize : Finding → Prop` and `all_findings_verified : ∀ f, formalize f` to bridge file

## [0.224.53] - 2026-02-20

### Changed
- Close `million_never_literal` sorry in `RSA/Domains/Degrees.lean` (`native_decide`)

## [0.224.52] - 2026-02-20

### Changed
- **Chierchia1998 cleanup**: Remove dead `Domain` struct, `Individual.plural` (was `id`), `Kind.isNatural` (always `True`); drop `Option` from `down` — round-trip theorems now `up (down P) = P` / `down (up k) = k` (no `Option` peeling); unify `pluralize`/`massExtension` into single `pluralize`; scope DKP derivation section; trim unused opens in Dayal2004

## [0.224.51] - 2026-02-20

### Changed
- **Chierchia1998 `Individual` refactor**: Replace `inductive Individual` with `abbrev Individual Atom := Set Atom`; atoms are singletons, pluralities are larger sets; `PartialOrder`/`SemilatticeSup` from Mathlib for free; remove `partOf`, `join`, `LE` instance, `Kind.isPlurality`; add `IsMass` mass-noun condition; close both `up_down_id` and `down_up_id` sorries (2→0); bridge theorems `isMass_div`/`isMass_cum` connect to `Core/Mereology`

## [0.224.50] - 2026-02-20

### Changed
- **Kao et al. (2014) rewrite**: Slim Theory file to pure model definition (674→209 lines); move theorems to `Phenomena/Nonliteral/Hyperbole/RSA_KaoEtAl2014Bridge.lean` with Data/Bridge split; all 6 theorems proved by `rsa_predict` (0 sorries, was 1)
- **`rsa_predict` extended**: Three new goal forms — marginal L1 sum comparison, latent inference (`L1_latent`), and cross-utterance policy sum; `List.map/sum ↔ +` chain bridging via simp+linarith fallback
- **`Verified.lean`**: Three new bridge axioms — `L1_marginal_gt_of_precomputed`, `L1_latent_gt_of_precomputed`, `L1_sum_gt_of_precomputed`

### Added
- `Phenomena/Nonliteral/Hyperbole/Studies/KaoEtAl2014.lean`: Empirical data (qualitative predictions)
- `Phenomena/Nonliteral/Hyperbole/RSA_KaoEtAl2014Bridge.lean`: 6 bridge theorems (hyperbole affect, marginal affect, QUD inference, literal correctness, literal non-hyperbolic, pragmatic halo)

## [0.224.49] - 2026-02-20

### Added
- **Osborne & Groß (2012) "Constructions are catenae"**: Three-file integration following Theories/Phenomena separation:
  - `CatenalConstruction.lean` (Theories): `CatenalCx` bridge type pairing CxG `Construction` with DG catena witness; derived predicates (`isConstituent`, `isNonConstituentCatena`, `isContiguous`); `singleton` smart constructor; `nodes_nonempty` theorem; general `constituent_implies_catena` statement (1 sorry — requires BFS correctness bridge)
  - `OsborneGross2012/Data.lean` (Phenomena): 11 concrete dependency trees across 5 construction types — idioms (4), LVCs (3), verb chains (2), displacement (1), comparative correlative (1)
  - `DG_OsborneGross2012Bridge.lean` (Phenomena): Claim 1 (all construction types are catenae, 12 verified), Claim 2 (interleaving preserves catena-hood, 16 verified), 4 `CatenalCx` instances spanning full specificity spectrum, FKO1988 idiom typology bridge; 0 sorries in bridge

## [0.224.48] - 2026-02-20

### Changed
- `DenicEtAl2021Bridge.lean`: Rewrite bridge with genuine derivations — general coarsening theorem (`de_composed_is_ue`, universally quantified, structural proof via monoid homomorphism), UE strength as discriminating dimension, `envSignature` map deriving `isGloballyUE` from theory, `predictNPIEffect`/`predictPPIEffect` prediction functions verified against all 8 data points and `experiment1` list, full data file coverage (17/19 definitions linked)
- `DisjunctionIgnorance.lean`: Replace duplicate `ContextPolarity'` (2-valued) with canonical `ContextPolarity` from `Core.NaturalLogic` (3-valued), adding `.nonMonotonic → .inclusive` case

## [0.224.47] - 2026-02-20

### Changed
- `Tactics/RSAPredict.lean`: Exp-log algebraic simplification — detect `exp(α*(log(x)-c))` pattern in MetaBounds computation and evaluate as `x^α * exp(-α*c)` instead of calling `logPoint` (50-iteration bisection); eliminates 600 logPoint calls for Kao et al. 2014, reducing S1 reification from 14s to <1s (total: 204s → 2.4s, 85× speedup from original)

## [0.224.46] - 2026-02-20

### Changed
- `BarLevFox2020.lean`: Move II infrastructure (`isIICompatible`, `isMISet`, `II`, `isInnocentlyIncludable`, `exhIEII`) to `Exhaustivity/Basic.lean`; remove 7 dead definitions; parametrize A/B duplication via `extend_II_with_target` and `target_in_II`; extract `perm_cover` shared helper (688→534 lines, 0 sorries)

## [0.224.44] - 2026-02-20

### Fixed
- `Theories/Pragmatics/RSA/ScalarImplicatures/Hurford.lean`: Close 4 sorries — `base_redundancy`, `refined_disjunction_informative` via `native_decide`; `hurford_model_captures_rescue` from components; `hyponym_always_redundant` via `native_decide`
- `Phenomena/ScalarImplicatures/RSA_HurfordBridge.lean`: Close 2 sorries — `rsa_matches_data_someOrAll` and `rsa_matches_data_americanCalifornian` via `rfl`
- `Theories/Pragmatics/NeoGricean/Implementations/BarLevFox2020.lean`: Close 3 sorries — `fc_not_closed_general`, `fc_entails_permA`, `fc_entails_permB`; fix modeling bug (add `separatelyAB` world to distinguish ◇a∧◇b from ◇(a∧b)); prove free choice theorem via Innocent Inclusion with full MC-set/MI-set computation

## [0.224.43] - 2026-02-19

### Changed
- `Tactics/RSAPredict.lean`: L0 cache warm-up and Cauchy fast-path — pre-compute all L0(l,u,w) values before S1 loop so denominators are cached; fast-path `Real.ofCauchy` detection skips the isDefEq loop for large numeric literals; remove dead code (`buildIteFn`, `buildS1ScoreTable`, `mkQIExact`, `mkQIntervalFromBounds`)

## [0.224.42] - 2026-02-19

### Changed
- `Tactics/RSAPredict.lean`: Add expression-level memoization cache to `reifyToRExpr` — shared subexpressions (L0 denominators, meaning functions, cost terms) are computed once and reused across S1 score reifications; Kao et al. 2014 (1000 S1 scores) drops from 204s to 16s (12.7x speedup)

## [0.224.41] - 2026-02-19

### Added
- `Core/Categorical/MereoCat.lean`: Category of mereological domains — bundled partially ordered types with `StrictMono` morphisms; `DimensionChain.toMereoMor` bridge connects dimension chains to categorical composition
- `Core/Categorical/PartitionCat.lean`: Thin category of QUD partitions — refinement witnesses as morphisms via `PLift`; `QUDHom.toTrivial` (terminal), `QUDHom.composeLeft` (meet projection)
- `Core/Categorical/ScaleCat.lean`: Category of comparative scales — `OrderHom` morphisms over bundled preordered types with `ComparativeScale` metadata; `licensing_invariant` for same-boundedness morphisms
- `Core/Categorical/AgentCat.lean`: Category of rational action agents — score-proportionality morphisms form a groupoid; `AgentMor.preserves_policy` via Luce scale invariance
- `Events/DimensionCoherence.lean`: Cross-chain coherence theorems — `dimension_coherence` (two chains, same QUA pullback), `any_chain_qua_transfer` (falsifiable prediction for future dimension chains), `mereoMor_qua_pullback` (functorial QUA action)
- `DecisionTheoretic/PartitionAdjunction.lean`: Sufficient partition construction — `sufficientPartition` (coarsest utility-preserving QUD), forward Galois direction (`refinement_preserves_utility`), `dominance_transfers_within_cell`, counterexample proving backward direction false, `dpRefinement` preorder on decision problems

## [0.224.39] - 2026-02-19

### Changed
- `Tactics/RSAPredict.lean`: Compute L1 scores entirely at meta time — meta-level QInterval combinators (`metaQINormalize`, `metaL1Score`) mirror the object-level evaluators but run in MetaM with native ℚ arithmetic; `native_decide` now only checks separation of two concrete ℚ literals instead of evaluating the full QInterval composition pipeline; power-of-2 rounding (`roundBounds`) keeps intermediate ℚ denominators bounded

## [0.224.38] - 2026-02-19

### Fixed
- `DecisionTheoretic/Core.lean`: Prove `conjunction_dominates_disjunction` — add inclusion-exclusion helpers, positivity/monotonicity lemmas, and a pure-arithmetic `max_div_gt_or_div` lemma to avoid set/rw interaction issues; eliminates all sorrys in Core
- `DecisionTheoretic/ScalarImplicature.lean`: Prove `if_not_indeed_conjunction` via `conjunction_dominates_disjunction` with transitivity; eliminates all sorrys
- `DecisionTheoretic/But.lean`: Prove `default_but_properties` (Theorem 10) via Bayes reciprocity — negative relevance cross-multiplied with total probability and normalization; add helper lemmas for probSum splitting and commutativity; one sorry remains (Theorem 8, requires total probability decomposition)

## [0.224.37] - 2026-02-19

### Fixed
- `Tactics/RSAPredict.lean`: Handle Cauchy-form ℝ literals (`Real.ofCauchy`) in reifier — when `whnf` reduces `OfNat.ofNat ℝ n` past the OfNat instance to the internal constructor form, recover n via `findEmbeddedNat`; Kao et al. 2014 (10×20×5 = 1000 S1 scores) now passes

## [0.224.36] - 2026-02-19

### Added
- `Tactics/RSAPredict.lean`: Level-aware `rsa_predict` tactic — reifies S1 scores individually via RExpr to prevent exponential blowup on nested models (L0→S1→L1); handles product-type worlds, large ℝ literals, and latent variable marginalization
- `Core/Interval/Combinators.lean`: Generic QInterval combinators (`qi_sum_map`, `qi_normalize`, `qi_nonneg_mul`, `qi_softmax`) for compositional interval evaluation
- `Theories/Pragmatics/RSA/Core/Verified.lean`: Generic QInterval evaluators for each RSA level with bridge theorems (`L1_gt_of_score_sep`, `L1_latent_gt_of_score_sep`) reducing L1 policy ordering to interval separation checks

## [0.224.35] - 2026-02-19

### Fixed
- `blog/hugo.toml`: Add `params.author` to fix Hugo build error (`site.Author` removed in newer Hugo versions)

## [0.224.34] - 2026-02-19

### Changed
- `KaoEtAl2014_Hyperbole.lean`: Replace toy priors with fitted empirical distributions from paper; add QInterval-based computable evaluator for `native_decide` proofs; sorry one marginal-affect lemma pending shared-denominator proof

### Added
- `.gitignore`: Hugo build artifacts (`blog/.hugo_build.lock`, `blog/public/`)

## [0.224.33] - 2026-02-19

### Added
- `Core/Interval/ReflectInterval.lean`: Proof-by-reflection for interval arithmetic — reified `RExpr` type with `denote`, `eval`, and `eval_sound`, enabling `rsa_decide` to use `native_decide` on compiled interval bounds
- `Core/LuceChoice.lean`: Generic Luce choice rule parameterized over ordered fields, with IIA and scale invariance
- `Phenomena/Ellipsis/VPEllipsis.lean`: VP ellipsis empirical data (voice mismatch tolerance, Merchant 2013)
- `RationalAction.policy_gt_of_score_gt`: Strict policy monotonicity lemma for `rsa_decide` denominator elimination
- `Tactics/RSADecide.lean`: Reflection-based `RExpr` reifier for `rsa_decide`, replacing Expr-based approach

### Changed
- Consolidate `Core/DimensionBridge.lean` into `Core/MereoDim.lean` (§12 DimensionChain) and `Semantics/Events/DimensionBridge.lean`

### Removed
- `Core/DimensionBridge.lean` (contents moved to MereoDim and Events/DimensionBridge)

## [0.224.31] - 2026-02-19

### Changed
- Inline `conjGSQuestion` wrapper: `Add (GSQuestion W)` now points directly at `QUD.compose`; rename theorems to `compose_comm`/`compose_assoc`/`compose_trivial_left`
- Fix `isMentionSome` duplication in `Inquisitive.lean`: delegate to `isInquisitive` instead of duplicating body
- Move `InfoSet`, `totalIgnorance`, `restrictedCells`, `foldl_reps_mem`, `restrictedCells_cover`, `restrictedCells_inhabited` from `PragmaticAnswerhood.lean` to `Partition.lean` (general partition infrastructure, not pragmatics-specific); make helpers public
- Fix `whQuestionEntails` placeholder in `EntropyNPIs.lean`: replace `True` with proper predicate-agreement definition; prove `wh_subject_is_de` and `npi_licensed_wh_subject` from it
- Replace stub structures with real theorems in `Coordination.lean`: `functionallyDependent` with converse theorem, `conjoin` with refinement proof, `sluice_inherits_resolution`
- Document `probOfState` as `abbrev` of `probOfProp`; add ℚ↔ℝ bridge docstring in `ProbabilisticAnswerhood.lean`
- Add `toIssue`/`toIssue_alternatives` GSQuestion→Issue bridge in `Inquisitive.lean`

### Removed
- `DecisionTheory.lean` re-export shim (no downstream consumers)
- Dead code: `EmbeddedCoordination`, `Sluice` struct, duplicate `alternativeQuestion`, `alternative_vs_polar` (proved `True`), `conjunctionIsMentionAll`/`inheritsMentionSome`, `MentionSomeQuestion`/`existentialCreatesMentionSome`, `GSQuestion.equivInJ`/`isQuestionIn`, `false_proposition_true_pragmatic_answer` (proved `True`)

## [0.224.30] - 2026-02-19

### Added
- `blog/scripts/gen_map.py`: Auto-generate map data from Lean import graph (nodes, edges, tiers, positions, descriptions)
- `blog/static/js/map-data.js`: Generated data file consumed by the interactive map page
- `blog/content/map.md`: Interactive "Map of Formal Linguistics" page, now loads auto-generated data instead of hardcoded constants

## [0.224.29] - 2026-02-19

### Added
- `CausalVerb.lean`: Unified CausalFrame abstraction (Nadathur 2023) bridging implicative verbs, ability modals, and degree constructions through a single parameterized frame with actualization modes
- `CausalClosure.lean`: `normalDevelopment` as Mathlib `ClosureOperator` on `(Situation, trueLE)` for positive dynamics; sufficiency = closure membership
- `DegreeCausation.lean`: Degree constructions (*enough/too*) as CausalFrame instances with aspectual actualization
- `algClosureOp`: Mathlib `ClosureOperator (α → Prop)` instance for mereological `AlgClosure`, grounding `subset_algClosure`/`algClosure_mono`/`algClosure_idempotent` in Mathlib
- `IsSumHom.toSupHom` / `SupHom.toIsSumHom`: Bidirectional bridge between linglib's `IsSumHom` and Mathlib's bundled `SupHom` (SLat hom-set)
- `GaloisConnection.gc`: Mathlib `GaloisConnection` instance for `extension`/`intension` via `OrderDual`, grounding the hand-proved `galois_connection` theorem

### Changed
- Make `positive_normalDevelopment_grows` public in `Sufficiency.lean` (was private, needed for closure operator axioms)
- Extend `Implicative.lean` with `ImplicativeScenario` structure and `manageSem`/`failSem` semantics
- Extend `Ability.lean` with `AbilityScenario` and aspectual modulation (`abilityWithAspect`)

## [0.224.28] - 2026-02-19

### Changed
- Replace false `probAnswers_when_consistent` with `probAnswers_when_entailing` — consistency doesn't guarantee probability increase, but entailment gives conditional probability 1
- Replace false `nonExhaustive_incomplete_answer` with `nonExhaustive_witness` — polar questions have ≤2 cells, so the original conclusion was unprovable
- Fix `pragmaticAnswer_monotone_up` by adding `hPinJ'` (P ⊆ J') hypothesis and proving via `restrictedCells_cover` + transitivity
- Fix `exhaustive_rigid_gives_complete_answer` by adding non-emptiness hypothesis
- Fix `pairList_as_conjunction` by switching `individualQuestion` to `all beq` pattern and proving pointwise `sameAnswer` equality

### Added
- `restrictedCells_cover`: every J-world belongs to some cell of J/Q (key helper for pragmatic answerhood proofs)
- `foldl_conj_sameAnswer`: foldl of question conjunction distributes over `sameAnswer`

### Fixed
- Close 5 sorrys across Question semantics (ProbabilisticAnswerhood 1, ScopeReadings 1, PragmaticAnswerhood 3)

## [0.224.27] - 2026-02-19

### Changed
- Fix `assertionStrength` from `negMulLog(P)` (weighted self-information) to `-log(P)` (surprisal), matching van Rooy (2003)'s informativity measure
- Replace false `questionUtility_eq_entropy_for_epistemic` (0/1 utility ≠ entropy) with `questionEntropy_nonneg`
- Replace ill-typed `entropy_leq_expected_utility` (ℝ ≤ ℚ) with `questionEntropy_binary`

### Added
- `questionEntropy_nonneg`: entropy is non-negative for valid cell probabilities
- `questionEntropy_binary`: for binary partitions, `questionEntropy = binaryEntropy(P(pos))`
- `npi_assertion_licensed_de`: NPI narrows negation → higher surprisal, via `Real.log_le_log`
- `unified_npi_licensing`: NPI licensing for both assertions (surprisal monotonicity) and questions (entropy increase) under DE/negative-bias polarity

### Fixed
- Close remaining 3 sorrys in EntropyNPIs (3 → 0); file is now sorry-free

## [0.224.26] - 2026-02-19

### Changed
- Refactor `EntropyNPIs.lean` from ℚ-based `informativity`/`questionEntropy` to ℝ-valued `Real.negMulLog` from Mathlib, with `Fintype`-based cell probability sums
- Drop `informativity` entirely; `negMulLog` is the per-cell entropy contribution
- Replace list-based `worlds.filter` with `cellProb` via `Finset.sum`

### Added
- `binaryEntropy`, `binaryEntropy_le_half`: binary entropy function and its maximum at ½ via `concaveOn_negMulLog`
- `binaryEntropy_mono_of_closer_to_half`: binary entropy is monotone on [0, ½], proved via double application of `concaveOn_negMulLog` with convex combination parameter `t = (q-p)/(1-2p)`
- `entropy_maximal_equiprobable`: equiprobable binary questions maximize entropy
- `settled_entropy_zero`, `kl_strengthens_implies_higher_entropy`: settled questions have zero entropy; non-settled have positive
- `stressed_any_achieves_kl_strengthening`: stressed "any" achieves K&L strengthening when negative cell has positive probability
- `npi_increases_entropy_when_negatively_biased`, `ppi_increases_entropy_when_positively_biased`: domain widening increases entropy when question is biased toward the widened polarity
- `strong_npi_creates_rhetorical`: strong NPI bounding cell probability by ε bounds entropy by `binaryEntropy(ε)`

### Fixed
- Close 6 sorrys in EntropyNPIs (9 → 3); remaining 3 are ℚ/ℝ bridge theorems

## [0.224.25] - 2026-02-19

### Added
- `QInterval.exact_zero_containsReal`, `exact_one_containsReal`: specialized containment lemmas for 0 and 1 that use `OfNat.ofNat` instead of `Nat.cast`, fixing kernel type mismatches in nested proof terms (`Nat.cast 1 = 0 + 1 ≢ OfNat.ofNat 1 = One.one`)
- `QInterval.decidable_rec_pos/neg_containsReal`: handle `ite` unfolded to `Decidable.rec` by whnf
- `QInterval.invPos`, `invPos_containsReal`: inverse of positive intervals
- `QInterval.eq_zero_of_bounds`, `zero_mul_containsReal`, `mul_zero_containsReal`, `zero_div_containsReal`: zero short-circuit lemmas
- `QInterval.mul`, `mul_containsReal` (axiom): general 4-corner interval multiplication
- `rsa_decide`: exp/log reification via `expInterval`/`logInterval`, let-binding handler, Decidable.rec handler, Inv.inv handler, zero short-circuiting for `*` and `/`
- `LogInterval.lean`: log interval arithmetic via bisection inversion of exp

### Fixed
- `rsa_decide` natural literal handler uses `exact_zero/one_containsReal` for n=0,1 to avoid `Nat.cast` vs `OfNat.ofNat` kernel mismatch that broke nested ite proof construction

## [0.224.22] - 2026-02-19

### Changed
- Collapse `IndividuationCriterion` into `Setoid`: `DotType` now holds `Setoid (A₁ × A₂)` directly instead of a custom struct; `countDistinct` takes `Setoid α`; all field references `.rel`/`.equiv` → `.r`/`.iseqv`

## [0.224.21] - 2026-02-19

### Changed
- Refactor `IndividuationCriterion`: use `Equivalence` instead of separate `refl`/`symm`/`trans` fields; add `toSetoid` bridge
- Replace `ComplexType` alias with `DotType` struct bundling aspect types with their individuation criterion (the book's point: individuation is part of the lexical specification, not external)
- Add `IType.meet`/`IType.join` to `Core.lean`: compose carriers and names so intensional identity propagates through type operations; add `IType.meet_true_iff`, `IType.join_true_iff`
- Simplify `FrameBridge.lean`: drop `TypedFrame`/`Attribute` (Lean structures *are* typed frames); keep `Frame2`/`FrameType2` for explicit proofs

## [0.224.20] - 2026-02-19

### Added
- New `TypeTheoretic/Copredication.lean`: dot types with individuation, copredication operator, `IndividuationCriterion` with counting, `individuation_can_diverge` theorem (Chatzikyriakidis et al. 2025 §3)
- New `TypeTheoretic/FrameBridge.lean`: typed attribute-value frames, `Frame2 ↔ SimpleRecordType2` roundtrip, `frame_truth_eq_record_truth` equivalence, `frame_structure_matters` (Chatzikyriakidis et al. 2025 §2–3)
- New `Phenomena/Polysemy/Data.lean`: copredication empirical data (book, lunch, newspaper examples; counting datum from Gotham 2017)
- New `Phenomena/Polysemy/CopredBridge.lean`: `DotType PhysObj Info` with `physical_count = 3`, `informational_count = 2`, `counting_matches_datum`
- New `Phenomena/Attitudes/IntentionalIdentity/Data.lean`: Geach's Hob-Nob puzzle, Edelberg's spy variant
- New `Phenomena/Attitudes/IntentionalIdentity/Bridge.lean`: TTR solution via shared `IType` across agents, `witch_need_not_exist`, `intensional_distinction_enables_ii`
- Proposition granularity hierarchy in `TypeTheoretic/Core.lean`: `prop_collapses_intensional_distinctions`, `ttr_strictly_finer_than_worlds`

### Changed
- Rename `Probabilistic/Frames/` → `Probabilistic/Scenarios/` to disambiguate probabilistic scenario semantics (Erk & Herbelot 2024) from typed attribute-value frames (Petersen, Löbner, Osswald); update namespace and all imports

## [0.224.19] - 2026-02-19

### Changed
- Close 49 sorrys across 15 files via `native_decide`, `norm_num`, and `rfl`:
  - SikosEtAl2021Bridge (3): context classification theorems
  - NoncooperativeCommunication (1): `barnett_backfire_instance`
  - SumersEtAl2023 (4): reward examples, truthfulness/relevance independence
  - ScontrasPearl2021Bridge (3): empirical ordering, typed distribution ordering, inverse preference
  - HeKaiserIskarous2025Bridge (6): dimensions, cost, fuzzy interpretation, polarity
  - CremersWilcoxSpector2023Bridge (5): domain counts (utterances, worlds, parses, lexica, goals)
  - Nouwen2024Bridge (3): evaluative measure properties (horrible/pleasant)
  - YoonEtAl2020Bridge (6): softNot properties, negation vagueness, domain counts, cost
  - FrankeBergen2020Bridge (3): dimensions, literal meaning checks
  - VanTielEtAl2021 (4): Montague grounding (threshold/monotonicity)
  - LassiterGoodman2017 (2): graded tallness monotonicity and boundary
  - LexicalAmbiguity (1): astronomer/star conflict example
  - TesslerGoodman2019 (1): generic monotone prevalence
  - TesslerFranke2020 (3): gap semantics (happy/not-unhappy distinction)
  - Embedded/Questions (4): question uniqueness witnesses

## [0.224.18] - 2026-02-19

### Added
- State completeness direction of Holliday & Icard (2013) Theorems 6–7 in Scale.lean (`theorem6_completeness`, `theorem7_completeness`; both sorry)
- Add `FinAddMeasure.toWorldPrior`: extract world prior from measure via singletons μ({w}), with `toWorldPrior_nonneg` lemma
- Add `probToOrdering_const` to ProbabilityOrdering.lean: `probToOrdering` is world-independent (proof by `rfl`)
- New `Linglib/Comparisons/KratzerEpistemicRSA.lean`: Kratzer–Epistemic–RSA bridge tracing the dependency chain from Kratzer ordering sources through l-lifting, EpistemicSystemW/FA, representation theorems, to RSA worldPrior. §1 `kratzerToSystemW` and §2 (uses `toWorldPrior`) are sorry-free definitions; §3 `kratzer_to_rsa_prior` and §4 `prob_ordering_roundtrip` are conjectures (sorry)

## [0.224.14] - 2026-02-19

### Changed
- Redesign RSAConfig API: replace `speakerUtility : SpeakerUtility U W` with inline `s1Score` field taking a `Latent` parameter, so latent variables (QUDs, lexicons) can enter at S1 rather than being forced into `meaning`
- Delete `SpeakerUtility.lean` and its import from `Linglib.lean`
- Drop `.qud` smart constructor — each paper constructs `RSAConfig` directly
- Migrate `FrankGoodman2012`, `BellerGerstenberg2025`, `QingFranke2013` to inline `s1Score`
- Rewrite `KaoEtAl2014_Hyperbole` from scratch matching the paper: 10 price states (round/sharp pairs), binary affect, 5 QUD goals, `s1Score` as `exp(α·(ln L0_proj - C(u)))`, differential utterance cost (C(sharp)/C(round) = 3.4), 4 sorry'd theorems (hyperbole, literal inference, QUD inference, pragmatic halo)

## [0.224.16] - 2026-02-19

### Changed
- Delete duplicate `divNonnegPos`/`divNonnegPos_containsReal` from QInterval.lean (identical to `divPos`)
- Namespace `EpistemicAxiom` definitions in Scale.lean (wrap 6 dotted-name defs in proper namespace block)
- Upgrade InformationTheory.lean import from `Mathlib.Data.Rat.Defs` to `Mathlib.Algebra.Order.Ring.Rat`; remove workaround import from LCEC.lean
- Replace `foldl (· + ·) 0` with `List.sum` in `entropy` and `iComplexity`
- Fix false ambidirectionality theorems in Comparative.lean: replace `sorry`'d `comparative_ambidirectional`/`equative_ambidirectional` (ill-defined `(· > ·)` MAX on dense orders) with proved `comparative_boundary`/`equative_boundary` using `(· ≥ ·)` MAX via new `maxOnScale_ge_atMost` lemma

## [0.224.15] - 2026-02-19

### Changed
- Close `axiomA_iff_fa` sorry in Scale.lean: Axiom A ↔ finite additivity via set-algebraic decomposition (`(A∪C)\(B∪C) = A\B` when disjoint; `(A\B)∪(A∩B) = A`)
- Close `transparent_iComplexity_zero` sorry in LCEC.lean: transparent paradigm systems have I-complexity = 0, via `foldl_add_zero_of_forall_zero` helper and list membership decomposition

## [0.224.13] - 2026-02-19

### Changed
- Close 3 Scale.lean sorrys: `inducedGe_axiomT` (monotonicity via union-diff decomposition), `toSystemFA.bottom` (μ(∅)=0 from additivity), `toSystemFA.additive` (qualitative additivity via diff-inter decomposition with `conv_lhs`)

## [0.224.12] - 2026-02-19

### Added
- Add `Linglib/Core/Interval/` module: `QInterval.lean` (rational interval arithmetic with ℝ containment), `PadeExp.lean` (Padé approximant for exp), `RpowInterval.lean` (real power intervals)
- Close `divPos_containsReal` and `divNonnegPos_containsReal` sorrys in QInterval.lean: division monotonicity via calc chains

### Fixed
- Commit untracked `Linglib/Core/Interval/` directory and update `Linglib.lean` imports (fixes CI)

## [0.224.11] - 2026-02-19

### Changed
- Close `deriv_logSumExp` sorry: derivative of log-partition function via `HasDerivAt.fun_sum`, chain rule, and algebra
- Close `in_adverbial_incompatible_with_ssr` sorry: QUA + SSR_univ contradiction via `qua_cum_incompatible` (modulo `ssr_univ_implies_cum`); remove redundant `[PartialOrder (Ev Time)]` instance
- Close `semantic_is_pragmatic_limit` sorry: pragmatic answerhood reduces to semantic answerhood when J = totalIgnorance, with helper lemmas `filter_totalIgnorance`, `intersect_totalIgnorance`, `restrictedCells_totalIgnorance`

## [0.224.9] - 2026-02-18

### Added
- `nonneg_of_forall` tactic: closes `0 ≤ f a₁ + ⋯ + f aₙ` given `∀ x, 0 ≤ f x`
  in context, decomposing via `add_nonneg`/`mul_nonneg` then applying local hypotheses

## [0.224.8] - 2026-02-18

### Changed
- Refactor `Core/Causation.lean`: use `bif` for Bool branches, make `extend_hasValue_same/diff` params implicit, add `normalDevelopment_succ_fix`, `normalDevelopment_succ_step`, and general `normalDevelopment_fixpoint_at` theorem
- Update `Necessity.lean`, `ProductionDependence.lean`, `Resultatives.lean`: use implicit-param versions of `extend_hasValue_diff`
- Refactor `Sufficiency.lean`: replace `simp only [normalDevelopment]` with `rw [normalDevelopment_succ_fix/step]`, replace `simp only [hMet, ↓reduceIte]` with `rw [apply_of_met/not_met]`

## [0.224.7] - 2026-02-18

### Added
- `rsa_decide` Finset.sum fast-path: detect summation head constants and call
  `whnf` directly, saving ~3-5 depth per sum element (critical for |W| ≥ 10)
- `RSAConfig.qud` smart constructor: separates base semantics from QUD
  projection, sets `Latent := QUD` with composable `qudProject` function
- `RSA.Priors` module: `jointPrior`, `uniformPrior` combinators with
  non-negativity proofs for building priors over product spaces

## [0.224.6] - 2026-02-18

### Changed
- Close `independent_source_disrupts_tightness` sorry in `Resultatives.lean`:
  parametric proof that an independent energy source disrupts causal necessity,
  using manual foldl expansion with pre-computed `hasValue` facts
- Add `CausalLaw.apply_of_met`, `apply_of_not_met`, `simple_effect`,
  `simple_effectValue` simp lemmas to `Core/Causation.lean` — avoids stuck
  `if false = true then …` terms when reasoning about causal law application

## [0.224.5] - 2026-02-18

### Added
- Formalize Holliday & Icard (2013) epistemic comparative likelihood in `Core/Scale.lean` (§ 14):
  axiom hierarchy (W ⊂ F ⊂ FA), measure semantics (`FinAddMeasure`), world-ordering semantics
  (Halpern lift), representation theorems, `axiomA_iff_fa` bridge, `EpistemicTag` + `LicensingPipeline`
- `five_frameworks_agree`: extend four-framework licensing agreement to five (Kennedy, Rouillard, Krifka, Zwarts, Holliday–Icard)
- Add `holliday-icard-2013` to bibliography

## [0.224.4] - 2026-02-18

### Changed
- Dissolve `Core/DimensionBridge.lean`: move all remaining content to natural homes
  - BoundaryType bridge + LicensingPipeline instance → `Core/Time.lean`
  - DimensionChain, deep bridge, pullback patterns, Krifka licensing → `Core/MereoDim.lean`
  - Zwarts licensing theorems → `Core/Path.lean`
  - `four_frameworks_agree` → `Core/Scale.lean` (MIPDomain namespace)
- Update `Events/DimensionBridge.lean` imports and namespace opens

### Removed
- `Core/DimensionBridge.lean` — all content co-located with defining types

## [0.224.3] - 2026-02-18

### Changed
- Move `MereoTag`, `LicensingPipeline` typeclass, and `universal` licensing theorem from `Core/DimensionBridge.lean` to `Core/Scale.lean` — these are generic scale-theoretic concepts, not dimension-specific infrastructure
- `BoundaryType` instance stays in `DimensionBridge` (depends on `Core/Time`)

## [0.224.2] - 2026-02-18

### Changed
- Simplify `ComparativeScale` from 4 fields (`le`, `le_refl`, `le_trans`, `boundedness`) to 1 field (`boundedness`), with ordering from ambient `[Preorder α]`
- Fix `AdditiveScale.fa` to use `≤`/`⊔` from ambient `SemilatticeSup` instead of bundled `le`, eliminating coherence gap with Mathlib's ordering
- Delete `ScaleMorphism` and its namespace — categorical morphisms are just Mathlib's `Monotone`
- Delete `ComparativeScale.ofPreorder`/`ofLinearOrder` (now trivial `⟨b⟩`)
- Simplify `MIPDomain` constructors to `{ boundedness := b, ... }`
- Replace `MereoDim ↔ ScaleMorphism` bridge (§11) with `MereoDim ↔ Monotone` bridge: `mereoDim_monotone`, `extMeasure_monotone`

### Added
- `AdditiveScale.IsRepresentable`: representation theorem for additive scales (monotone additive function into ℚ)
- `open_scale_unlicensable`: boundedness necessity theorem — open scales always have monotone families with no optimum

## [0.224.1] - 2026-02-18

### Added
- Add categorical root structure to `Core/Scale.lean`: `ComparativeScale` (preorder + boundedness), `AdditiveScale` (+ join + FA), `ScaleMorphism` (monotone maps), with `id`, `comp`, `ofMonotone`, `ofStrictMono`
- `MIPDomain` now extends `ComparativeScale` structurally (via `ofLinearOrder`)
- Add `MereoDim` ↔ `ScaleMorphism` bridge theorems in `Core/MereoDim.lean` §11: `mereoDim_scaleMorphism`, `extMeasure_scaleMorphism`, `mereoDim_comp_eq_scaleMorphism_comp`, `dimension_chain_scaleMorphism`, `qua_cum_boundedness_coherence`

### Changed
- Rename `Core/MeasurementScale.lean` → `Core/Scale.lean`; update imports in 15 downstream files

## [0.224.0] - 2026-02-18

### Changed
- Close 4 sorries across Causation and Distributivity modules
- `redundant_cause_not_necessary` (Necessity.lean): add `hne : c1 ≠ c2` and `hPos : isPositiveDynamics` hypotheses; prove via `Situation.trueLE` and `normalDevelopment_trueLE_positive` monotonicity
- `single_pathway_sufficiency_implies_necessity` (ProductionDependence.lean): prove P-CAUSE → D-CAUSE in single-pathway models by showing the only law doesn't fire when cause=false
- `falseOnAll_full_iff_noneSatisfy`, `pluralTruthValue_eq_candidateSemantics` (Distributivity.lean): fix `fullCandidateSet` to exclude empty sub-pluralities, prove both theorems using singleton witnesses
- Add public `normalDevelopment_trueLE_positive` wrapper (Sufficiency.lean) for cross-file monotonicity proofs

## [0.223.9] - 2026-02-18

### Changed
- Close all 3 `sorry`s in `Questions/Polarity.lean`: `request_forces_ppq` (0.223.7), `tagQuestionInformativity`, `rhetoricalUsePPQ`
- Simplify `surprisal` approximation: remove broken `prob=0 → 1000` cap and `prob≥1 → 0` guard; use `1/prob - 1` unconditionally (monotone for all `prob > 0`), with a guard only for ℚ's `1/0 = 0`
- Add `informativenessAdvantage_pos`: if `P(p) > 0` and `P(p) < P(¬p)`, then `surprisal(p) > surprisal(¬p)`, via `1/a - 1/b = (b-a)/(ab) > 0`
- Add helper lemmas: `surprisal_eq_inv_sub`, `lt_of_positiveIsLessLikely`, `pnot_fold_eq`
- `tagQuestionInformativity` and `rhetoricalUsePPQ` now need only `hPosProb` (no `hSubOne`)

## [0.223.8] - 2026-02-18

### Added
- Formalize Ackerman & Malouf (2013) Low Conditional Entropy Conjecture (LCEC)
- Add `Core/InformationTheory.lean`: factor ℚ-valued entropy, conditional entropy, mutual information out of RSA into domain-agnostic Core module
- Add `Theories/Morphology/WP/LCEC.lean`: `ParadigmSystem` (single-list entries), `InflectionClass`, `cellEntropy`, `conditionalCellEntropy`, `iComplexity`, `eComplexity`, LCEC predicate, implicative relations, `groupBySum` helper, `fromStems` bridge to `Core.MorphRule`
- Add `Phenomena/Morphology/Typology.lean`: `LanguageData` type + cross-linguistic paradigm complexity data for 10 typologically diverse languages (Ackerman & Malouf 2013, Tables 2-3)
- Add `Phenomena/Morphology/Studies/AckermanMalouf2013/Bridge.lean`: per-language LCEC verification, E/I-complexity dissociation theorems, Mazatec case study

### Changed
- Refactor `RSA/Extensions/InformationTheory/Basic.lean` to re-export from `Core.InformationTheory` via `export`, keeping `RSALevel` in RSA namespace
- Remove empty `Theories/Morphology/W&P/` directory (replaced by `WP/`)

### Changed
- Refactor `RSA/Extensions/InformationTheory/Basic.lean` to re-export from `Core.InformationTheory` via `export`, keeping `RSALevel` in RSA namespace

## [0.223.7] - 2026-02-18

### Changed
- Close `request_forces_ppq` sorry in `Questions/Polarity.lean`: when goal = questioned proposition, goalProbAdvantage ≥ 0 (requests force PPQ)
- Proof: P(g|¬p) = 0 (filtering by ¬p yields no p-worlds) and P(g|p) ∈ {0, 1} ≥ 0
- Add 8 private helper lemmas: `foldl_add_zero_init`, `p_false_of_mem_filter_pnot`, `conditionalGoalProb_goal_negCondition_eq_zero`, `foldl_div_factor{,_gen}`, `foldl_congr_mem`, `foldl_filter_goal_eq_div`, `conditionalGoalProb_self_nonneg`
- Fix `tagQuestionInformativity` and `rhetoricalUsePPQ`: add positive-probability hypothesis (original statements were false — counterexample: P(p)=0, P(¬p)=1/2000 gives surprisal(p)=1000 < surprisal(¬p)=1999)

## [0.223.6] - 2026-02-18

### Changed
- Close `before_ambidirectional` sorry → `before_preEvent_ambidirectional` in `TemporalConnectives.lean`: *before* is truth-conditionally insensitive to event polarity (Rett 2026, §5.2)
- Define `preEventDenotation`: pre-event complement of [s, f] as stative denotation of [bot, s], capturing Rett's stipulation that only pre-event runtimes are relevant
- Add `complet_stative`: COMPLET on stative denotations extracts the finish point (mirrors `complet_bridges_cessation`)
- Add `timeTrace_stative_closedInterval`, `maxOnScale_lt_stative`, `timeTrace_complet_preEvent`, `maxOnScale_lt_complet_preEvent`: building-block lemmas connecting stative/COMPLET traces to MAX₍<₎ singletons
- Proof chain: both `stativeDenotation i_B` and `COMPLET(preEvent)` share MAX₍<₎ = {i_B.start}, so `before_determined_by_max` gives the ↔
- Remove false `before_ambidirectional` (used `isAmbidirectional` with full Bᶜ, which fails for dense/discrete time)

## [0.223.5] - 2026-02-18

### Changed
- Fix Rett (2026) citation: preprint/ms., not *Language* (4 files)
- Add `maxOnScale_lt_closedInterval`, `maxOnScale_gt_closedInterval` to `Core/MeasurementScale.lean`: MAX₍<₎ and MAX₍>₎ on closed intervals are singletons
- Add `before_determined_by_max`, `rett_before_closedTrace_eq` to `TemporalConnectives.lean`: *before* truth conditions depend only on MAX₍<₎ of B's time trace; reduce to t < s for closed-interval traces
- Rewrite `before_ambidirectional` sorry analysis: Rett's argument uses pre-event complement (not full Bᶜ), shared informative bounds at boundary point; `isAmbidirectional` with full complement is false
- Fix `while_not_ambidirectional` unused section variable lint

## [0.223.4] - 2026-02-18

### Changed
- Close 3 `sorry`s in `Theories/Semantics/Tense/TemporalConnectives.lean`:
  - `anscombe_rett_agree_stative_before_start`: Anscombe and Rett agree on stative *before*-start (maxOnScale picks i_B.start as minimum)
  - `after_not_ambidirectional`: *after* is NOT ambidirectional (add `∃ a b, a < b` hypothesis; fails for trivial time types)
  - Fix `anscombe_rett_agree_telic_after_finish` → `rett_implies_anscombe_telic_after_finish`: the ↔ was false (Anscombe only needs *some* B-time before A; Rett needs A after B's finish); prove the correct → direction
- Update `before_ambidirectional` sorry comment: theorem is false for general `LinearOrder Time` (MAX₍<₎(Bᶜ) ≠ MAX₍<₎(B) for bounded/discrete time types; requires Rett 2026 reanalysis)

## [0.223.3] - 2026-02-18

### Changed
- Close `superlative_isStrawsonDE` sorry in `Theories/Semantics/Entailment/StrawsonEntailment.lean`: superlatives are Strawson downward-entailing (von Fintel 1999)
- Fix and close `atomCount_sup_disjoint` sorry in `Core/Mereology.lean`: add join-primality hypothesis (atoms must be join-prime for additivity to hold; the original statement was false for general `SemilatticeSup`, e.g. M₃ lattice)

## [0.223.2] - 2026-02-18

### Changed
- Close 2 `sorry`s in `Core/UtilityTheory.lean`: `threeClasses` (Luce Theorem 12, neutral class indifference) and `scaleDecomposition` (§3.D multiplicative factoring v(aρb) = w(a,b) · φ(ρ))
- Add `EventLuceScale`, `GambleLuceScale` ratio scale structures
- Add helper lemmas: `luce_eq_half_iff`, `ratio_eq_of_frac_eq`, `ratio_independent`, `v_eq_product`
- Add between-class ordering theorems: `favorable_over_unfavorable`, `favorable_over_neutral`
- Correct `threeClasses` statement: restrict to neutral class (same-class indifference is false for favorable/unfavorable)

## [0.223.1] - 2026-02-18

### Added
- Formalize Luce (1959) Choice Axiom (IIA) in `Core/RationalAction.lean` §1a: constant ratio rule, subset choice (`pChoice`), IIA theorem, product rule, scale invariance, proportional-scores uniqueness
- New `Core/UtilityTheory.lean`: Luce Chapter 3 gamble choice theory — decomposition axiom, monotonicity axiom, event equivalence classes, scale decomposition, RSA utility decomposition bridge

### Changed
- Close 3 `sorry`s in `Core/RationalAction.lean`: `shannonEntropy_le_log_card` (via KL(p‖uniform) ≥ 0), `softmax_maximizes_entropyReg` (via Gibbs VP / α), `softmax_unique_maximizer` (via KL = 0 ⟹ p = q using `klFun_eq_zero_iff`)
- Add helper lemmas: `shannonEntropy_eq_negMulLog`, `kl_eq_zero_imp_eq`
- Improve proof sketches for remaining `sorry`s (`logSumExp_convex`, `deriv_logSumExp`)

## [0.223.0] - 2026-02-18

### Changed
- **Remove entire ℚ-based RSA system**: delete RSAScenario, RSA.Eval, ExactDist, RationalPower, and all ℚ-valued RSA computation infrastructure (~15,000 lines removed across 95 files)
- **New RSA API**: RSAConfig (ℝ-valued, pluggable SpeakerUtility) + RationalAction (Luce choice) are now the sole RSA infrastructure
- Gut Core/Basic.lean, Eval.lean, Distribution.lean, BasicQ.lean, Model.lean, Convergence.lean and 9 other core stubs to thin re-exports of Config.lean
- Rewrite all ~30 RSA implementation files against new API (domain types and meaning functions preserved, RSA computation results sorry'd)
- Rewrite all RSA domain files (Quantities, Degrees, QUD, Scope) removing ℚ computation
- Gut all RSA extension files (InformationTheory, LexicalUncertainty, ArgumentativeStrength, ScalarImplicatures, Questions)
- Update all phenomena bridges and comparison files to remove old API dependencies
- Replace ExactDist with Prior (W → ℚ) in ProbabilisticAnswerhood and Additive particle semantics
- Fix SumersEtAl2023 decide→norm_num for ℚ comparisons

## [0.222.10] - 2026-02-18

### Added
- Formalize Sikos et al. (2021) "Reevaluating pragmatic reasoning in language games" — critique of RSA's empirical value in reference games
- Data file: experimental design, model fit comparisons (baseline ≈ RSA across 3 experiments), context type taxonomy
- Bridge file: structural model relationships (baseline = L0, L1 = L0 in trivial contexts, L1 ≠ L0 in solvable contexts)
- Metric sensitivity analysis: prove that 8/12 items in FG2012's context are trivially predicted (L0 = L1), so correlation-based evaluation is structurally insensitive to pragmatic effects — the metric is too coarse to distinguish models, regardless of human behavior

## [0.222.9] - 2026-02-18

### Changed
- Refactor BSML: split theory code out of `Phenomena/Modality/Aloni2022.lean` into `Theories/Semantics/Dynamic/Systems/BSML/Basic.lean` (core types, support/anti-support) and `FreeChoice.lean` (enrichment, FC theorems)
- Drop phantom type parameter `W` from `BSMLFormula`; bundle `worlds : List W` into `BSMLModel`; drop `worlds` parameter from `support`/`antiSupport` signatures
- Move `Phenomena/Modality/CompareFC.lean` to `Comparisons/FreeChoice.lean`
- Clean dead code from `TeamSemantics.lean` (remove `BilateralFormula`, `TeamPartition`, `supports`/`antiSupports`, `TeamProp`, `liftProp`, `isFlat`, `Entails`)
- Slim `Aloni2022.lean` to bridge file (concrete models, formulas, #eval checks only)

## [0.222.8] - 2026-02-18

### Changed
- Close all 3 remaining `sorry` instances in Aloni 2022 BSML formalization: `enriched_support_implies_nonempty` (disj case), `narrowScopeFC`, `wideScopeFC`
- Add infrastructure lemmas for split/subteam membership, singleton witnesses, indisputability transfer

## [0.222.7] - 2026-02-18

### Removed
- Delete `RSA/Domains/ReferenceGames.lean` — redundant domain abstraction layer; implementations define their own types
- Inline `Color` type in `DegenEtAl2020.lean`, drop vestigial import from `WaldonDegen2021.lean`
- Fix stale docstring references in `Almog2014.lean`, `Demonstratives.lean`

## [0.222.6] - 2026-02-18

### Changed
- Fix Aloni 2022 BSML enrichment to match paper's Definition 6: conjunction and disjunction no longer add redundant NE wrappers (`[φ ∧ ψ]⁺ = [φ]⁺ ∧ [ψ]⁺`, `[φ ∨ ψ]⁺ = [φ]⁺ ∨ [ψ]⁺`)
- Restrict FC theorems (`narrowScopeFC`, `wideScopeFC`, `dualProhibition`) to atomic formulas — the general versions are false (counterexample theorem added)

### Added
- `narrowScopeFC_false_for_general_formulas`: native_decide counterexample showing `[◇(α ∨ β)]⁺ ⊨ ◇α` fails for `α = ¬□□q` with empty accessibility
- Close `dualProhibition` sorry with structured proof via anti-support monotonicity for ◇
- Add helper lemmas: `list_all_mono`, `team_all_mono`, `team_all_of_isEmpty`, `antiSupport_poss_weaken`, `antiSupport_enriched_disj_implies_left/right`

## [0.222.4] - 2026-02-18

### Added
- Add `Phenomena/WordOrder/Studies/ArnoldEtAl2000Bridge.lean` — bridge theorems deriving structural limitations of three competing ordering accounts from their own definitions:
  - DLM (`totalDepLength`) is discourse-blind by `rfl` (word-invariance)
  - Pure-discourse model (`DiscourseStatus → Nat`) cannot reproduce the 4-way gradient shift rate
  - CCG `ShiftFeature` conflates 4 empirically distinct weight classes into 2 (pigeonhole)

## [0.222.3] - 2026-02-18

### Added
- Add `Phenomena/WordOrder/Studies/ArnoldEtAl2000.lean` — corpus data from Arnold, Wasow, Losongco & Ginstrom (2000) "Heaviness vs. Newness": dative alternation (N=637), NP shift (N=307), Table 1 mean NP lengths, gradient shift rates by word count, logistic regression factor results, `DiscourseStatus` bridge

## [0.222.2] - 2026-02-17

### Added
- Add `Phenomena/Ellipsis/Studies/AnandHardtMcCloskey2021/` — corpus data (4,700 sluices) and SIC bridge theorems connecting empirical mismatch distributions to argument domain predictions
- Add `WhSemanticType` to `Core/Basic.lean` — 7-way wh-phrase taxonomy (entity, degree, reason, manner, temporal, locative, classificatory) motivated by Santa Cruz Sluicing Corpus
- Add `assignedCase : Option UD.Case` to `HeadPair` in `FormalMatching.lean`, closing the case-matching gap: dative ≠ accusative now blocks `structurallyIdentical`
- Add case mismatch theorems to `FormalMatching.lean` (`case_mismatch_not_identical`, `case_mismatch_blocks_sluicing`, `case_match_licenses_sluicing`)
- Add AHM2021 bibliography entry with `@cite` cross-reference

### Changed
- Split `QuestionType.whyHow` into `.whReason` and `.whManner` with `whSemanticType` mapping
- Delete `Phenomena/Ellipsis/Minimalism_SluicingBridge.lean` (fake string-returning bridge); real SIC bridge theorems now live in `Studies/AnandHardtMcCloskey2021/Bridge.lean`

## [0.222.0] - 2026-02-17

### Added
- Add `Core/BToM.lean` — Bayesian Theory of Mind (Baker et al. 2017) generative model with joint score, world/belief/desire marginals, and world-marginal factoring theorem
- Add `Comparisons/ProjectionMechanisms.lean` — comparison of compositional filtering (Heim 1983, Schlenker 2009) vs RSA BToM (Scontras & Tonhauser 2025) for presupposition projection
- Add `Fragments/Yoruba/FocusParticles.lean` — Yorùbá focus particles across dialects (ni, ín) with head-direction contrast and FOFC relevance
- Add `Phenomena/Conditionals/Studies/EvcenBaleBarner2026/` — conditional perfection data and bridge (QUD effects, speaker knowledge, exhaustification)
- Add `Theories/Semantics/Conditionals/Exhaustivity.lean` — answer-level exhaustification account of conditional perfection (von Fintel 2001)
- Add generic attitude verb infrastructure in `RSA.BToM` namespace (HasComplement, HasBelief, HasAntecedent typeclasses; factive/non-factive verb semantics; condOp)

### Changed
- Ground RSA L1 in BToM: `L1_world`, `L1_beliefState`, `L1_goal` now defined via BToM marginals with equivalence theorems (`L1_world_score_eq_worldMarginal`, `L1_goal_score_eq_desireMarginal`, `L1_beliefState_score_eq_beliefMarginal`)
- Factor S1 into `S1_score` total function; add `toBToM`, `L1_joint_score`, `L1_world_score`, `L1_beliefState_score`, `L1_goal_score` as BToM-grounded score functions
- Prove `L1_world_score_factors`: world prior factors out of L1's world inference (Bayes' rule corollary)
- Move `HeadDirection` from `Phenomena/WordOrder/Typology.lean` to `Core/Basic.lean`
- Move `FIPApplication` from `Phenomena/Focus/Basic.lean` and `Theories/Semantics/Focus/Interpretation.lean` to `Core/InformationStructure.lean`
- Add BToM bridge theorems for Scontras & Tonhauser 2025 (`know_is_factive`, `think_is_nonFactive`, `qud_matches_btom`, `assumesC_matches_generic`)
- Add `@cite` tags to Cacchioli 2025 and Scontras & Tonhauser 2025
- Update bibliography with Cacchioli 2025 and Tsilia, Zhao & Sharvit 2026

## [0.221.3] - 2026-02-17

### Added
- Add `Fragments/Tigrinya/ClausePrefixes.lean` — four clausal prefix entries (zɨ-, kɨ-, kəmzi-, ʔay-...-n) with head categories, clause types, agreement properties, and discontinuity marking
- Add `Phenomena/Complementation/Studies/Cacchioli2025/Data.lean` — empirical data: co-occurrence restrictions, verb class selection, agreement asymmetry
- Add `Phenomena/Complementation/Studies/Cacchioli2025/Bridge.lean` — bridge theorems connecting Fragment entries to EP hierarchy (fValue ordering), CTPClass selection, and circumfix realization
- Prove `prefixes_distinct_flevels`: Neg(2) < Fin(3) < Rel(5) < Force(6)
- Prove `all_cooccurrences_ungrammatical`: complementary distribution of prefixes
- Prove `all_prefixes_verbal`: all four heads in the verbal extended projection

## [0.221.2] - 2026-02-17

### Added
- Add `Theories/Morphology/Core/Circumfix.lean` — theory-neutral `CircumfixExponence` structure for discontinuous morphology (prefix + stem + suffix)
- Bridge theorems connecting to `AttachmentSide.circumfix` from Core/MorphRule
- German past participle `ge-...-t` example with surface form verification

## [0.221.1] - 2026-02-17

### Added
- Add `finite`, `factive`, `neg`, `rel` to `FeatureVal` — clause-typing features for Rizzi's (1997) split-CP and Pollock's (1989) split-IP
- Add `finAgreeFeatures`, `forceFinAgreeFeatures`, `negAgreeFeatures`, `relAgreeFeatures` — Agree configurations for clause-typing
- Add `Phenomena/Complementation/Studies/Cacchioli2025/SelectionBridge.lean` — bridges CTPClass (Noonan 2007) to FeatureVal via `ctpToFiniteness` and `ctpToFactivity`
- Prove `irrealis_always_nonfinite`: irrealis CTP classes always select [-finite]

## [0.221.0] - 2026-02-17

### Added
- Add `Force`, `Neg`, `Mod`, `Rel`, `Pol` to `Cat` — five new functional heads for cartographic syntax
  - Force (Rizzi 1997): clause-typing head, fValue 6 (same as C when unsplit)
  - Neg (Pollock 1989; Zanuttini 1997): negation head, fValue 2 (IP-internal)
  - Mod (Cinque 1999): modality head, fValue 2 (IP-internal)
  - Rel (Rizzi 2001): relativization head, fValue 5 (topic field)
  - Pol (Laka 1990): polarity head, fValue 2 (IP-internal)
- Add `negVerbalEP` and `fullRizziLP` EP spines with consistency/monotonicity theorems
- Add `force_equals_c_fvalue`, `neg_in_inflectional_domain`, `new_heads_verbal` theorems
- Update `catFeatures`, `fValue`, `catFamily`, `epSemanticType`, `argumentDomainCat` for new heads

### Changed
- Remove `#eval` test sections from ExtendedProjection/Basic.lean and Properties.lean — all checks are now theorems

## [0.220.0] - 2026-02-17

### Changed
- Fix fValue collapse in split-CP: Fin(3), Foc(4), Top(5), C(6), SA(7) — previously Fin/Foc/Top/C all mapped to 3, making the formalization unable to distinguish well-formed C-domain orderings from pathological ones
- Add split-CP verbal EP spine `splitCPVerbalEP` with consistency and monotonicity theorems
- Add split-CP EP-internal relation theorems: `fin_internal_to_foc`, `foc_internal_to_top`, `top_internal_to_c`, `t_internal_to_fin`
- Add `fin_foc_not_perfect` and `reverse_splitCP_not_monotone` — negative results that were incorrectly positive before the fix
- Update SpeechActs.lean fValue comments to reflect new values

## [0.219.18] - 2026-02-17

### Changed
- Add `DepTree.WF` structure bundling `uniqueHeads`, `depIdx_lt`, `headIdx_lt` — reduces hypothesis threading in DG proofs
- Refactor `parentOf_of_edge_uh`, `dominates_iterParent_uh`, `dominates_antisymm`, `dominates_comparable`, `projection_disjoint_of_disjoint`, `escape_gives_crossing`, `interleaving_not_planar`, `planar_implies_wellNested`, `projective_implies_planar` to use `DepTree.WF`
- Extract `iterParent_chain_mem_projection` and `iterParent_chain_linked` from inline `have` blocks in `escape_gives_crossing` to standalone private theorems
- Delete unused `dominates_parent_step` and `dominates_has_incoming`
- Remove `Bool.not_eq_false_eq_true` helper; use `simp` + case split instead

## [0.219.17] - 2026-02-17

### Changed
- Close last DG sorry: prove `planar_implies_wellNested` (Kuhlmann & Nivre 2006, Theorem 1) — planar trees with unique heads are well-nested
  - `escape_gives_crossing`: parent chain walking + discrete IVT to find boundary-crossing edges
  - `interleaving_not_planar`: interleaving disjoint projections force crossing edges (6-case analysis on spanning edge intervals)
  - `crossing_edges_not_planar`: 4-point crossing witness implies ¬planar
  - `dominates_comparable`: two ancestors of the same node are comparable under dominance
  - `projection_disjoint_of_disjoint`: disjoint nodes have disjoint projections
  - `exists_spanning_edge`, `exists_spanning_edge_down`, `exists_spanning_edge_up`: induction on dominance to find linked edges spanning a position
  - `find_exit_step`, `find_entry_step`: discrete IVT helpers
  - `linked_symm_val`, `disjoint_symm`: symmetry lemmas
- Make `parentOf_uh`, `iterParent_uh`, `parentOf_of_edge_uh`, `dominates_iterParent_uh`, `iterParent_chain_bound` public in `Basic.lean`
- Remove unused `isAcyclic` hypothesis from `planar_implies_wellNested` — proof only requires `hasUniqueHeads`

## [0.219.16] - 2026-02-17

### Added
- `Core/DimensionBridge.lean`: Theory-neutral cross-dimension bridge with three levels of unification
  - `MereoTag` enum (qua/cum): binary mereological classification shared across all four frameworks
  - `LicensingPipeline` typeclass: maps any classification type to `Boundedness`, with `universal` theorem proving framework-independent licensing
  - `LicensingPipeline` instances: `Boundedness`, `MereoTag`, `BoundaryType` (theory-neutral)
  - `DimensionChain` structure: first-class two-leg pipeline Source →f Inter →μ Measure with `MereoDim` on both legs
  - `DimensionChain.composed`, `qua_transfer`, `qua_transfer_leg₁`, `qua_transfer_leg₂`: generic QUA pullback through chains
  - `cum_exceeds_source`: CUM + fresh incomparable element → strictly larger measure (structural "CUM → open scale")
  - `cum_measure_unbounded`: CUM + disjoint fresh supply with minimum measure δ → measurement unbounded (proved via Archimedean ℚ; original `¬ y ≤ x` hypothesis strengthened to `¬ Overlap x y ∧ δ ≤ μ y` after discovering convergent-increment counterexample)
  - `boundaryTypeToBoundedness`, `four_frameworks_agree`, `sumHom_qua_pullback_pattern`/`sumHom_cum_pullback_pattern`, named licensing theorems
- `Events/DimensionBridge.lean`: Theory-specific commutativity diamond + concrete dimension chains
  - `LicensingPipeline` instances: `Telicity`, `VendlerClass`, `PathShape`
  - `vendler_comm`, `pathShape_comm`: commutativity squares (two paths to Boundedness agree)
  - `commutativity_diamond`: all six classification paths converge at same licensing prediction
  - `temporalChain`, `spatialChain`, `objectChain`: concrete `DimensionChain` instantiations for τ/σ/θ
  - `temporal_qua_licensed`, `spatial_qua_licensed`, `object_qua_licensed`: end-to-end QUA transfer
  - `dimension_irrelevance`: licensing depends only on QUA/CUM, not on which dimension chain

## [0.219.15] - 2026-02-17

### Added
- `Core/Path.lean`: Spatial path infrastructure — `Path` type (directed trajectory between locations), `PathShape` enum (bounded/unbounded/source PP classification from Zwarts 2005), and `PathShape.toBoundedness` bridge to `Core.Scale.Boundedness`
- `Events/SpatialTrace.lean`: Spatial trace function σ — the third Krifka/Zwarts dimension alongside τ (temporal) and θ (object)
  - `SpatialTrace` class: σ as sum homomorphism from events to paths
  - `instIsSumHomσ`: `IsSumHom` instance for σ (parallels `instIsSumHomRuntime` for τ)
  - `σ_mereoDim`: injective σ is a `MereoDim` (enables QUA pullback)
  - `bounded_path_telic`: QUA path predicate → QUA VP (Zwarts 2005: bounded PP → telic VP)
  - `unbounded_path_atelic`: CUM path predicate → CUM VP (unbounded PP → atelic VP)
  - `pathShapeToTelicity`: PathShape → Telicity bridge
  - `telicity_boundedness_agree`: telicity ↔ scale licensing agreement
  - `LevinClass.pathSpec`: motion verb path annotations (inherently directed → bounded, leave → source, manner-of-motion → neutral)

## [0.219.14] - 2026-02-17

### Changed
- Factor `LaxMeasureSquare` out of `GRADSquare`: general mereological square (proportional extensive measures + MereoDim + QUA pullback) now lives in `Core/MereoDim.lean` §10; `GRADSquare` extends it with SINC only
- Move `MeasureProportional` from `Krifka1998.lean` to `Core/MereoDim.lean` §9 (general proportionality structure, not SINC-specific)
- Redefine `GRADSquare extends LaxMeasureSquare` in `Krifka1998.lean`; derived theorems delegate to `toLaxMeasureSquare`

### Added
- `LaxMeasureSquare` in `Core/MereoDim.lean` §10: lax commutative square of mereological dimensions with `ExtMeasure` on both arms
- `LaxMeasureSquare.laxCommutativity`: the defining equation `μ₂(f(e)) = rate * μ₁(x)` for R-pairs
- `LaxMeasureSquare.mereoDim₁`/`mereoDim₂`: both arms are `MereoDim`
- `LaxMeasureSquare.qua_pullback₂`: QUA pullback through the composed path

## [0.219.13] - 2026-02-17

### Changed
- Close `iterParent_chain_bound` sorry in `DG/Core/Basic.lean`: pigeonhole-based proof that parent-pointer chains of length > n revisit a node, using `nodup_bound` and `ofFn_nodup_of_injective`
- Close `dominates_antisymm` sorry in `DG/Core/Basic.lean`: full proof that dominance is antisymmetric in well-formed trees (unique heads + acyclic + bounded depIdx)
- Improve `planar_implies_wellNested` docstring in `NonProjective.lean` with detailed proof sketch identifying required infrastructure (projection disjointness, subtree connectivity, discrete IVT)

### Added
- Parent-pointer tracing infrastructure in `DG/Core/Basic.lean`: `parentOf_uh`, `iterParent_uh`, `iterParent_add_uh`, `follow_visited_uh`, `follow_step_uh`, `follow_no_parent_uh`, `follow_false_mono`, `follow_false_mono_gen`, `follow_false_of_chain_revisit`, `follow_false_of_cycle`, `isAcyclic_follow_uh`, `parentOf_eq_find_uh`, `parentOf_of_edge_uh`, `dominates_iterParent_uh`, `dominates_depIdx_lt`, `iterParent_chain_lt`
- `nodup_bound`: pigeonhole principle for bounded nodup lists
- `ofFn_nodup_of_injective`: `List.ofFn` of injective function is nodup

## [0.219.12] - 2026-02-17

### Added
- `GRADSquare` structure in `Krifka1998.lean` §6b: bundles lax commutative diagram (two dimension chains Events→ℚ via object and temporal paths) with SINC + extensive measures
- `GRADSquare.laxCommutativity`: the defining equation `dur(τ(e)) = rate * μ_obj(x)` for θ-pairs
- `GRADSquare.grad`: GRAD derived self-contained from the square
- `GRADSquare.objMereoDim`/`evMereoDim`: both arms are `MereoDim`
- `GRADSquare.qua_pullback_ev`: QUA pullback through the temporal path
- `krifkaGRADSquare`: canonical instantiation for `Ev Time` in `Krifka1989.lean` §6
- `durationMeasure_eq_comp`, `krifka_lax_commutativity`: helpers for the canonical case

## [0.219.11] - 2026-02-17

### Added
- `MereoDim` typeclass in `Core/MereoDim.lean` §5: morphism class of Mereo^op wrapping `StrictMono` for typeclass dispatch
- `instMereoDimOfExtMeasure`: automatic `MereoDim` instance for any `ExtMeasure` (§6)
- `MereoDim.ofInjSumHom`: manual constructor from `IsSumHom` + `Injective` (§6)
- `MereoDim.comp`: composition theorem for dimension chains (§7)
- `qua_pullback_mereoDim`/`qua_pullback_mereoDim_comp`: typeclass-dispatched QUA pullback (§8)
- `instIsSumHomRuntime`: `IsSumHom` instance for τ in `Events/Mereology.lean`, enabling automatic `cum_pullback`
- Re-export MereoDim typeclass and pullback theorems via `Events.Mereology`

## [0.219.10] - 2026-02-17

### Changed
- Merge pullback theorems (qua_pullback, cum_pullback, singleton_qua, extMeasure_strictMono, IsSumHom.strictMono_of_injective, etc.) from `Core/Dimension.lean` into `Core/Mereology.lean` §8–12
- Rename `Core/Dimension.lean` → `Core/MereoDim.lean`: home for the mereological dimension category (Mereology ↔ MeasurementScale bridge, future MereoDim/JoinDim/ExtDim typeclasses)
- Simplify `Events/Mereology.lean` re-export block with section comments

## [0.219.9] - 2026-02-17

### Added
- MeasurementScale bridge in `Core/Dimension.lean` §9–12: connect Mereology ↔ MeasurementScale pillars
- `quaBoundedness`/`cumBoundedness`: mereological annotations mapping QUA → `Boundedness.closed`, CUM → `Boundedness.open_`
- `extMeasure_kennedyMIP`/`extMeasure_rouillardMIP`: ExtMeasure → MIPDomain constructors
- `singleton_qua_closed`/`extMeasure_singleton_closed`: singleton QUA ↔ closed scale bridge
- `cum_sum_exceeds`/`cum_sum_exceeds_both`: CUM sum extensibility (mechanism behind open scales)
- Re-export MeasurementScale bridge theorems via `Events.Mereology`

## [0.219.8] - 2026-02-17

### Added
- `IsSumHom.strictMono_of_injective`: bridge from IsSumHom + Injective to StrictMono (Dimension.lean §6)
- `qua_of_injective_sumHom`: functional QUA propagation as `qua_pullback` instance (Dimension.lean §7)
- `cum_qua_dimension_disjoint`: CUM/QUA incompatibility preserved through dimension maps (Dimension.lean §8)
- Docstring cross-references in Krifka1998.lean linking relational `qua_propagation` to functional `qua_pullback`
- Re-export new dimension theorems via `Events.Mereology`

## [0.219.7] - 2026-02-17

### Added
- Add `Core/Dimension.lean`: mereological dimension infrastructure — QUA and CUM as contravariant functors on Mereo^op
- `qua_pullback`: QUA pullback along StrictMono maps (general theorem subsuming `extMeasure_qua`)
- `cum_pullback`: CUM pullback along IsSumHom maps (wrapper for `IsSumHom.cum_preimage`)
- `extMeasure_strictMono`: bridge from ExtMeasure to StrictMono
- `singleton_qua`: singletons are QUA on any PartialOrder (generalizes `atom_qua`)
- `extMeasure_qua'`: derive `extMeasure_qua` as corollary of `qua_pullback` (no positivity hypothesis needed)
- `qua_pullback_comp`: composition principle for QUA pullback (Krifka dimension chains)
- Re-export dimension theorems via `Events.Mereology`

## [0.219.6] - 2026-02-17

### Added
- Formalize Turk, Hirsch & İnce (2026) category match constraint for Turkish polar questions
- Add `CatItem` and `categoryMatchAlts`/`typeTheoAlts` to `Core/Alternatives.lean`, grounded in `UD.UPOS`
- Add `QParticleLayer.polP` for clause-internal polarity heads
- Add `Fragments/Turkish/QuestionParticles.lean`: Turkish *mI* particle entry (UPOS `PART`, layer `polP`)
- Add Turkish polar QA-pair judgments to `Phenomena/Questions/PolarAnswers.lean`
- Add `Phenomena/Questions/Studies/TurkHirschInce2026Bridge.lean`: finite 4-world scenario proving type-theoretic alternatives over-generate (admit □p) while UPOS category match yields correct {p, ¬p}

## [0.219.5] - 2026-02-17

### Changed
- Close `mem_projection_of_dominates` sorry: prove forward bridge Dominates → BFS membership
- Prove `dominates_iff_mem_projection`: full bidirectional bridge between Prop-level dominance and BFS projection
- Add BFS infrastructure: `go_mono_fuel`, `filter_split_at_node`, `go_children_complete`, `projection_closed_under_children`, `filter_length_le_of_imp`

## [0.219.4] - 2026-02-17

### Added
- Formalize Tsilia, Zhao & Sharvit (2026) "Tense and Perspective": presuppositional tense theory
- Add `Theories/Semantics/Tense/TsiliaEtAl2026.lean`: tense presuppositions, OP_π, ⌈then⌉ presupposition, PrProp bridge
- Create tense→presupposition import edge (`Core.Presupposition`)
- Add `thenPresentIncompatibility` to `TensePhenomenon`, `hasPresuppositionalTense` to `TenseTheory`
- Add cross-linguistic `ThenAdverb` Fragment entries for 7 languages (English, German, Mandarin, Japanese, Greek, Russian, Hebrew)
- Extend `Comparisons/TenseTheories.lean` with presuppositional comparison (10 theories)

### Changed
- Rename `Perspective.lean` → `ParticipantPerspective.lean` to disambiguate participant perspective (Lakoff 1970) from temporal perspective (π)
- Refactor `ThenPresentBridge.lean`: move `ThenAdverb` type to `Basic.lean`, move per-language entries to Fragment files

## [0.219.3] - 2026-02-17

### Added
- Formalize Zhao (2026) cross-domain parallels: ATOM-DIST, degree events, then-present puzzle
- Add `Core/AtomicDistributivity.lean`: domain-parameterized ATOM-DIST_α (Zhao Def. 5.3), EvQuant, antiAtomDistLicensed
- Add `Theories/Semantics/Events/DegreeEvents.lean`: DegreeEv with degree trace τ_d, ComparisonRole ([STD], [TAR], [DIFF])
- Add `Fragments/Mandarin/AspectComparison.lean`: cross-domain particles le, guo, mei-you with NOT-ATOM-DIST_α licensing
- Add `Phenomena/Aspect/CrossDomainBridge.lean`: VendlerClass ↔ ATOM-DIST_t bridge, le licensing prediction
- Add `Phenomena/Tense/ThenPresentBridge.lean`: then-present incompatibility theorem via Kiparsky's perspective parameter

## [0.219.2] - 2026-02-17

### Fixed
- Close `depth_fuel_step`, `depth_le_of_edge`, `dominates_depth_le` sorrys in DG/Core/Basic.lean
- Add `hasUniqueHeads_count` helper theorem extracting per-node count predicate from `hasUniqueHeads`
- Close `unique_parent_of_hasUniqueHeads` sorry in NonProjective.lean
- Close `projective_implies_planar` proof (4-case analysis using interval lemmas + dominance antisymmetry)
- Add `.gitignore` entry for `scratch/` test directory
- Improve `dominates_antisymm` sorry documentation with concrete `follow`-based proof approach

## [0.219.1] - 2026-02-17

### Changed
- **Revise Warstadt (2022) formalization**: Replace invented possessive example with paper's actual green card (Table 1) and family-genus-species (Table 2) examples, following Data/Bridge pattern
- Add `Phenomena/Presupposition/Studies/Warstadt2022.lean` (theory-neutral data: GCWorld, FGSWorld, truth conditions, priors, QUDs)
- Add `Phenomena/Presupposition/RSA_Warstadt2022Bridge.lean` (RSA computation, predictions, PrProp connection)
- Delete old `Theories/Pragmatics/RSA/Implementations/Warstadt2022.lean`
- Add `projectionL1_context` and `projectionL1_world` helpers to `RSA.Eval` to reduce boilerplate in projection models
- Simplify call sites in QingEtAl2016, ScontrasTonhauser2025, and Warstadt bridge
- Align bridge file namespaces to file locations (`Phenomena.Presupposition.Warstadt2022Bridge`, `Phenomena.Presupposition.HeKaiserIskarous2025Bridge`)
- Delete empty HKI stub from `Theories/Pragmatics/RSA/Implementations/`
- Update Compare.lean imports and docstrings for new Warstadt domain

### Fixed
- Fix doc-gen4 CI: use `lake exe doc-gen4` instead of hardcoded binary path

## [0.219.0] - 2026-02-16

### Changed
- **Reorganize Comparisons/ directory**: Comparisons/ now contains only pure metatheory (13 files); 14 phenomenon-anchored comparison files moved to `Phenomena/{Category}/Compare.lean`
- Move `ThresholdSemantics.lean` from Comparisons/ to `Theories/Semantics/Probabilistic/SDS/` (was a dependency violation: Theories/ imported from Comparisons/)
- Extract `EmbeddedSI.lean` (shared types: `EmbeddedSIWorld`, `EmbeddedSIMessage`, `embeddedMeaning`, `ExhScope`, `globalExhMeaning`, `localExhMeaning`) into `Theories/Pragmatics/RSA/Core/` to fix dependency violation where `CompositionalRSA.lean` imported from Comparisons/
- Update `RSAExhExpressivity.lean` to import extracted types from `RSA.Core.EmbeddedSI`
- Update `CompositionalRSA.lean` to import `RSA.Core.EmbeddedSI` instead of `Comparisons.RSAExhExpressivity`
- Files moved: `ScalarImplicature` → `ScalarImplicatures/CompareAgreement`, `Implicature` → `ScalarImplicatures/Compare`, `CausativeAlternation` → `Causatives/Compare`, `BeforeAfter` → `Tense/Compare`, `ScopeFreezing` → `Quantification/Compare`, `CumulativeReadings` → `Plurals/Compare`, `Islands` → `FillerGap/Compare`, `NumeralSalience` → `Numerals/Compare`, `PolarQuestions` → `Questions/Compare`, `KindReference` → `Generics/Compare`, `FreeChoice/Compare` → `Modality/CompareFC`, `FreeChoice/Aloni2022` → `Modality/Aloni2022`, `PresuppositionProjection` → `Presupposition/Compare`, `ResultativeArgLicensing` → `ArgumentStructure/Compare`
- Update all namespaces, imports, and cross-references in moved files and consumers

## [0.218.25] - 2026-02-16

### Fixed
- Close `hasMultiplePronunciations` sorry in Amalgamation.lean: define via `subterms` count (copy theory — multiple occurrences = verb doubling)
- Close `isComplexMorphologicalWord` sorry in Amalgamation.lean: define via `LexicalItem.isComplex` on leaf tokens
- Fix `projective_implies_planar` and `planar_implies_wellNested` in NonProjective.lean: add required `hasUniqueHeads` hypothesis (original statements were false without it; counterexample: 4-node multi-headed graph)
- Add `root_mem_projection`, `interval_mem_of_range`, `interval_mem_between` lemmas to DG/Core/Basic.lean (discrete IVT for sorted interval lists)
- Improve sorry documentation for `isCatena_iff_IsCatena` in Catena.lean with detailed proof sketch and identified blockers

## [0.218.24] - 2026-02-16

### Changed
- **Variable BEq is now lawful by construction**: derive `BEq` from `DecidableEq` instead of from `String.BEq`, eliminating `Variable.beq_def` theorem entirely (`(a == b) = decide (a = b)` is now `rfl`)
- Move `Situation.extend_hasValue_same/diff` to Core/Causation.lean as `@[simp]` lemmas
- Move `Situation.trueLE` ordering and `isPositiveDynamics` to Core/Causation.lean for reuse across Sufficiency, Necessity, and Ability modules
- Remove `Variable.beq_def` from all simp sets (no longer needed with lawful-by-construction BEq)

## [0.218.23] - 2026-02-16

### Fixed
- Close `sufficiency_monotone_positive` sorry in Causation/Sufficiency.lean: monotonicity of causal sufficiency for positive dynamics via trueLE ordering on situations, with 15 supporting lemmas
- Add `isPositiveDynamics` predicate and positivity proofs for all standard constructors (simple, conjunctive, disjunctive, chain)
- Remove `@[simp]` from `Variable.beq_def` to fix simp loop
- Close `dep_length_ge_one_plus_intervening` sorry in HarmonicOrder.lean via `chain_length_le_range` + `Pairwise.filter`
- Close `exists_catena_not_constituent` sorry in VPDivergence.lean via `child_mem_projection`
- Add BFS infrastructure to DG/Core/Basic.lean: `go_mem_of_queue`, `projection_nodup`, `child_mem_projection`, `getLast!_mem_cons`, `chain_length_le_range`
- Improve sorry documentation for `projective_implies_planar` and `planar_implies_wellNested` in NonProjective.lean

## [0.218.22] - 2026-02-16

### Fixed
- Add `LawfulBEq Variable` instance and `Variable.beq_def` simp lemma to Core/Causation.lean
- Close 3 sorry's in Causation/Sufficiency.lean: `disjunctive_each_sufficient`, `conjunctive_neither_sufficient_alone`, `conjunctive_sufficient_with_other` via normalDevelopment fixpoint proofs
- Close `single_cause_perfection` sorry in Causation/Integration.lean: sufficiency implies necessity in single-cause models
- Close `pump_breaks_anbncndn` sorry in FormalLanguageTheory.lean: pumping down {aⁿbⁿcⁿdⁿ} breaks symbol count equality via contiguity argument (.a and .d separated by 2p positions)
- Close `anbnc_not_pumpable` sorry in FormalLanguageTheory.lean: {aⁿbⁿcⁿ} is not context-free via 3-symbol pumping lemma with 8 helper lemmas
- Add `LawfulBEq ThreeSymbol` instance for 3-symbol pumping proof
- Close 3 sorry's in HarmonicOrder.lean: `chain_tdl_ge_span` (triangle inequality via foldl_min_assoc), `monotone_ascending_achieves_span`, `consecutive_tdl` (via List.range' induction)

## [0.218.21] - 2026-02-16

### Fixed
- Close `makeString_in_language` sorry (filter/replicate helper lemmas + `LawfulBEq FourSymbol`)
- Add `singleton_isCatena` theorem + `mem_go_of_mem_visited` BFS helper to Catena.lean
- Fix `exists_catena_not_constituent` statement: remove vacuous `SimpleGraph` parameter, use Bool-level `isCatena`

## [0.218.20] - 2026-02-16

### Fixed
- Fix pumping lemma: replace unsound axiom with `HasPumpingProperty4` def, fix ∀→∃ quantifier in `anbncndn_not_pumpable`
- Strengthen `dep_length_eq_one_plus_intervening` to `dep_length_ge_one_plus_intervening` (= → ≥, equality only holds without sibling subtrees)
- Close `leaf_no_subtree_members` and `leaf_no_intervening` sorrys via new `projection_of_no_children` lemma
- Fix `projection_of_leaf` Lean 4.28 breakage (`ite_false` simp regression), delegate to `projection_of_no_children`
- Fix bibliography source links for moved RSA implementation files

## [0.218.19] - 2026-02-16

### Changed
- Standardize bridge file naming: rename 65 `Bridge_*` prefix files to `*Bridge` suffix convention (Lean/Mathlib style)

## [0.218.18] - 2026-02-16

### Changed
- Phenomena migration: move 7 author-named files into Studies/ subdirectories (Sag2010, FutrellEtAl2020, HahnDegenFutrell2021, ClausWalch2024, WoodinEtAl2024, HuangSpelkeSnedeker2013, VonFintel1999)
- Flatten MeasurePhrases/ into Quantification/, ConditionalModality/ into Modality/, CzechThreeWayNeg/ into Negation/
- Rename Gradability/Basic.lean → Data.lean
- Fix mislabeled files: add Bridge suffix to PracticalReasoning, InformationalBackgrounds, ConditionalModality Data
- Remove orphaned Tense/Cumming2026/ and Tense/Lakoff1970/ duplicates

## [0.218.17] - 2026-02-16

### Fixed
- Fix remaining Lean 4.28 build failures: add `Mathlib.Tactic.DeriveFintype` (9 files), `Mathlib.Tactic.Ring` (2 files)
- Commit all unstaged changes from previous sessions

## [0.218.16] - 2026-02-16

### Fixed
- Close `softmax_uniform_limit` sorry: prove α=0 softmax yields uniform distribution (fix Nat/ℚ division in statement)

## [0.218.15] - 2026-02-16

### Fixed
- HigherOrder.lean: restore `saw'` relation via tower-type GQs (`TowerGQ`), replacing vacuous `HODGQ`-based theorem with substantive derivation matching `cumulative` from Basic.lean
- Analyticity.lean: add von Fintel nonemptiness presupposition to `butExceptive`, close `someBut_LContradiction` sorry (was provably false without it), complete `everyBut_not_LAnalytic` proof

## [0.218.13] - 2026-02-16

### Fixed
- Fix build failures from Lean 4 v4.28.0-rc1 API changes
  - Distribution.lean: add missing `Mathlib.Algebra.Order.BigOperators.Group.Finset` import
  - PragmaticAnswerhood.lean: adapt to implicit `List.mem_cons_self` args, switch `eraseDups` → Mathlib `dedup` (with `nodup_dedup`/`mem_dedup`), fix `Nat.ble_eq` → `decide_eq_true`
  - RSA Basic.lean: replace `linarith` with `exact add_nonneg` for cost nonnegativity
- Close two `sorry`s in Builder.lean (`assertsSufficiency_iff_makeSem`)
- Close `sorry` in AntiAdditivity.lean (`atMost_not_antiAdditive`) with concrete counterexample using `atMost 1`

## [0.218.4] - 2026-02-16

### Changed
- Merged `Theories/Morphology/{Tense,Aspect,Number,Degree}.lean` → `Theories/Morphology/Exponence.lean`

## [0.218.3] - 2026-02-16

### Changed
- Flattened `Theories/Morphology/Diagnostics/CliticVsAffix.lean` → `Theories/Morphology/CliticVsAffix.lean`
- Moved `Theories/Syntax/Minimalism/Morphology/Fission.lean` → `Theories/Morphology/DM/Fission.lean`

## [0.218.2] - 2026-02-16

### Changed
- Moved `ProcessingModel.lean` back to `Core/` (framework-agnostic infrastructure)

## [0.218.1] - 2026-02-16

### Changed
- Consolidated `Core/Interfaces/` (7 files) → `Core/Interface.lean` (single file)
- Moved `Core/Morphology/{Aspect,Degree,Number,ScaleFromParadigm,StemToLex,Tense}.lean` → `Theories/Morphology/`
- Flattened `Core/Morphology/MorphRule.lean` → `Core/MorphRule.lean`
- Moved `Core/Verbs.lean` → `Theories/Semantics/Lexical/Verb/VerbEntry.lean`
- Removed `Theories/Pragmatics/RSA/Implementations/CausalCorrelation.lean`
- Fixed ~30 bibliography entries after manual verification against publisher sites: corrected hallucinated titles (Scontras & Tonhauser 2025, Martin et al. 2025, Ahn & Zhu 2025, Cao et al. 2025, Warstadt 2022), wrong author names (Alsop, Cremers et al., Haslinger et al., Harding et al., Grusdt et al.), wrong journals (Sumers et al. 2024, Cummins & Franke 2021, Nouwen 2024, Franke & Bergen 2020), and wrong years (Ciardelli et al. 2018, Hintikka 1962, Krifka 2003). Removed unverifiable Goodwin et al. (2025) entry and CausalCorrelation.lean
- Rewired imports across ~40 files

## [0.218.0] - 2026-02-16

### Changed
- **Dependency discipline fully enforced**: 0 violations in Theories→Phenomena and Fragments→Phenomena directions
- Rewired all imports for the 11 bridge files moved in 0.217.6 (old Theories/ paths → new Phenomena/ paths)
- Extracted `AdjectivalConstruction` to `Theories/Semantics/Lexical/Adjective/Theory.lean` (was in `Phenomena/Gradability/Evaluativity.lean`); fixes NeoGricean Alternatives + Evaluativity violations
- Extracted `QParticleLayer` to `Theories/Semantics/Questions/QParticleLayer.lean` (was in `Phenomena/Questions/Typology.lean`); fixes 9 Fragment QuestionParticles violations
- Extracted `NegPosition`, `Diagnostic`, `licenses` to `Theories/Semantics/Polarity/CzechNegation.lean` (was in `Phenomena/Negation/CzechThreeWayNeg.lean`); fixes Czech Fragment violations
- Moved `MandarinTrigger` to `Fragments/Mandarin/Particles.lean` (was in `Phenomena/Presupposition/Studies/Wang2025.lean`)

## [0.217.6] - 2026-02-16

### Changed
- **Theories/Pragmatics/RSA/Core/Softmax/Limits.lean**: Proved `entropy_tendsto_max` (α → 0: entropy → log|U| via continuity of softmax + x·log x) and `entropy_tendsto_zero` (α → ∞: entropy → 0 via negMulLog continuity + pointwise softmax convergence). Zero sorrys remain in Limits.lean.
- **Theories/Pragmatics/NeoGricean/Exhaustivity/Interface.lean**: Proved `ie_eq_mw_when_closed` (Spector Theorem 9: exhIE = exhMW under conjunction closure) by connecting to `theorem9_main` via propext. Changed hypothesis from binary to `closedUnderConj`. Zero sorrys remain.

## [0.217.5] - 2026-02-16

### Changed
- **Theories/Pragmatics/RSA/Core/Convergence.lean**: Proved all 3 remaining sorrys. `G_α_bounded_above` via entropy ≤ log|U| (from KL(p‖uniform) ≥ 0) + E_VL ≤ 0 (utility nonpositive for distributions). `RSA_converges` via Monotone Convergence Theorem (`monotone_nat_of_le_succ` + `tendsto_atTop_ciSup`). `eventually_εConverged` via convergent ⇒ Cauchy. Added `prior_sum` field to `RSAScenarioR`. Zero sorrys remain.

## [0.217.4] - 2026-02-16

### Added
- **blog/data/references.bib**: Centralized BibTeX bibliography (102 entries) as single source of truth for all references
- **blog/scripts/gen_bibliography.py**: BibTeX→Markdown generator with `@cite{key}` cross-referencing from Lean docstrings
- **blog/scripts/verify_bibliography.py**: Verification script that checks entries against Semantic Scholar API
- **blog/content/bibliography.md**: Generated bibliography page on the Hugo blog
- **Bibliography nav entry** in `hugo.toml` between Roadmap and API Docs
- 12 new DOIs added after Semantic Scholar verification (fox-2007, phillips-brown-2025, von-stechow-2009, kratzer-1998, krifka-2004, krifka-1989, krifka-1998, haslinger-etal-2025, montague-1973, marcolli-chomsky-berwick-2023, waldon-degen-2021, hamblin-1973)

### Fixed
- **klecha-2016**: Corrected DOI from `10.3765/sp.9.9` to `10.3765/sp.9.8` (wrong article number)

## [0.217.3] - 2026-02-16

### Changed
- **Dependency discipline**: Moved bridge code from 50 Theories/ files into 55 new Phenomena/ bridge files, eliminating Theories→Phenomena import violations. Theory files now contain only pure theory (types, operators, predicates); all code that imports both Theories/ and Phenomena/ data lives in Phenomena/ bridge files. Net effect: −4373 lines from Theories/, redistributed to Phenomena/.
- **Linglib.lean**: Removed duplicate `GibbsVariational` import

### Added
- **55 Phenomena bridge files** across 20 phenomenon categories: Anaphora (5), Aspect (1), Causatives (1), Constructions (2), Coordination (1), Ellipsis (4), Entailment (1), FillerGap (4), Gradability (3), Imprecision (1), Modality (3), Polarity (1), Politeness (1), Presupposition (5), Quantification (5), Questions (2), ScalarImplicatures (6), WordOrder (7), AdditiveParticles (1), Negation (1)
- **Phenomena/Tense/Cumming2026/Bridge.lean**: Cumming (2026) tense bridge
- **Phenomena/Tense/Lakoff1970/Data.lean**: Lakoff (1970) tense data
- **Phenomena/Aspect/Studies/AlstottAravind2026.lean**: Alstott & Aravind (2026) aspect study
- **Phenomena/Imprecision/Studies/LassiterGoodman2017.lean**: Lassiter & Goodman (2017) imprecision data
- **Phenomena/AdditiveParticles/Studies/TurcoBraunDimroth2014.lean**: Turco, Braun & Dimroth (2014) additive particle data
- **Phenomena/Negation/Studies/StankovaSimik2024.lean**: Stanková & Šimík (2024) negation data
- **Theories/Pragmatics/RSA/PhaseTransition.lean**: RSA phase transition analysis

## [0.217.2] - 2026-02-16

### Changed
- **Theories/Pragmatics/RSA/Core/Convergence.lean**: Eliminated all 5 axioms. Replaced `rsa_speaker_maximizes_G_α` and `rsa_listener_maximizes_G_α` with proved theorems using Gibbs Variational Principle and Bayesian optimality from GibbsVariational.lean. KKT axioms (`kkt_sufficiency_for_concave_on_simplex`, `kkt_sufficiency_for_concave_on_positive`) deleted — bypassed entirely. `G_α_bounded` axiom converted to sorry with proof sketch. Fixed listener proof to handle zero-prior meanings via case splitting.
- **Theories/Pragmatics/RSA/Core/GibbsVariational.lean**: Cleaned up unused variable warnings

## [0.217.0] - 2026-02-16

### Changed
- **Theories/Semantics/Compositional/ → Montague/**: Renamed to reflect Montague architecture identity. 8 core files stay (Basic, Composition, Variables, Modification, Conjunction, PTQ, Lexicon, Derivation); 7 domain-specific files relocated: Anaphora→Reference/Binding, Core/Polarity→Entailment/Polarity, Core/Time→Tense/BranchingTime, Derivation/Scope→Scope, Derivation/TruthConditions→Phenomena/Entailment/Bridge_Montague_TruthConditions, Interface/SemanticBackend→Pragmatics/RSA/Core/SemanticBackend, Interface/SyntaxInterface→Semantics/SyntaxInterface. Core/ and Derivation/ subdirectories eliminated.

## [0.216.1] - 2026-02-16

### Added
- **Theories/Pragmatics/RSA/Core/GibbsVariational.lean**: Gibbs Variational Principle and Bayesian optimality proved using Mathlib's `InformationTheory.KullbackLeibler.KLFun`. Zero sorrys. Key theorems: `kl_finite_nonneg` (via `klFun_nonneg`), `gibbs_maximizes` (softmax uniquely maximizes H(p) + α⟨p,s⟩), `bayesian_maximizes` (Bayesian posterior maximizes E[log L]).
- **Theories/Pragmatics/RSA/Core/Softmax/Basic.lean**: KL divergence infrastructure and Gibbs VP proof (self-contained, not using Mathlib InformationTheory). `klFinite`, `kl_nonneg` (via log x ≤ x−1), `log_softmax`, `gibbs_variational`, `bayesian_maximizes_expected_log` — all fully proved, zero sorrys added.
- **Theories/Pragmatics/DecisionTheoretic/Also.lean**: Also-implicature via DTS framework

### Changed
- **Theories/Pragmatics/RSA/Core/Convergence.lean**: Fixed normalization bug — `listenerUpdate` and `initRSA` now normalize listener distributions (previously returned unnormalized scores)
- **Theories/Pragmatics/DTS/ → DecisionTheoretic/**: Renamed directory for clarity (DTS files retained as aliases)
- **Dependency discipline**: Removed 3 Theories→Phenomena import violations (CCG/Intonation.lean, DependencyGrammar/Coordination.lean, DependencyGrammar/LongDistance.lean)

## [0.215.2] - 2026-02-16

### Changed
- **Core/Basic.lean**: Replaced unsound tree-free `areSisters`/`cCommands` (sisterhood held for ALL distinct pairs via `node x y` witness) with tree-relative `areSistersIn`/`cCommandsIn`/`asymCCommandsIn` that restrict witnesses to subterms of a given root. Moved general utilities from LCA.lean: `subterms`, `terminalNodes` + theorems, `containsB`/`containsB_iff`, `linearize`. Added `LIToken.phonForm` and `phonYield_eq_linearize` connecting `phonYield` and `linearize`.
- **Formal/Linearization/LCA.lean**: Unified 4 negative c-command proofs into `inner_not_cCommandsIn_outer`; unified 4 positive c-command theorems into `outer_cCommandsIn_inner_left`/`_right` (work for arbitrary SOs); unified `spec_precedes_head_complement` and `head_precedes_complement` into `outer_precedes_inner` (old names kept as aliases); removed `section SpecPrecedesHC` and redundant `hne_spec_hc` hypothesis (leaf ≠ node is derivable). LCA.lean reduced from 630 to 311 lines.
- **Core/Agree.lean**: All c-command uses (`probeCommands`, `validAgree`, `intervenes`, `closestGoal`, `MultipleAgree.isValid`, `defectivelyIntervenes`, `validAgreeWithPIC`, `fullAgree`) now take a `root : SyntacticObject` parameter and use `cCommandsIn root` instead of the unsound tree-free `cCommands`.
- **Formal/Constraints/HMC.lean**: `immediatelyCCommands` now uses `cCommandsIn root` (previously ignored its `_root` parameter). Amalgamation theorems updated accordingly.

## [0.215.1] - 2026-02-16

### Added
- **Theories/Syntax/Minimalism/Formal/Linearization/LCA.lean**: Kayne (1994) Linear Correspondence Axiom — `subterms`, `terminalNodes`, `dominatedTerminals` (Kayne's d function), tree-relative `areSistersIn`/`cCommandsIn`/`asymCCommandsIn` (needed because Basic.lean's tree-free `areSisters` makes asymmetric c-command trivially false), `lcaPrecedesIn`, `SatisfiesLCAIn`, `linearize`; `containsB`/`containsB_iff` (boolean decidable containment); theorems: `spec_precedes_head_complement` (S-H-C order), `head_precedes_complement` (head before complement internals), `no_right_specifier` (right specifiers ruled out), `adjunction_left_only` (head adjunction is left-adjunction), `sister_terminals_unordered` (sister-terminal limitation); concrete examples with `native_decide`

## [0.215.0] - 2026-02-16

### Changed
- **Theories→Phenomena dependency enforcement**: Moved 86 files out of `Theories/` that violated the `Theories → Fragments → Phenomena` dependency discipline (importing from `Phenomena/`). Files moved to `Phenomena/Syntax/`, `Phenomena/Semantics/`, and `Phenomena/Pragmatics/` preserving their relative structure. Includes RSA paper implementations, NeoGricean bridge files, syntax framework bridge files (CCG, HPSG, Minimalism, DependencyGrammar, ConstructionGrammar), and semantics bridge files (Events, Focus, Presupposition, Entailment, Questions, TypeTheoretic). Full transitive closure computed to ensure no Theories/ file transitively depends on Phenomena/. Zero remaining violations.
- **Phenomena/ study-directory cleanup**: Moved 8 top-level study-specific directories under their primary phenomenon: AlstottAravind2026→Aspect/Studies/, Charlow2021→Plurals/Studies/, Cumming2026→Tense/Studies/, Lakoff1970→Tense/Studies/, MunozPerez2026→Causatives/Studies/, StankovaSimik2024→Negation/Studies/, TurcoBraunDimroth2014→AdditiveParticles/Studies/, SpalekMcNally→ChangeOfState/Studies/.
- **Phenomena/ granularity consolidation**: Merged 17 small/specific directories into broader groupings. TemporalAdverbials+TemporalConnectives→Tense/, ActualityInferences+ConditionalModality+ModalConcord+OutlookMarkers→Modality/, Islands→FillerGap/, NonProjectivity+DependencyLength→WordOrder/, Honorifics→Politeness/, MeasurePhrases→Quantification/, ChangeOfState→Causatives/, WeakEvidenceEffect+ArgumentativeFraming→ScalarImplicatures/, NumeralModification+NumeralSemantics+NumberUse→Numerals/, Metaphor+Humor→Nonliteral/. Reduces top-level Phenomena/ entries from ~50 to ~33.

## [0.214.1] - 2026-02-16

### Added
- **Theories/Semantics/Tense/Declerck.lean**: Declerck (1991) tense theory — TO-chain architecture (`DeclercianSchema`, `TOLink`), all eight English tense schemata (preterit, present, present perfect, past perfect, future, future perfect, conditional, conditional perfect), `TimeSphere` classification, bridge theorems to `ReichenbachFrame` (with structural `eventTime_eq_refTime` invariant), temporal vagueness proofs for future perfect and conditional
- **Core/Time.lean**: `SituationBoundedness` (bounded/unbounded; Smith 1991, Depraetere 1995)

### Changed
- **Phenomena/Tense/Data.lean**: `SituationBoundedness` imported from `Core/Time.lean`; local `BoundedFrame` simplified to a plain struct (removed polymorphism); tense-sphere theorems renamed to theory-neutral names (`preterit_isPast`, `perfect_isPresent`)

## [0.214.0] - 2026-02-15

### Changed
- **Theories/ directory reorganization**: Restructured the entire `Theories/` directory into `Syntax/`, `Semantics/`, `Pragmatics/`, and `Morphology/` top-level categories. Dissolved `TruthConditional/` (72 files) and `IntensionalSemantics/` (56 files) into coherent domain-specific directories under `Semantics/` (Compositional, Intensional, Modality, Conditionals, Attitudes, Tense, Questions, Reference, Causation, Focus, Presupposition, Entailment, Mood, Lexical, Probabilistic, Dynamic, Events, TypeTheoretic). Moved syntax frameworks (Minimalism, HPSG, CCG, DependencyGrammar, ConstructionGrammar) under `Syntax/`. Moved pragmatic frameworks (RSA, NeoGricean, DTS) under `Pragmatics/`. ~414 files moved, ~1200 import statements rewritten.
- **Namespace alignment**: Renamed all internal `namespace`, `open`, `end`, and qualified references to match the new directory structure. `TruthConditional.*` → `Semantics.Compositional.*`/`Semantics.Lexical.*`/etc., `IntensionalSemantics.*` → `Semantics.Modality.*`/`Semantics.Attitudes.*`/etc., `QuestionSemantics` → `Semantics.Questions`, `DynamicSemantics` → `Semantics.Dynamic`, `EventSemantics` → `Semantics.Events`, `TTR` → `Semantics.TypeTheoretic`, `SDS` → `Semantics.Probabilistic.SDS`. ~1000 additional replacements across ~370 files.

## [0.213.31] - 2026-02-15

### Added
- **Theories/DTS/Core.lean**: Decision-Theoretic Semantics core (Merin 1999) — `Issue`, `DTSContext`, `condProb`, `bayesFactor`, `posRelevant`/`negRelevant`/`irrelevant`, `CIP`, `pxor`; Corollary 3 (sign reversal), Fact 5 (CIP multiplicativity), Theorem 6b (XOR counterexample via `native_decide`)
- **Theories/DTS/ScalarImplicature.lean**: DTS scalar implicature — `sgnRelevance` (PSM), `upwardCone`/`downwardCone`, `ScalarInterpretation`; Predictions 1–2 (conjunction dominates disjunction)
- **Theories/DTS/But.lean**: DTS "but" semantics — `butFelicitous` (Hypothesis 4), `NNIR` (Def. 10), `defaultBut`; Theorems 8–10 (CIP + contrariness → unexpectedness), Corollary 11 (Harris universal)
- **Theories/DTS/Even.lean**: DTS "even" semantics — `evenFelicitous` (Hypothesis 5); Prediction 3 (`but_even_incompatible` proved via `linarith`)

## [0.213.30] - 2026-02-15

### Changed
- **Core/ProcessingModel.lean**: Proved all 4 monotonicity theorems (`locality_monotone`, `boundaries_monotone`, `referentialLoad_monotone`, `ease_monotone`) — Pareto dominance prevents easier/harder classification when a single dimension worsens/improves
- **Core/Proposition.lean**: Proved `FiniteWorlds.ofFintype` and `FiniteWorlds.toFintype` — complete bridge between Mathlib `Fintype` and linglib `FiniteWorlds` conventions

## [0.213.29] - 2026-02-15

### Added
- **Phenomena/ScalarImplicatures/Studies/MeyerFeiman2021.lean**: Meyer & Feiman (2021) "Composing Alternatives" — `ProcessProfile` (ALT-GEN × ALT-NEG decomposition), `ScalarItemClass` (quantifier/numeral/FC), `PrimingExperiment` (6 experiments), `TheoreticalPosition` falsification; connects to existing Horn scale data and FC phenomena
- **Phenomena/ScalarImplicatures/Studies/MeyerFeiman2021Bridge.lean**: Per-experiment verification theorems (`all_experiments_match`), falsification theorems (`exactly_one_survives`), connections to Hurford rescue (offline ALT-GEN enables immediate exhaustification), connections to FC phenomena (innocentInclusion vs exhaustification), `all_profiles_distinct`

## [0.213.28] - 2026-02-15

### Added
- **Core/DecisionTheory.lean**: `maximinUtilityValue_monotone_cell` (MUV anti-monotone in cell containment), `questionMaximin_le_muv` (questionMaximin ≤ MUV of any member cell), `le_foldl_min` (made public); `securityLevel_le_utility`, `securityLevel_subset_ge`, `maximinValue_subset_ge`, foldl min/max helpers — full monotonicity infrastructure for maximin decision theory
- **Core/Partition.lean**: `toCells_cell_nonempty` (each cell in toCells has a representative in elements), `toCells_nonempty` (toCells of nonempty list is nonempty), `toCells_fine_sub_coarse` (refinement implies fine cells are subsets of coarse cells)

### Changed
- **GSVanRooyBridge.lean**: `blackwell_maximin_forward` fully proved (was sorry) — refinement implies maximin dominance, via cell monotonicity + partition nonemptiness
- **Core/DecisionTheory.lean**: Removed false `questionUtility_nonneg` (correct QUD-specific version in Partition.lean); fixed `maximinUtilityValue_nonneg` to require nonemptiness hypothesis; Lean 4.28 API compatibility fixes throughout
- **QuestionSemantics/DecisionTheory.lean**: Updated re-export to match Core changes

## [0.213.27] - 2026-02-15

### Added
- **Core/SquareOfOpposition.lean**: Square of Opposition as first-class algebraic object — `Square`, `SquareOps`, `SquareRelations`, `Square.fromOps`, `Square.fromBox`, `Square.fromGQOps`; contradiction diagonal theorems (`fromBox_contradAO`, `fromBox_contradEI`); connection to `outerNeg`/`innerNeg`/`dualQ`; subalternation = Horn-scale ordering
- **Core/Conjectures.lean**: O-corner gap conjecture — `o_corner_gap` (A/E/I lexicalized, O not), `o_corner_pragmatic_explanation` (scalar implicature of I recovers O)
- **Attitude/NegRaising.lean**: Neg-raising as O→E pragmatic strengthening in the doxastic square — `NegRaisingPredicate`, `doxasticSquare`, `negRaisesAt`, `negRaisingAvailable`; `believeNR`/`thinkNR` (neg-raising), `knowNR` (non-neg-raising); `doxasticSquare_contradAO`/`doxasticSquare_contradEI` proved; `negRaising_iff_nonVeridical`

## [0.213.26] - 2026-02-15

### Added
- **Core/Partition.lean**: `partitionValue_ge_of_questionUtility_ge` (bridge from `questionUtility` ordering to `partitionValue` ordering on `Finset.univ`), `partitionValue_congr_on_worlds` (partition value depends only on DP within worlds), `questionUtility_qud_nonneg` (QUD-derived question utility is non-negative under `totalProb ≤ 1`, proved via Blackwell + case split on dpValue sign)
- **Core/Partition.lean**: Helper infrastructure — `foldl_max_ge_opt_aux`/`foldl_max_ge_optVal` (partition-value foldl dominates dpValue), `trivial_toCellsFinset_univ` (trivial QUD has one cell)
- **GSVanRooyBridge.lean**: `blackwell_dominance_refinement` proved (dominance → refinement, the hard direction of Blackwell, via `partitionValue_restrict_support` + `partitionValue_congr_on_worlds` + `blackwell_characterizes_refinement`); `blackwell_full` now fully proved; `questionUtility_nonneg_from_blackwell` proved as corollary of `questionUtility_qud_nonneg`; `mentionSome_multiple_satisfiers` (substantive replacement for vacuous `humanConcern_implies_mentionSomeDP`)

### Changed
- **GSVanRooyBridge.lean**: `blackwell_maximin` reformulated to forward-only `blackwell_maximin_forward` (biconditional was false with fixed action type); 3 false pragmatic answerhood theorems (`pragmaticAnswer_implies_nonnegUtility`, `positiveUtility_implies_pragmaticAnswer`, `pragmaticAnswer_iff_utility`) deleted and replaced with correct `questionUtility_nonneg_from_blackwell`

### Fixed
- **Core/Partition.lean**: Three build errors in `partitionValue_restrict_support` — `congr_arg` for `max` wrapper in `cell_value_restrict_support`, `DecidablePred` for filter predicate, conjunction order in `Finset.mem_filter` destructuring

## [0.213.25] - 2026-02-15

### Changed
- **blog**: Rewrite hello-world post with cumulative-science framing; revise generalized quantifiers post; move Kennedy-meets-G&S post from `docs/blog/` to Hugo blog

## [0.213.24] - 2026-02-15

### Added
- **Theories/Minimalism/Tense/Zeijlstra.lean**: Zeijlstra (2012) SOT as upward Agree — `TenseFeatureStatus`, `TenseHead`, `UpwardAgree`, `SOTAgreeConfig`, derivation theorems for simultaneous/shifted via [uPAST]/[iPAST], SOT-Negative Concord parallel, bridge to Minimalism Agree infrastructure
- **Theories/Minimalism/Tense/Wurmbrand.lean**: Wurmbrand (2014) infinitival tense — three-way `InfinitivalTenseClass` (future irrealis / propositional / restructuring), `WollDecomposition` (*will* = PRES + *woll*), `TemporalOrientation`, verb classifications (want, believe, try)
- **Theories/IntensionalSemantics/Tense/Sharvit.lean**: Sharvit (2003) simultaneous tense — `SimultaneousTense`, `IndirectQuestionTense`, `EmbeddedPresentUnderFuture`, `HebrewSOTChoice`, `RCSimultaneousTense`, derivation theorems for indirect question SOT and embedded present puzzle
- **IntensionalSemantics/Tense/Basic.lean**: 5 new `TensePhenomenon` constructors (`embeddedPresentPuzzle`, `lifetimeEffects`, `fakePast`, `optionalSOT`, `dependentVsIndependentTense`); `hasAgreeBasedSOT` field on `TenseTheory` (default `false`, backward-compatible); `isExtended` classifier; updated `phenomenon_coverage` theorem
- **Phenomena/Tense/Data.lean**: 5 new data frames — `matrixWillSay`/`embeddedPresentUnderFuture` (embedded present puzzle), `lifetimeAristotle` (lifetime effects), `fakePastSubjunctive` (fake past), `optionalSOTPastForm`/`optionalSOTPresentForm` (optional SOT), `decidedToLeave`/`believesToBeSick`/`triedToLeave` (Wurmbrand classification)
- **Phenomena/Tense/Bridge.lean**: Per-theory derivation theorems for Zeijlstra, Wurmbrand, Sharvit, and Deal (fake past)
- **Comparisons/TenseTheories.lean**: Updated to 9 theories — `five_simultaneous_mechanisms`, `only_syntactic_theories_use_agree`, `only_sharvit_has_simultaneous_tense`, `semantic_vs_syntactic_divide`, updated `no_single_theory_covers_all` and `minimal_cover`

### Changed
- **Comparisons/TensesAndPronouns.lean** renamed to **Comparisons/Partee1973.lean** — clearer name; `TenseTheories.lean` scope note cross-references it

## [0.213.23] - 2026-02-15

### Changed
- **IntensionalSemantics/Tense/Basic.lean**: Extracted embedding infrastructure (`embeddedFrame`, `simultaneousFrame`, `shiftedFrame`, `upperLimitConstraint`, `EmbeddedTenseReading`, `availableReadings`, SOT reading theorems, ULC theorems, TensePronoun ↔ SOT frame projections) from `TruthConditional/Sentence/Tense/SequenceOfTense.lean` into the intensional semantics layer where it conceptually belongs
- **TruthConditional/Sentence/Tense/SequenceOfTense.lean**: Reduced to a thin TC↔IS bridge file — retains only `applyTense`↔`embeddedFrame` and `temporallyBound`↔Reichenbach bridge theorems
- **Theory files** (Abusch, VonStechow, Kratzer, Ogihara, Deal): Dropped SequenceOfTense import — all embedding infrastructure now comes from `IS/Tense/Basic.lean`
- **Phenomena/Tense/Bridge.lean**: Updated opens to reference `IntensionalSemantics.Tense` namespace

## [0.213.22] - 2026-02-15

### Added
- **Theories/IntensionalSemantics/Tense/**: New directory with six tense theory formalizations — Abusch (1997), Von Stechow (2009), Kratzer (1998), Ogihara (1996), Klecha (2016), Deal (2020) — each with compositional semantics, derivation theorems, and identity cards
- **IntensionalSemantics/Tense/Basic.lean**: Shared infrastructure — `TensePhenomenon` (11 phenomena), `TenseTheory` identity card, `AttitudeTemporalSemantics`
- **IntensionalSemantics/Tense/Abusch.lean**: Temporal de re (`TemporalDeRe`), relation transmission, ULC, derivation theorems for shifted/simultaneous/double-access/de re
- **IntensionalSemantics/Tense/VonStechow.lean**: Feature checking (`checkTenseFeature`), perspective shift, RC tense derivation
- **IntensionalSemantics/Tense/Kratzer.lean**: SOT deletion (`sotDeletionApplicable`, `applyDeletion`), deletion-vs-ambiguity distinction
- **IntensionalSemantics/Tense/Ogihara.lean**: Ambiguous past (`OgiharaPastReading`), zero tense semantics
- **IntensionalSemantics/Tense/Klecha.lean**: Modal eval time shift (`modalEvalTimeShift`), modal-tense interaction
- **IntensionalSemantics/Tense/Deal.lean**: Counterfactual distance (`PastMorphologyUse`, `CounterfactualDistance`), refined ULC
- **Phenomena/Tense/Data.lean**: Unified tense phenomena data (absorbs SOT + 5 new phenomena: future-under-past, RC tense, modal-tense, counterfactual, temporal de re)
- **Phenomena/Tense/Bridge.lean**: Per-theory × per-phenomenon derivation theorems, aspect-tense pipeline, ULC bridges
- **Comparisons/TenseTheories.lean**: Cross-cutting comparison — convergence, three simultaneous mechanisms, divergence, `no_single_theory_covers_all`, `minimal_cover`
- **Core/Tense.lean**: `evalTimeIndex` field on `TensePronoun` (default 0, backward-compatible); `evalTime`, `fullPresupposition` definitions; `evalTime_root_is_speech`, `evalTime_shifts_under_embedding` theorems
- **IntensionalSemantics/Tense/Basic.lean**: 7 eventual-target phenomena added to `TensePhenomenon` (SOT in indirect questions, FID, historical present, perfect interactions, future-oriented complements, adjunct clause tense, indexical tense shift) with `isEventualTarget` classifier
- **Phenomena/Tense/Data.lean**: Data frames for all 7 eventual targets — `matrixAsked`/`indirectQSimultaneous`/`indirectQShifted` (SOT in questions), `fidWalked`/`fidGardenBeautiful` (FID), `historicalPresent` (narrative present), `pluperfectShifted` (perfect interactions), `wantedToLeave` (future-oriented), `adjunctBeforeLeft`/`matrixWasHappy` (adjunct tense), `indexicalShiftPresent` (Amharic-type shift)

### Changed
- **Phenomena/SequenceOfTense/**: Absorbed into `Phenomena/Tense/` (files deleted)
- **TensesAndPronouns.lean**: Cross-reference to new tense theory infrastructure
- **SequenceOfTense.lean**: Docstring cross-referencing `IntensionalSemantics/Tense/`
- **Tense/Basic.lean**: Export list updated with `evalTime_root_is_speech`, `evalTime_shifts_under_embedding`

## [0.213.21] - 2026-02-15

### Added
- **Core/Partition.lean**: `toFinpartition` — construct Mathlib `Finpartition` from QUD via `Finpartition.ofSetoid`
- **Core/Partition.lean**: Question Utility Bridge section — `questionUtility_eq_finsetSum` (list-based `questionUtility` = `Finset.sum` over `toCellsFinset` via `cellOfRep` bijection + `Finset.sum_nbij`), `questionUtility_refinement_ge` (QUD refinement implies `questionUtility` ordering under non-negative priors)
- **Core/Partition.lean**: Helper infrastructure — `foldl_add_shift`, `foldl_add_eq_toFinset_sum` (NoDup list foldl = Finset.sum), `cellOfRep`/`cellOfRep_mem_toCellsFinset`/`cellOfRep_injOn`/`cellOfRep_surjOn`, `cellProb_mul_valueAfterLearning`, `toCells_totalProb`

### Changed
- **Core/Partition.lean**: `partitionEU` rewritten to use `Finpartition`-based cells instead of custom foldl arithmetic (~200 lines of manual decomposition lemmas replaced); `cellProb_mul_conditionalEU` simplified to use `Finset.sum`/`Finset.single_le_sum`/`field_simp`

## [0.213.20] - 2026-02-15

### Added
- **Core/Tense.lean**: Unified tense pronoun architecture (Abusch 1997) — `TensePronoun` type unifying Priorean, Reichenbach, referential, Kaplan indexical, and attitude-binding views of tense; `GramTense.constrains` as the shared temporal ordering kernel; `doubleAccess` for present-under-past; bridge theorems (`bound_resolve_eq_binder`, `bound_present_simultaneous`, `indexical_present_at_speech`)
- **Tense/Basic.lean**: `applyTense_eq_constrains` bridge connecting Reichenbach `applyTense` to `GramTense.constrains`
- **SequenceOfTense.lean**: `TensePronoun` ↔ SOT frame bridges (`simultaneousFrame_from_tense_pronoun`, `shiftedFrame_from_tense_pronoun`, `doubleAccess_present_under_past`)

### Changed
- **Core/Tense.lean**: `GramTense`, `SOTParameter`, `TenseInterpretation`, `TemporalAssignment`, `interpTense`, `updateTemporal`, `temporalLambdaAbs`, `situationToTemporal`, `SitProp`, `bound_is_sot_mechanism`, `zeroTense_receives_binder_time` moved from `Tense/Basic.lean` to `Core/Tense.lean` — shared infrastructure now accessible to both `TruthConditional/` and `IntensionalSemantics/` without cross-tree imports
- **Tense/Basic.lean**: Now imports `Core.Tense` and re-exports all moved names via `export` — zero downstream breakage
- **TensesAndPronouns.lean**: Docstring updated to reference `TensePronoun` as the unifying type

## [0.213.19] - 2026-02-15

### Added
- **Tense/Basic.lean**: `zeroTense_receives_binder_time` — Ogihara's zero tense mechanism: bound tense variable receives matrix event time
- **SequenceOfTense.lean**: Ogihara bridge theorems (`temporallyBound_forces_time_eq`, `temporallyBound_gives_simultaneous`, `ogihara_bound_tense_simultaneous`) connecting attitude accessibility to Reichenbach frames
- **TensesAndPronouns.lean**: § 7 Referential↔Priorean bridge (`referential_past_decomposition`, `bound_tense_receives_attitude_time`)

### Changed
- **Tense/Basic.lean**: Temporal variable infrastructure (`TemporalAssignment`, `interpTense`, `temporalLambdaAbs`, `updateTemporal`, `situationToTemporal`) moved here from Comparisons/TensesAndPronouns — these are tense theory definitions, not cross-theory comparisons
- **TensesAndPronouns.lean**: Slimmed to genuine cross-theory observations (Kaplan, Elbourne, Partee-vs-Prior); now uses Tense/Basic exports
- **SequenceOfTense.lean**: Added `SituationDependent` import for attitude↔tense bridge

## [0.213.18] - 2026-02-15

### Added
- **Core/Intension.lean**: `ReferentialMode` (indexical/anaphoric/bound) — Partee's three-way classification as theory-neutral infrastructure; `VarAssignment`, `updateVar`, `lookupVar`, `varLambdaAbs` — generic variable assignment algebra
- **Elbourne.lean**: `SitVarStatus.toReferentialModes`, `ReferentialMode.toSitVarStatus` bridge with round-trip theorem

### Changed
- **Tense/Basic.lean**: `TenseInterpretation` is now an alias for `Core.ReferentialMode.ReferentialMode` (same constructors, zero downstream breakage); added `SitProp` docstring noting Bool counterpart
- **TensesAndPronouns.lean**: `TemporalAssignment`, `updateTemporal`, `interpTense`, `temporalLambdaAbs` now specialize `Core.VarAssignment` generics; `toSitVarStatus` uses `ReferentialMode.isFree`
- **SituationDependent.lean**: Added `SitProp` docstring noting Prop counterpart

## [0.213.17] - 2026-02-15

### Added
- **Comparisons/TensesAndPronouns.lean**: Partee (1973) structural analogy — temporal assignment functions, `interpTense`, `temporalLambdaAbs`, bridge to Kaplan's `opNow` and Elbourne's `SitVarStatus`, Partee vs Prior tension

## [0.213.16] - 2026-02-15

### Added
- **Core/ModalLogic.lean**: `ModalItem` shared type unifying `AuxEntry`, `ModalAdvEntry`, `ModalExpression` — with `sharesForce`, `sharesFlavor`, `areRegisterVariants`; `ConcordType` enum (negation/modalNecessity/modalPossibility) with `fromModalForce`
- **Core/Register.lean**: `SocialIndex` type (competence/solidarity) for social indexation of concord

### Changed
- **Fragments/English/FunctionWords.lean**: Add `.toModalItem` projections to `AuxEntry` and `ModalAdvEntry`
- **Theories/IntensionalSemantics/Modal/Typology.lean**: Add `.toModalItem` projection to `ModalExpression`
- **Phenomena/ModalConcord/LiuRotter2025Bridge.lean**: Refactor to use `ModalItem.sharesForce` from Core; add Section D with `socialIndex` mapping and cross-phenomenon concord theorems (possibility MC patterns with NC)

## [0.213.15] - 2026-02-15

### Added
- **Fragments/English/FunctionWords.lean**: `ModalAdvEntry` structure and 8 modal adverb entries (*certainly*, *definitely*, *necessarily*, *possibly*, *perhaps*, *maybe*, *probably*, *potentially*) with force-flavor meanings and register
- **Phenomena/ModalConcord/LiuRotter2025.lean**: Liu & Rotter (2025) data — 2×2 FORCE × NUMBER speaker commitment ratings, 7 social meaning interaction effects, competence/warmth classification
- **Phenomena/ModalConcord/LiuRotter2025Bridge.lean**: Bridge proving all 6 stimulus aux-adverb pairs share force, force predicts commitment direction, cross-reference to Dieuleveut et al.

## [0.213.14] - 2026-02-15

### Added
- **Core/Register.lean**: Sociolinguistic register type (`Level`: informal/neutral/formal) for pronoun and modal formality
- **Phenomena/ModalConcord/**: Data and Bridge for Dieuleveut, Hsu & Bhatt (2025) modal non-concord experiments
- **Phenomena/Quantification/Bridge.lean**: Replace deleted Universals.lean with Bridge file
- **Core/Quantification.lean**: Van Benthem 1984 number-tree impossibility theorems (`no_asymmetric`, `no_strict_partial_order`, `no_euclidean`)
- **SORRY_AUDIT.md**: Strategic analysis of all sorrys and axioms by role and difficulty

### Changed
- **Core/Pronouns.lean**: Replace `formality : Nat` with `register : Level` across `PronounEntry` and `AllocutiveEntry`
- **Core/Verbs.lean**: Remove `VerbClass` enum — verb classification is now derived from primitive fields (factivity, opacity, speech-act status, etc.)
- **Fragments/*/Pronouns.lean** (10 languages): Update all pronoun entries from `formality` to `register`
- **Fragments/English/Predicates/Verbal.lean**: Remove `verbClass` usage, add `levinClass` and `rootProfile` to verb entries
- **Fragments/*/Predicates.lean** (8 languages): Remove `verbClass` references
- **Phenomena/Complementation/Bridge.lean**: Rewrite `deriveCTPClass` to use primitive verb fields instead of `VerbClass`
- **Theories/QuestionSemantics/LeftPeriphery.lean**: Rewrite `deriveSelectionClass` to use primitive verb fields
- **Theories/Minimalism/Phenomena/Allocutivity.lean**: Update formality→register bridge (`formalityToHonLevel` → `levelToHonLevel`)
- **Fragments/English/FunctionWords.lean**: Add register field to aux entries

### Removed
- **Phenomena/Quantification/Universals.lean**: Consolidated into Bridge.lean
- **Core/Verbs.lean**: `VerbClass` enum (replaced by derived classification)

## [0.213.13] - 2026-02-15

### Changed
- **Linglib/Core/Partition.lean**: Prove `eu_eq_partitionEU` (law of total expectation for partition-relative EU). Adds ~200 lines of infrastructure: foldl-sum arithmetic helpers, cell probability cancellation, disjoint filter sum decomposition, and the `toCells` partition sum decomposition. Only `blackwell_refinement_value` (Jensen's inequality) remains as sorry.

## [0.213.12] - 2026-02-15

### Added
- **Phenomena/Modality/PracticalReasoning.lean**: Teleological necessity (Kratzer §2.8) — "To get to Harlem, take the A train" scenario with goal and efficiency orderings
- **Phenomena/Modality/InformationalBackgrounds.lean**: Non-realistic informational modal bases (Kratzer §2.3d) — weather report scenario, `isRealistic` proofs, evidence bridge
- **Phenomena/Modality/DegreeCollapse.lean**: Modal strength as degree (Kratzer §2.5) — `modalStrength` definition, concrete rain scenario theorems, fully proved general theorems `strength_one_iff_necessity` and `strength_pos_iff_possibility`
- **Theories/IntensionalSemantics/Modal/ProbabilityOrdering.lean**: Probability-to-ordering bridge (Kratzer §2.4) — `probToOrdering`, uniform/skewed assignments, ranking preservation
- **Fragments/German/Predicates/Modal.lean**: German modal verb fragment — `GermanModalEntry` structure, 6 modals (können, dürfen, müssen, sollen, mögen, wollen)
- **Phenomena/Modality/GermanModalsBridge.lean**: German modal typology bridge — `ModalInventory` from fragment, `german_all_iff` verified

### Changed
- **Phenomena/Modality/TypologyBridge.lean**: Add German as 10th language; rename `seven_of_nine_perfect_iff` → `eight_of_ten_perfect_iff`
- **Linglib.lean**: Add 9 new imports for Kratzer Ch. 2 and ConditionalModality modules

## [0.213.11] - 2026-02-15

### Changed
- **Theories/TruthConditional/Sentence/Tense/SequenceOfTense.lean**: Remove vestigial imports (`IntensionalSemantics.Attitude.SituationDependent`, `ViewpointAspect`) and relocate cross-framework aspect–tense pipeline section to Bridge; file is now purely intra-theory (Tense.Basic + Reichenbach)
- **Phenomena/SequenceOfTense/Bridge.lean**: Receive relocated pipeline; add `evalPast_iff_PAST` and `evalPres_iff_toSitProp` proving point-level and situation-level tense operators agree via `toSitProp`; add Reichenbach–aspect correspondence (`matrixSaid_is_perfective`, `embeddedShifted_is_perfective`, `perfective_implies_aspect_assumption`)

## [0.213.9] - 2026-02-14

### Added
- **Theories/IntensionalSemantics/Attitude/SituationDependent.lean**: Situation-dependent attitude semantics (von Stechow 2009) — `SitProp`, `SitAccessRel`, `sitBoxAt`, `SitDoxasticPredicate`; backward-compat lifting operators (`liftProp`, `liftAccess`, `liftDoxastic`) with key theorem `sitBoxAt_lift_eq_boxAt` proving lifted operators recover classic Hintikka semantics; `temporallyBound` and `futureOriented` accessibility constraints for genuinely temporal attitudes
- **Theories/TruthConditional/Sentence/Tense/SequenceOfTense.lean**: SOT mechanics connecting tense to attitude embedding — `embeddedFrame` (perspective time shift P' = E_matrix), `EmbeddedTenseReading` (.shifted/.simultaneous), `availableReadings` by `SOTParameter`; `simultaneousFrame`/`shiftedFrame` constructors; bridge theorems deriving past-under-past from Reichenbach analysis (`past_under_past_shifted_is_past`, `past_under_past_simultaneous_is_past`)
- **Phenomena/SequenceOfTense/Data.lean**: Concrete Reichenbach frames for English SOT ("John said Mary was sick" — simultaneous and shifted readings) and Japanese non-SOT ("Taroo-wa ... to itta") with theory-neutral temporal fact theorems
- **Phenomena/SequenceOfTense/Bridge.lean**: Bridge theorems connecting SOT data to theory — `satisfiesTense` verification, `simultaneousFrame`/`shiftedFrame` constructor matching, SOT parameter bridge (English vs Japanese), `composeTense` derivation

### Changed
- **Theories/TruthConditional/Determiner/Quantifier.lean**: Added `few_sem` (`|R∩S| < |R\S|`) and `half_sem` (`2*|R∩S| = |R|`) denotations; conservativity proofs (`few_conservative`, `half_conservative`); `few_scope_down` monotonicity proof; `nodup` field on `FiniteModel`; bijection-invariance infrastructure (`map_bij_perm`, `filter_length_bij_inv`, `all_bij_inv`, `any_bij_inv`)
- **Fragments/English/Determiners.lean**: Replaced `sorry` in `gqDenotation` for `few`/`half`; added `few_conservative_bridge`, `half_conservative_bridge`
- **Phenomena/Quantification/Universals.lean**: Converted 3 axioms to theorems — `conservativity_universal`, `quantity_universal` (Mostowski 1957 bijection-invariance), `positive_strong_determiners_upward_monotone` (P&W Ch.6)
- **FiniteModel instances**: Added `nodup` field to all 6 instances (Quantifier.lean, ExamplesBridge.lean, Monotonicity.lean, IntensionalSemantics/Basic.lean, AlternativeGeneration.lean, MontagueExhaustivity.lean)
- **Theories/IntensionalSemantics/Mood/Basic.lean**: Added `subj_temporal_anchor` theorem and docstring connecting SUBJ's situation introduction to attitude temporal shifting (both mechanisms introduce temporal anchors for embedded clauses)
- **Theories/TruthConditional/Sentence/Tense/Basic.lean**: Added `composeTense` algebraic properties (`composeTense_present_left`, `composeTense_present_right`, `composeTense_past_idempotent`, `composeTense_future_idempotent`) with docstring pointing to `SequenceOfTense` for the derived version

## [0.213.8] - 2026-02-14

### Changed
- **Theories/QuestionSemantics/Answerhood.lean**: Closed all 11 sorrys — proved `wh_refines_polar` (G&S 1984 core result), `ans_answers`, `ans_completely_answers`, `complete_not_partial`, `gsToHamblin_recognizes_ans`, `partition_cells_are_hamblin_alternatives`, `nonrigid_may_fail_semantic`, `exhaustive_answers`; replaced false `karttunen_agrees_with_gs_for_unique_answer` with correct `gs_ans_implies_karttunen` + `karttunen_not_implies_gs`; added `karttunen_coordination_problem` (concrete cross-categorial failure); added foldl helper infrastructure (`foldl_reps_subset`, `foldl_acc_preserved`, `foldl_has_rep`, `foldl_reps_no_dup`, `foldl_nodup`, `filter_map_comm`, `nodup_filter_eq_singleton`)

## [0.213.7] - 2026-02-14

### Added
- **Core/RootDimensions.lean**: Root content framework grounded in Levin (1993) — `MeaningComponents` (6 binary class-defining features), `Range` constraint mechanism, 6 quality dimensions (force magnitude/direction from Talmy 1988/2000, patient robustness from Spalek & McNally, result type from Levin/Beavers & Koontz-Garboden 2020, volitionality/agent control from Dowty 1991), `RootProfile` with `overlaps`, full Levin class taxonomy (49 top-level classes from §§9–57)
- **Phenomena/SpalekMcNally/Data.lean**: Bridge theorems for Spalek & McNally (forthcoming) — shared event structure (Levin class, causative builder, verb class), different root content (patient restrictions, force direction, agent control), root overlap theorem, translation data (P-ACTRES Tables 1–2), asymmetric translation preference theorems

### Changed
- **Core/Verbs.lean**: Added `levinClass` and `rootProfile` optional fields to `VerbCore`
- **Fragments/English/Predicates/Verbal.lean**: Added `tear_` entry with full root profile; updated `break_` with Levin class and root profile
- **Fragments/Spanish/Predicates.lean**: Added `rasgar` entry with root profile and causative builder

## [0.213.6] - 2026-02-14

### Changed
- **Phenomena/Quantification/Universals.lean**: Replaced 10 vacuous `axiom ... : True` declarations with real types — `conservativity_universal` now asserts `Conservative (q.gqDenotation m)`, `quantity_universal` asserts `QuantityInvariant`, `positive_strong_determiners_upward_monotone` asserts `PositiveStrong → ScopeUpwardMono`; van Benthem impossibility theorems converted from axioms to `theorem ... := sorry`; removed `no_nonconservative_determiners` (merged into `conservativity_universal`); converted 3 unformalizeable claims to comments
- **Phenomena/Quantification/Typology.lean**: Converted vacuous `conservativity_crosslinguistic` to comment
- **Phenomena/Agreement/NounCategorization.lean**: Gave `classifier_semantic_hierarchy` real implicational type; converted `greenberg_classifier_number` to comment
- **Phenomena/Coordination/Typology.lean**: Closed trivial sorry (goal was `True`)
- **14 files across Comparisons/, Theories/, Phenomena/**: Replaced ~27 `theorem ... : True := trivial` placeholders with real types (with `sorry`), comments explaining what's needed, or actual proofs where possible; 2 vacuous theorems in Barker2011 deleted

## [0.213.5] - 2026-02-14

### Changed (Pattern C migration)
- Renamed 58 Phenomena data/bridge files to enforce Theories→Fragments→Phenomena dependency discipline (see 0.213.5 commit)

## [0.213.4] - 2026-02-14

### Added
- **Core/Time.lean**: Extract theory-neutral temporal infrastructure from `TruthConditional/Core/Time` — `TimeStructure`, `Interval` + all methods (point, contains, subinterval, overlaps, precedes, meets), `BoundaryType`/`GInterval` (Rouillard 2026 open/closed intervals), `DenseTime`, `Situation` + all methods, `TemporalRelation` + eval, `TimeStructure ℤ` instance + example constants
- **Core/Reichenbach.lean**: Extract Reichenbach's temporal framework from `TruthConditional/Core/Time` — `ReichenbachFrame` (S, P, R, E times; Kiparsky 2002 perspective time P), `isPast`/`isPresent`/`isFuture` (R vs P), `isPerfective`/`isImperfective`/`isPerfect`/`isProspective` (E vs R), `isPast_simpleCase` theorem
- **Core/Causation.lean**: Unified causal infrastructure replacing `CausalInference.lean` + `CausalModel.lean` — structural layer (Nadathur & Lauer 2020: `Variable`, `Situation`, `CausalLaw`, `CausalDynamics`, `normalDevelopment`, `intervene`, `causallyNecessary`/`causallySufficient`, `manipulates`) + probabilistic layer (Grusdt, Lassiter & Franke 2022: `WorldState`, `CausalRelation`, `NoisyOR`)
- **Core/DecisionTheory.lean**: Promoted from `QuestionSemantics/DecisionTheory` — `DecisionProblem`, `expectedUtility`, `maximin`, mention-some/mention-all classification; usable by RSA, causal decision theory, explanation models without question-semantic dependencies
- **Core/NaturalLogic.lean**: Natural logic relation algebra (Icard 2012) — 7 `NLRelation`s (≡, ⊑, ⊒, ^, |, ⌣, #), 9 `EntailmentSig`s, `join` (⋈), `compose` (∘), `project` ([]^φ); `PartialOrder` + `BoundedOrder` on relations, `Monoid` on signatures
- **Core/Partition.lean**: Partition lattice on `QUD` — refinement ordering, coarsening, cell enumeration; Merin (1999) decision-theoretic characterization of negativity as proper coarsening
- **Core/PolarityPartition.lean**: Bridge connecting `NaturalLogic` algebra to `Partition` lattice — `complements_same_partition`, DE contexts map refinements to coarsenings, double-complement identity
- **Core/Verbs.lean**: Cross-linguistic verb infrastructure — `VerbCore` bundles argument structure, semantic class, complement type, control, attitude/causative builders; language-specific fragments extend with inflectional paradigms
- **Core/Morphology/MorphRule.lean**: Compositional morphological rules (`MorphRule σ`) with formal AND semantic effects, `Stem σ` with inflectional paradigms, Bybee (1985) relevance hierarchy; replaces `Core/Morpheme.lean`
- **Core/Morphology/Aspect.lean**: Aspect morphology rules (progressive, gerundive) — all `isVacuous := true`
- **Core/Morphology/Number.lean**: Number morphology linking singular/plural to mereological structure (Link 1983); vacuous verb agreement
- **Core/Morphology/StemToLex.lean**: Bridge from morphological stems to Montague-style semantic lexical entries
- **Theories/EventSemantics/TemporalDecomposition.lean**: Subevent structure for telic predicates — `SubeventPhases` (activity + result traces), `TemporalDecomposition` (.simple/.complex), `DecomposedEv`; bridges `EventStructure.Template` to `ViewpointAspect`
- **Theories/TruthConditional/Sentence/Tense/PerfectPolysemy.lean**: Kiparsky (2002) perfect polysemy — Perfect Time Span interaction with subevent structure via `TemporalDecomposition`
- **Theories/RSA/Implementations/HardingGerstenbergIcard2025.lean**: Communication-first explanation account — utterances are "FACT because X=x", literal meaning is actual causation, decision problem is manipulation game; classic explanatory virtues emerge from pragmatic dynamics
- **Fragments/German/Predicates.lean**: German causative and attitude verbs extending `VerbCore` with inflectional paradigm (3sg, Präteritum, Partizip II)
- **Phenomena/Causatives/StructuralCausation.lean**: Verification of causal structures (preemption, prevention, enabling, double prevention, overdetermination)
- **Phenomena/Morphology/Composition.lean**: Tests for morphological pipeline — regular/irregular plurals, mass nouns, verb agreement

### Changed
- **Theories/TruthConditional/Core/Time.lean**: Slimmed to theory-specific branching-time definitions only — `WorldHistory`, `historicalBase`, `HistoricalProperties`, `TProp`/`TBProp`, `liftProp`, `holdsAt`; all framework-agnostic infrastructure moved to Core/
- **Theories/TruthConditional/Sentence/Tense/Basic.lean**: Tense now relates R to perspective time P (Kiparsky 2002), not speech time S; `applyTense`/`satisfiesTense` updated
- **Theories/QuestionSemantics/DecisionTheory.lean**: Core decision theory promoted to `Core/DecisionTheory`; module now re-exports and adds question-specific extensions
- **Theories/QuestionSemantics/Partition.lean**: Partition lattice promoted to `Core/Partition`; module now re-exports
- **Theories/TruthConditional/Core/Polarity.lean**: Integrated `NaturalLogic` entailment signatures
- **Theories/TruthConditional/Sentence/Entailment/AntiAdditivity.lean**: Extended with `NaturalLogic`-based anti-additivity characterization
- **Theories/TruthConditional/Sentence/Entailment/PolarityBuilder.lean**: Extended with compositional polarity signature tracking
- **Fragments/English/Predicates/Verbal.lean**: Overhauled to use `VerbCore`; all verb entries now carry argument structure, semantic class, and builder links
- **Fragments/{French,Japanese,Korean,Mandarin,Spanish,Turkish}/Predicates.lean**: Extended to use `VerbCore` with language-specific inflectional paradigms

### Deleted
- **Core/CausalInference.lean**: Replaced by `Core/Causation.lean`
- **Core/CausalModel.lean**: Absorbed into `Core/Causation.lean`
- **Core/Morpheme.lean**: Replaced by `Core/Morphology/MorphRule.lean`

## [0.213.3] - 2026-02-14

### Added
- **Core/Morphology/Tense.lean**: Morphological rules for tense marking — `TenseFormType` (`.synthetic` vs `.periphrastic`), five `MorphRule` constructors (`pastRule`, `presentRule`, `futureRule`, `periphrasticPastRule`, `periphrasticFutureRule`), all `isVacuous := true` since temporal semantics lives in the Theory layer; Lakoff's diagnostic: periphrastic forms block "false" tense interpretations
- **Phenomena/Lakoff1970/Data.lean**: 11 grammaticality judgments from Lakoff (1970) §§1–5 — false tense (ex4a/6a/8a/9a), SOT/novelty (ex13a/13b), perfect/salience (ex22a/22b), will-deletion (ex27a/27b/25b); `TenseJudgment` structure with `TenseUseType` and `TenseFormType` fields; collection/counting verification theorems
- **Phenomena/Lakoff1970/Bridge.lean**: Bridge theorems connecting Lakoff data to Theory predictions — per-datum form-type verification against Fragment entries, false-tense diagnostic (`falseTenseRequiresSynthetic`), temporal-perspective bridges (`false_past_is_temporally_present`, `false_past_classified_correctly`), novel-info/salience/will-deletion bridges, cross-cutting acceptability prediction (`grammatical_false_tense_all_synthetic`)

### Changed
- **Theories/.../Perspective.lean**: Added `TenseUse` (`.trueTense`/`.falseTense`), `classifyUse` (derives use type from `GramTense` + `TensePerspective` temporal relation), `falseTenseRequiresSynthetic` (Lakoff's periphrastic diagnostic); imports `Core/Morphology/Tense`
- **Fragments/English/Tense.lean**: Added `TensePerspectiveEntry` extending `TenseEvidentialParadigm` with `gramTense` and `formType`; four new entries (`simplePastPerspective`, `simplePresentPerspective`, `usedTo`, `goingTo`); `allowsFalseTense` derived from `formType`; verification theorems for synthetic/periphrastic false-tense behavior

## [0.213.2] - 2026-02-14

### Added
- **Core/Morphology/Degree.lean**: Comparative and superlative `MorphRule` constructors (`comparativeRule`, `superlativeRule`) — both `isVacuous := true` since degree semantics is compositional (handled by `TruthConditional/Adjective/Comparative.lean`); supports regular (`-er`/`-est`), irregular (`better`/`best`), and periphrastic (`more expensive`/`most expensive`) forms
- **Core/Morphology/ScaleFromParadigm.lean**: Automatic Horn scale generation from adjective paradigms — `MorphScale` (positive/comparative/superlative triple), `adjectiveScale` (extracts degree scale from a `Stem`'s paradigm), `morphologicalAlternatives` (returns paradigm-mates as scalar alternatives), `MorphScale.toHornScale` (bridge to `Core/HornScale.lean`)
- **`.degree` constructor on `MorphCategory`**: Relevance rank 5 (same as tense) — comparative/superlative morphology compositionally modifies the adjective's interpretation, analogous to tense on verbs
- **`AdjModifierEntry.toStem`**: Converts adjective modifier entries to morphological stems with degree paradigms; all 18 entries in the English adjective fragment produce valid stems
- **Phenomena/Morphology/DegreeComposition.lean**: Test suite for degree morphology — regular/irregular/periphrastic form generation, scale generation, morphological alternatives, Bybee relevance hierarchy bridge, semantic vacuity verification across all adjective entries

## [0.213.1] - 2026-02-14

### Added
- **Core/DiscourseRole.lean**: Framework-agnostic discourse participant roles (`DiscourseRole`: speaker/addressee), `IllocutionaryMood` (declarative/interrogative/imperative/promissive), `epistemicAuthority` (maps mood to authoritative participant per Lakoff 1970), `resolveRole` (projects discourse role to entity via `KContext`)
- **Theories/TruthConditional/Sentence/Tense/Perspective.lean**: Lakoff (1970) participant-sensitive tense — `TensePerspective` extends `EvidentialFrame` with `speakerSalience` and `hearerNovelty`; five Lakoff predicates: `falsePast` (past tense on present events lacking salience), `falseFuture`, `novelInfoPresent` (present survives under past matrix when content is new to hearer), `perfectRequiresSalience`, `willDeletion` (scheduled futures in present tense); bridge theorems connecting to `UPCondition.present` and `downstreamEvidence`

## [0.213.0] - 2026-02-14

### Added
- **Core/Morpheme.lean**: Framework-agnostic morphological infrastructure — `MorphStatus` (freeWord/simpleClitic/specialClitic/inflAffix/derivAffix), `AttachmentSide`, `SelectionDegree`, `ParadigmCell`, `MorphCategory` (Bybee 1985 relevance hierarchy), `respectsRelevanceHierarchy`
- **Theories/Morphology/Diagnostics/CliticVsAffix.lean**: Zwicky & Pullum (1983) six-criterion diagnostic framework — `CliticAffixProfile` structure, `affixScore`/`cliticScore`, `classify` (derives `MorphStatus` from profile), exhaustivity theorem
- **Phenomena/Morphology/ZwickyPullum1983.lean**: English data for Z&P's argument that *-n't* is an inflectional affix — diagnostic profiles for simple clitics (*'s*, *'ve*, *'d*), inflectional affixes (*-ed*, *-s*, *-est*), and contracted negator (*-n't*); classification theorems (`nt_is_affix`, all six criteria unambiguous); paradigm gap verification (*mayn't*, *amn't*); morphophonological irregularity verification (*won't*, *can't*, *don't*, *shan't*, *mustn't*); semantic scope bridge to `IntensionalSemantics.Modal` (NOT(CAN(P)) vs MUST(NOT(P)) idiosyncrasy)
- **AuxEntry**: `negForm` (contracted negative form from Z&P Table 1) and `negIrregular` (phonological irregularity flag) fields; negative forms for all 22 auxiliaries including paradigm gaps (*may*, *am*) and irregular forms (*won't*, *can't*, *don't*, *shan't*, *mustn't*); new semi-modal entries (`dare`/`need`/`ought`)

### Refactored
- **MorphemeOrder.lean**: `MorphCategory`, `relevanceRank`, `respectsRelevanceHierarchy` moved from `DepGrammar.MemorySurprisal.MorphemeOrder` to `Core.Morpheme` — Bybee's relevance hierarchy is a morphological universal, not specific to memory-surprisal theory

## [0.212.0] - 2026-02-13

### Refactored
- **Renamed `Core/CounterfactualSpace.lean` → `Core/CausalInference.lean`**, namespace `Core.CounterfactualSpace` → `Core.CausalInference`. "Causal inference" better describes the unified module's scope (causal Bayes nets + counterfactual probability spaces + WorldState distributions)
- **Absorbed `CausalBayesNet.lean` into `CausalInference.lean`**: `CausalRelation`, `NoisyOR`, `WorldState` (all derived probabilities, conditional probabilities, independence/correlation checks, constructors, examples, `IsValid`, all validity theorems, `law_of_total_probability`, `bayes_theorem`), `DiscreteWorldSpace`, `toCFProbSpace`/`toWorldState` bridges, `dynamicsToKernel`, `backtrackerCounterfactual`
- **Deleted `CausalBayesNet.lean`**: All content moved to `CausalInference.lean`, eliminating the bridge pattern between the two files
- **Counterfactual.lean**: Removed `CounterfactualSpaceBridge` section (`dynamicsToKernel`, `causalCounterfactual_eq_kernel`, `backtrackerCounterfactual` moved to CausalInference); removed CounterfactualSpace import
- **Assertability.lean**: Removed `CounterfactualSpaceBridge` section (`assertabilityScore_eq_condOnF` absorbed); rewired import/open from CausalBayesNet to CausalInference
- **Integration.lean**: Rewired import/open from CausalBayesNet to CausalInference
- **RSA/GrusdtLassiterFranke2022.lean**: Rewired import/open from CausalBayesNet to CausalInference
- **Phenomena/Conditionals/Studies/GrusdtLassiterFranke2022.lean**: Rewired import/open from CausalBayesNet to CausalInference

### Fixed
- **`worldState_pCGivenA_eq_condOnF`**: Previously `sorry`, now proved by co-locating `marginalF`/`condOnF`/`toCFProbSpace` in the same file — marginalF at `true` unfolds to `w.pA` by `ring`

## [0.211.0] - 2026-02-13

### Added
- **Core/CounterfactualSpace.lean**: Counterfactual probability spaces (Park, Yang & Icard 2026) — `CFProbSpace` (joint distribution on ΩF × ΩCF), `FinCausalKernel`, `CFCausalSpace` with no-cross-world-effect axiom, `pointMassKernel`, marginals, conditioning, `backtrackerProb`/`interventionalProb` queries, `isIndependent`/`isSynchronized`/`isSymmetric` predicates. Marginal sum-to-one and nonneg theorems proved; `independent_cond_eq_marginal` and `synchronized_cond_point_mass` proved
- **CausalBayesNet.lean**: `WorldState.toCFProbSpace` / `CFProbSpace.toWorldState` bridge revealing `WorldState` as degenerate `CFProbSpace Bool Bool`
- **Counterfactual.lean**: `CausalDynamics.toKernel` bridge (deterministic model → point-mass kernel), `backtrackerCounterfactual` operator (new: condition on factual observation, read off counterfactual probability)
- **Integration.lean**: `integration_factors_through_cfps` theorem showing the grounding chain factors through `CFProbSpace`
- **Assertability.lean**: `assertabilityScore_eq_condOnF` theorem connecting assertability to `CFProbSpace` conditioning

## [0.210.0] - 2026-02-13

### Refactored
- **DynamicSemantics/Core**: Unified CCP namespace by eliminating the 2-param `CCP W E` type from `Core/Update.lean`. `InfoState W E` is now an `abbrev` for `Set (Possibility W E)`, so `CCP (Possibility W E)` is definitionally the old `CCP W E`. Merged `CCPOps` namespace into `CCP` — `testNeg`/`testMight`/`testMust`/`testImpl` are now `CCP.neg`/`CCP.might`/`CCP.must`/`CCP.impl`. `Update.lean` imports `CCP.lean` and no longer defines its own CCP type or duplicated combinators. `Translation.lean` updated to use `CCP (Possibility Unit E)`. `Effects/State/Basic.lean` FCS and UpdateSemantics combinators now delegate to generic `CCP.*`; `State W` made `abbrev`. `Effects/Nondeterminism/Charlow2019.lean` `stateMight` delegates to `CCP.might`

## [0.209.0] - 2026-02-13

### Added
- **Core/CCP.lean**: Generic test combinators in `CCPOps` namespace — `testNeg`, `testMight`, `testMust`, `testImpl` — as single source of truth for test-based dynamic operations on `CCP P`. `IsTest` proofs for all four, plus `testMight_eq_testNeg_testNeg` duality theorem. Docstring cross-references added to duplicated combinators in `Core/Update.lean`, `Effects/State/Basic.lean` (FCS + UpdateSemantics), and `Effects/Nondeterminism/Charlow2019.lean`

## [0.208.0] - 2026-02-13

### Refactored
- **DynamicSemantics/**: Reorganized by computational effect rather than named theory. New three-tier structure: `Core/` (shared infrastructure), `Effects/` (one subdir per effect: State, Nondeterminism, Continuation, Bilateral, Probability, Epistemic), `Systems/` (named theories as effect combinations: PLA, BUS, CDRT, IntensionalCDRT, DynamicGQ). DPL and DRT moved to `Effects/State/`; Charlow2019 and PointwiseUpdate to `Effects/Nondeterminism/`; Bilateral to `Effects/Bilateral/`; FreeChoice moved from BUS to `Effects/Bilateral/`; Probabilistic to `Effects/Probability/`; NeoStalnakerian to `Effects/Epistemic/`. FileChangeSemantics and UpdateSemantics stubs absorbed into `Effects/State/Basic.lean`. No content changes — only file moves and import path rewrites
- **TTR/**: Relocated from `DynamicSemantics/TTR/` to `Theories/TTR/` — TTR is a standalone framework like CCG or HPSG, not a dynamic semantics variant

## [0.207.0] - 2026-02-13

### Added
- **Core/Continuation.lean**: General continuation monad (`Cont R A`, `pure`, `bind`, `map`, `lower`, `Tower`), monad laws (all `rfl`). Extracts pattern from `LiftedTypes.lean`
- **Core/Mereology.lean**: `isMaximal`, `atomCount`, `cum_maximal_unique` (proved), `atomCount_sup_disjoint` (sorry'd). For Charlow 2021 M_v and cardinality operators
- **DynamicSemantics/Core/PointwiseUpdate.lean**: Bridge between pointwise `DRS` and update-theoretic `StateCCP`. `liftPW` (Charlow's ↑), `lowerPW` (↓), round-trip and distributivity theorems (sorry'd)
- **DynamicSemantics/DynamicGQ/Basic.lean**: Pointwise dynamic GQ operators — `Evar`, `Mvar`, `CardTest`, `sawDRS`, `exactlyN_pw`, `pseudoCumulative`/`cumulative` formulas (Charlow 2021 §2)
- **DynamicSemantics/DynamicGQ/UpdateTheoretic.lean**: State-level dynamic GQ operators — `Evar_u`, `Mvar_u`, `CardTest_u`, `dseq_u`, `exactlyN_u`. `CardTest_u_distributive` proved; `Mvar_u_nondistributive` sorry'd (Charlow 2021 §6)
- **DynamicSemantics/DynamicGQ/HigherOrder.lean**: Continuized dynamic GQs — `HODGQ`, `exactlyN_ho`, `liftGQ`, `lowerGQ`, `combineHO` (Charlow 2021 §3–4)
- **DynamicSemantics/DynamicGQ/SubtypePolymorphism.lean**: `Completeness` (t/T), `subtypeOf`, `TypedDRS`, `cumulative_welltyped`, `pseudo_cumulative_illtyped` (both proved). Charlow 2021 §4
- **DynamicSemantics/DynamicGQ/PostSuppositional.lean**: `PostSupp` (writer-like monad), `pure`, `bind`, `map`, `reify`, `trueAt`, `exactlyN_postsup` (Charlow 2021 §5)
- **Phenomena/Charlow2021/Data.lean**: Scenario A/B finite models with `native_decide` verification of cumulative vs pseudo-cumulative reading predictions
- **Phenomena/Charlow2021/CumulativeReadings.lean**: Bridge theorems connecting Data to DynamicGQ theory — `pointwise_overgenerates`, `update_correct`, `cumulative_strictly_stronger`
- **Comparisons/CumulativeReadings.lean**: Three-way comparison of higher-order GQ, post-suppositional, and update-theoretic approaches to cumulative readings

## [0.206.0] - 2026-02-13

### Refactored
- **Core/Evidence.lean**: Absorbed `EvidentialPerspective` from Evidential.lean (framework-agnostic type), added `EvidentialPerspective.isNonfuture`, renamed `toCausalRelation` → `toEvidentialPerspective`. Deleted `CausalRelation` (isomorphic to `EvidentialPerspective`), `isCausallyDownstream` (trivially-true constant), `all_sources_downstream`
- **Theories/.../Evidential.lean**: Added `EPCondition` (5 values) and `UPCondition` (5 values) enums with `toConstraint` methods. Revised `TenseEvidentialParadigm` to store enum values instead of opaque lambdas; `isNonfuture` now derived from `ep.isNonfuture`. Added generic `EPCondition.nonfuture_implies_downstream` lemma (one proof, five cases). Parameterized `nonfutureMeaning` over `{W : Type*}`. Deleted `Language`, `UtterancePerspective`, `GramTense.isNonfuture`, `causallyDownstreamEvidence`, `futurateLicensed` (pure aliases), CausalModel import
- **Fragments/{English/Tense, Korean/Evidentials, Bulgarian/Evidentials}.lean**: Replaced lambda EP/UP constraints with `EPCondition`/`UPCondition` enum values, removed `language`/`isNonfuture` fields
- **Phenomena/Cumming2026/Bridge.lean**: Replaced 4 per-language grouped theorems with per-entry `isNonfuture` verification (7 theorems) + generic `nonfuture_downstream` master theorem + per-entry downstream corollaries (7 one-liners)
- **Phenomena/Modality/EpistemicEvidentiality.lean**: Replaced `all_evidence_types_downstream` (used deleted `isCausallyDownstream`) with `all_evidence_types_nonfuture` using `toEvidentialPerspective.isNonfuture`

## [0.205.0] - 2026-02-13

### Added
- **Core/Evidence.lean**: Canonical three-way `EvidentialSource` (direct, hearsay, inference), `CausalRelation` (downstream, contemporaneous, prospective), `toCausalRelation` mapping, `all_sources_downstream` universal theorem
- **Fragments/English/Tense.lean**: English tense paradigm entries (Cumming 2026, Tables 20/22) — moved from Evidential.lean
- **Fragments/Korean/Evidentials.lean**: Korean -te and -ney paradigm entries (Cumming 2026, Tables 18/19) — moved from Evidential.lean
- **Fragments/Bulgarian/Evidentials.lean**: Bulgarian -l paradigm entries (Cumming 2026, Table 17) — moved from Evidential.lean
- **Phenomena/Cumming2026/Bridge.lean**: Verification theorems relocated from Evidential.lean (`cross_linguistic_nonfuture_downstream`, `future_no_downstream`, `korean_te_ney_ep_diverge`) plus per-language downstream theorems

### Refactored
- **Theories/TruthConditional/Sentence/Tense/Evidential.lean**: Now theory-only (types + predicates). Paradigm data moved to Fragments/, verification to Phenomena/. Added `nonfutureMeaning` (presuppositional encoding via `PrProp`), `EvidentialPerspective.toCausalRelation` bridge to `Core.Evidence`, `causallyDownstreamEvidence` connecting to `CausalModel.factuallyDeveloped`, `futurateLicensed` replacing `futurateException` stub with `normalDevelopment`-based grounding
- **Phenomena/Modality/EpistemicEvidentiality.lean**: Added `EvidenceType.toEvidentialSource` mapping VF&G's 4 types to Cumming's 3, `all_evidence_types_downstream` theorem

## [0.204.0] - 2026-02-13

### Added
- **Theories/TruthConditional/Sentence/Tense/Evidential.lean**: Cumming (2026) tense evidential constraint — `EvidentialFrame` extends `ReichenbachFrame` with acquisition time A, `downstreamEvidence` (T ≤ A), `TenseEvidentialParadigm` row type. Paradigm data for English (Tables 20, 22), Bulgarian -l (Table 17), Korean -te (Table 18), Korean -ney (Table 19). Verification: `cross_linguistic_nonfuture_downstream` (all nonfuture entries entail T ≤ A), `future_no_downstream`, `korean_te_ney_ep_diverge` (EP and UP factorize independently)
- **Comparisons/TenseModalEvidentiality.lean**: Bridge between Cumming's tense evidentiality and VF&G's kernel semantics. Dripping-raincoat scenario: `tense_modal_evidential_parallel` (downstream evidence co-occurs with must-defined), `direct_evidence_blocks_both` (direct evidence → kernel settles → must undefined, bare assertion used)

## [0.203.1] - 2026-02-13

### Refactored
- **Core/InformationStructure.lean**: Unified `PolarityMarkingEntry` structure — particles, prosodic, and other strategies share one type with optional `form`/`prosodicTarget` fields. Dutch and German Fragment files now both instantiate the same structure, making cross-linguistic comparison structural rather than accidental
- **Fragments/Dutch/Particles.lean**: `wel` now typed as `PolarityMarkingEntry` (was `PolarityParticleEntry`); dropped language-specific structure
- **Fragments/German/PolarityMarking.lean**: `verumFocus`/`dochPreUtterance` now typed as `PolarityMarkingEntry` (was a separate German-specific structure)
- **Phenomena/TurcoBraunDimroth2014/Data.lean**: `ProductionDatum.pctByStrategy : PolarityMarkingStrategy → Rat` replaces four named `Rat` fields — adding a strategy constructor now forces updating every datum. Dominant-strategy theorems universally quantified over strategies (`∀ s, s ≠ ... → ...`)

## [0.203.0] - 2026-02-13

### Added
- **Core/InformationStructure.lean**: `PolaritySwitchContext` (contrast vs correction; Klein 2008, Umbach 2004) and `PolarityMarkingStrategy` (particle, verumFocus, other, unmarked) — theory-neutral IS types for polarity-switch research
- **Fragments/Dutch/Particles.lean**: Dutch affirmative particle *wel*, sentence-internal, accented, both contexts. Per-entry `rfl` verification theorems
- **Fragments/German/PolarityMarking.lean**: German Verum focus (Höhle 1992) and pre-utterance *doch*. Named "PolarityMarking" not "Particles" because German's strategy is non-particulate
- **Phenomena/TurcoBraunDimroth2014/Data.lean**: Production strategy distributions (Fig. 2) and VF pitch range data (Fig. 6) from Turco, Braun & Dimroth 2014. Bridge theorems: `strategies_differ` (Dutch particle ≠ German VF), `dominant_strategies_both_marked`, `dutch_particle_internal_german_doch_not`. Verified: German zero sentence-internal particles (`rfl`), correction more prominent than contrast (`native_decide` on Rat)

## [0.202.0] - 2026-02-13

### Added
- **Core/MeasurementScale.lean**: Refactored `maxOnScale` from TemporalConnectives into domain-general infrastructure. Added `maxOnScale_singleton` (proved), `isAmbidirectional` (Rett 2026, §3), and `maxOnScale_atLeast_singleton` bridge theorem
- **Theories/TruthConditional/Adjective/Comparative.lean**: Comparative morpheme semantics via order-sensitive MAX (Schwarzschild 2008 / Rett 2026). `comparativeSem_eq_MAX` bridges direct comparison to MAX-based formulation via `maxOnScale_singleton`. Antonymy as scale reversal (`taller_shorter_antonymy`), ambidirectionality of comparatives, `comparative_than_DE` (universal quantification anti-monotonicity; Hoeksema 1983), manner implicature effects (Cépeda 2018)
- **Theories/TruthConditional/Sentence/Tense/TemporalConnectives.lean**: Ambidirectionality theorems for *before* (closed interval hypothesis), *after* (not ambidirectional), *while* (not ambidirectional). Imports `maxOnScale` from MeasurementScale instead of defining locally
- **Phenomena/Negation/ExpletiveNegation.lean**: High vs low EN typology (Greco 2018), cross-linguistic EN data from Jin & Koenig (2021) survey (50 languages for *before*, 39 for *fear*, 6+ for comparatives). `rett_generalization`: EN ↔ ambidirectionality verified exhaustively over all constructions (`cases c <;> rfl`). `licensesComparativeEN_iff_not_closed` connects scale boundedness to EN predictions (Kennedy & McNally 2005). Manner implicature data (French *avant que ne*, Italian comparative *non*) typed via `MannerEffect` from Comparative
- Unified temporal and degree MAX under single `maxOnScale` operator (Rett 2026)

## [0.201.0] - 2026-02-13

### Added
- **Theories/TruthConditional/Sentence/Tense/TemporalConnectives.lean**: Temporal connective semantics — Anscombe/Krifka under-specification vs Rett (2020) ambiguity for *before*/*after*. Both theories formalized over `timeTrace` (set of contained time points). INCHOAT (GLB) / COMPLET (LUB) coercion operators with scale-sensitive MAX
- **Fragments/English/TemporalExpressions.lean** (renamed from TemporalConnectives): Temporal subordinating connectives (before, after, while) as `TemporalConnectiveEntry`; temporal adverbial modifiers (within, at) as separate `TemporalModifierEntry` type
- **Fragments/Tagalog/TemporalConnectives.lean**: Tagalog *bago* ('before') aspect–reading data (PFV.NEUT → ≺ initial, AIA → ≺ final; Dell 1983, Rett 2020 §2.4)
- **Comparisons/BeforeAfter.lean**: Under-specification vs ambiguity theory profiles and empirical discriminators
- **Phenomena/AlstottAravind2026/Data.lean**: Processing data from 4 self-paced reading experiments with proper `Experiment` enum and `SpilloverRegion` type
- **Phenomena/TemporalConnectives/Examples.lean**: Concrete truth-condition tests for 6 scenarios (4 positive, 2 negative) verifying Anscombe and Rett on ℕ time points, plus INCHOAT/COMPLET on concrete data
- Proved: `inchoat_bridges_inception`, `complet_bridges_cessation`, `stative_denotation_subinterval_closed`, `timeTrace_stativeDenotation`, `timeTrace_accomplishmentDenotation`. 2 sorry's remain (Anscombe/Rett agreement on stative-before and telic-after)

## [0.200.0] - 2026-02-13

### Refactored (architectural cleanup of 0.199.0)
- **Minimalism/Core/VerbalDecomposition.lean**: Extract VerbHead (vDO/vGO/vBE) and event composition predicates out of Applicative.lean into standalone module. Applicative.lean now contains only ApplType (high/low).
- **Minimalism/Morphology/Fission.lean**: Parameterize over person type — generic `FissionRule` and `PFMarkingCondition` structures with no Fragment imports. Spanish instantiation moved to Bridge.lean.
- **Core/PersonCategory.lean**: Extract PersonCategory type, predicates, and UD bridges out of Phenomena/Agreement/PersonMarkingTypology.lean into Core/. Fixes Fragment→Phenomena dependency violation.
- **Fragments/Spanish/PersonFeatures.lean**: Import from Core.PersonCategory instead of Phenomena.Agreement.PersonMarkingTypology. Fixes dependency hierarchy violation.
- **Fragments/Spanish/Clitics.lean**: Syncretism (`isSyncretic`, `datReflSyncretic`) now derived from paradigm entries via `lookupForm` instead of stipulated match.
- **Phenomena/MunozPerez2026/Bridge.lean**: Now contains Spanish Fission instantiation (theory-specific, kept out of Fragments). Added Fission verification theorems (previously in Morphology/Fission.lean).
- **Minimalism/Phenomena/VoiceAppl.lean**: Add Voice/Phase bridge theorems — agentive Voice = phase head, non-thematic = not. `phase_iff_theta` proves correlation across all canonical Voice heads.
- **Minimalism/Core/Phase.lean**: Add Voice/v* correspondence documentation.

## [0.199.0] - 2026-02-13

### Added
- **Minimalism/Core/Voice.lean**: Voice head flavors (Kratzer 1996; Schäfer 2008) — agentive, causer, nonThematic, expletive. Key claim: non-thematic Voice (anticausative SE) is semantically vacuous.
- **Minimalism/Core/Applicative.lean**: Applicative types (Pylkkänen 2008 high/low) and Cuervo (2003) verbal decomposition (vDO, vGO, vBE). `isInchoative`, `isCausative` predicates.
- **Minimalism/Bridge/EventStructureBridge.lean**: Maps R&L (1998) event structure templates to Cuervo's VerbHead decomposition. Proves accomplishment↔causative, achievement↔inchoative bridges.
- **Minimalism/Morphology/Fission.lean**: Fission postsyntactic operation (Muñoz Pérez 2026). Derives stylistic applicative person restriction from [+PART, +SING] and inchoative structural context.
- **Minimalism/Phenomena/VoiceAppl.lean**: Classic Voice/Appl derivation tests — transitive, anticausative, unaccusative, ditransitive (low Appl), benefactive (high Appl), middle voice.
- **Fragments/Spanish/Clitics.lean**: Full Spanish clitic paradigm with syncretism data. DAT-REFL syncretism for 1SG/2SG drives SE-optionality.
- **Fragments/Spanish/Predicates.lean**: 10 Spanish verbs classified by anticausative marking and event structure. Per-verb verification theorems.
- **Fragments/Spanish/PersonFeatures.lean**: Bridges Cysouw PersonCategory to [±PART, ±AUTHOR, ±SING] feature decomposition. Derives Fission applicability.
- **Phenomena/MunozPerez2026/Data.lean**: Grammaticality judgments — three-way synonymy, person restriction (1SG/2SG only), marking restriction (unmarked blocks LE).
- **Phenomena/MunozPerez2026/Bridge.lean**: Derives all five predictions from infrastructure: person restriction from features, inchoative requirement from Fission context, marking restriction from fragment, SE-optionality from syncretism, synonymy from Voice vacuity.
- **Comparisons/CausativeAlternation.lean**: Cross-theory bridge connecting semantic (production/dependence), event-structural (templates), syntactic (Voice/VerbHead), and empirical (ThickThin) layers of the causative alternation.

### Changed
- **Minimalism/Core/Basic.lean**: Add `Voice` and `Appl` constructors to `Cat`.
- **Minimalism/Formal/ExtendedProjection/Basic.lean**: Voice and Appl get [+V, -N] features and F1 value. Updated `catFeatures`, `fValue`, `catFamily`, `fpos_iff_functional`.
- **Minimalism/Formal/ExtendedProjection/Properties.lean**: Add Voice/Appl cases to `epSemanticType`.

## [0.198.0] - 2026-02-12

### Added
- **Core/Mereology.lean**: Extract 26 generic mereological definitions (AlgClosure, CUM, DIV, QUA, Atom, Overlap, ExtMeasure, QMOD, IsSumHom + theorems) from EventSemantics to framework-agnostic Core module.
- **Core/SatisfactionOrdering.lean**: Rename from `OrderTheory.lean` — satisfaction-based orderings over Bool-valued criteria (Kratzer worlds, Phillips-Brown propositions).
- **NumericalExpressions.lean**: Bridge OT constraints (Cummins 2015) to SatisfactionOrdering — `NumeralConstraint` enum, `constraintSatisfied` coarse-graining, `cumminsOrdering`, `zero_violations_best`/`zero_bounds_any_violated` theorems.

### Changed
- **EventSemantics/Krifka1998.lean**: Add non-degeneracy condition to SINC (Krifka eq. 51.ii `extended` field). Add `MeasureProportional` structure and prove `grad_of_sinc` (was sorry).
- **EventSemantics/Mereology.lean**: Refactored to import Core/Mereology.lean, re-exports generic items, keeps only event-specific definitions (EventCEM, LexCum, RoleHom, Vendler bridges).
- **Modal/Kratzer.lean**, **PhillipsBrown.lean**, **SatisfactionOrdering.lean**: Update imports/opens for OrderTheory → SatisfactionOrdering rename.

## [0.197.0] - 2026-02-12

### Changed
- **Degree type unification**: Collapse four parallel degree types (`Height` in LG2017, `Height` in TG2022, `Degree` in GradableNouns, canonical `Degree max`) into one canonical `Degree max` / `Threshold max` from `Domain/Degree.lean`. Deletes ~120 lines of duplicate type definitions and boilerplate across 5 files.
- **Domain/Degree.lean**: Add `Fintype` instances for `Degree`/`Threshold`, `Coe (Threshold max) (Degree max)` via `Fin.castSucc`, convenience constructors `deg`/`thr`. Replace `.toNat` cross-type comparisons with `LinearOrder` operators in `positiveMeaning`, `negativeMeaning`, `antonymMeaning`, `contradictoryNeg`, `contraryNeg`, `inGapRegion`, `positiveMeaning'`, `contraryNegMeaning`, `notContraryNegMeaning`.
- **LassiterGoodman2017.lean**: `Height` and `Threshold` are now aliases for `Degree 10` and `Threshold 10`. Constructor patterns replaced with `match h.toNat with`.
- **Nouwen2024.lean**: Updated to use `deg n` constructors from unified type.
- **TesslerGoodman2022.lean**: `Height` now alias for `Degree 10`. Priors use `match h.toNat with`.
- **GradableNouns.lean**: Local `Degree` inductive replaced with `Degree 10` from `Domain/Degree.lean`. `d0_is_minimum` derived from `BoundedOrder.bot_le`.

## [0.196.0] - 2026-02-12

### Changed
- **Adjective/Theory.lean**: Remove phantom `max : Nat` parameter from `GradableAdjEntry` (no field used it). Remove `ScaleType` alias — use `Boundedness` directly from `Core.Scale`.
- **Fragments/English/Predicates/Adjectival.lean**: Update `AdjectivalPredicateEntry` (no type parameter). Replace `.lowerClosed`/`.upperClosed` with `.lowerBounded`/`.upperBounded`.
- **Fragments/English/Modifiers/Adjectives.lean**: `AdjModifierEntry.scaleType` now typed `Boundedness` directly. Replace `.lowerClosed`/`.upperClosed` with `.lowerBounded`/`.upperBounded`.
- **Adjective/Intensification.lean**: Fix dependency violation — `EvaluativeValence` now defined here (in Theories/) instead of imported from Phenomena/. `Phenomena/Gradability/Intensifiers.lean` imports it from Theories/ (correct direction).
- **Phenomena/Gradability/Vagueness.lean**: Move `VaguenessTheoryType`, `TheoryPredictionProfile`, and theory profiles to `Comparisons/VaguenessTheories.lean` (theory-comparative, not empirical data).

## [0.195.0] - 2026-02-12

### Added
- **Core/MeasurementScale.lean**: `MLScale` — Dinis & Jacinto (2026) ML theory (Marginal and Large differences). Structure with 5 axioms over a `LinearOrder`, derived relations (`L`, `MarginalDiff`, `AtMostMarginal`, `LargeDiff`), and two proved theorems: `m_transitive` (M is transitive) and `m_bounded` (M between two M-related elements implies M to each). No sorry.
- **Theories/TruthConditional/Adjective/Theory.lean**: `GradableMLScale` — combines `MIPDomain` with `MLScale` for the Marginality Scales Account. `marginalityPositive` — positive form requires degree *significantly* (L-related) greater than norm, not merely greater (R). `marginality_entails_standard` — marginality semantics strictly stronger than Kennedy (proved).
- **Phenomena/Gradability/Vagueness.lean**: `InterestRelativityDatum` — extension of vague adjective changes when interests change despite identical precise property (Charles III / Prince William scenario). `ToleranceStepDatum` — tolerance steps feel non-uniform: same precise difference, different perceived significance depending on proximity to threshold.

## [0.194.0] - 2026-02-12

### Changed
- **Core/MeasurementScale.lean**: Replace stipulative `boundedness` tag on `MeasurementScale` with Mathlib order typeclasses. `MeasurementScale` now extends `LinearOrder` only (no `boundedness` field). Monotonicity definitions (`IsUpwardMonotone`, `IsDownwardMonotone`, etc.) require `[LinearOrder α]` instead of `[MeasurementScale α]`. Removed ℕ/ℤ `MeasurementScale` instances and `satisfiesUDM` wrapper. Added `Boundedness.ofType` for deriving the enum from type properties. Added three typeclass-based licensing theorems: `open_no_upward_ceiling` (`[NoMaxOrder α]`), `upperBound_admits_optimum` (`[OrderTop α]`), `lowerBound_admits_optimum` (`[OrderBot α]`). `Boundedness` enum retained for lexical data tagging.

## [0.193.0] - 2026-02-12

### Added
- **Theories/DynamicSemantics/NeoStalnakerian.lean**: Rudin (2025) "Asserting epistemic modals" (L&P 48:43-88). Neo-Stalnakerian Framework: meta-intensionalization (MI), refinement, s-compatibility, rejection licensing. Simple semantics: `mightSimple`, `mustSimple`, `liftProp` with MI characterization theorems (`MI_liftProp`, `MI_mightSimple`, `MI_mustSimple`, `MI_must_eq_MI_lift`). NSF-derived updates: `nsfUpdateNonEpistemic` (intersection), `nsfUpdateMight` (consistency test), `nsfUpdateMust` (= non-epistemic). Derivation theorems: `nsf_recovers_stalnaker` (Stalnaker 1978), `nsfUpdateMight_spec` (Veltman 1996). Ordering semantics (§5): `OrdEpistemicState`, `bestWorlds` (maximal elements), `mightOrdering`, `nsfUpdateMightOrd` (add p to ordering source). Key proof: `ordering_update_commensurate` — if base has p-worlds, BEST after adding p contains a p-world (satisfaction count argument via `strict_dom_more_sat`). Appendix A2: `mustOrdering`, `MI_ord_must`, `nsfUpdateMustOrd` (add p, remove p-disjoint propositions). Appendix B: relational semantics equivalence under epistemic closure (`MI_relational_might_eq_domain`, `MI_relational_must_eq_domain`, `MI_relOrd_might_eq_domain`). Truth ≠ Acceptance: `might_truth_acceptance_dissociate` (truth depends on assertor's info, rejection on rejector's). No sorry.
- **Phenomena/Modality/Studies/Khoo2015.lean**: Khoo (2015) "Modal Disagreements" (Inquiry 58:511-534). Experimental data: 60 MTurk participants, 2×2 design (Control/Modal × False/Rejection), 7-point Likert. Mean ratings: Modal-Rejection 5.03, Modal-False 2.42, Control-Rejection 5.60, Control-False 6.10. The Difference Observation: speakers reject might-claims without judging them false. 6 verification theorems (`modal_rejection_high`, `modal_falsity_low`, `modal_rejection_exceeds_falsity`, `control_no_dissociation`, `modal_gap_large`, `control_gap_small`). Bridge theorem `nsf_predicts_khoo_pattern` connects to Rudin's `might_truth_acceptance_dissociate`.

## [0.192.0] - 2026-02-12

### Added
- **Phenomena/Modality/EpistemicEvidentiality.lean**: VF&G (2010) empirical data. 12 minimal pairs (bare vs. must) across 4 evidence types (direct, indirect, elimination, reported). 6 inference data (modus ponens validity, must-perhaps contradiction, retraction asymmetry, hedging preference, Hey-Wait-a-Minute test). 4 generalization theorems via `native_decide`: `direct_evidence_blocks_must`, `indirect_evidence_enables_must`, `must_always_entails_prejacent`, `bare_always_felicitous`.
- **IntensionalSemantics/Modal/Kernel.lean**: Von Fintel & Gillies (2010, 2021) kernel semantics. `Kernel` structure (direct-information propositions generating a modal base via ⋂K). `directlySettlesExplicit` (Implementation 1: ∃X∈K, X⊆P or X∩P=∅). `kernelPartition`, `settlesByPartition` (Implementation 2: partition-based settling). `kernelMust`, `kernelMight` as `PrProp` — first file connecting presuppositional propositions with Kratzer modal operators. Evidential presupposition: must/might defined only when K doesn't directly settle the prejacent. `KernelBackground` for world-dependent kernels. Bridge theorems: `kernelMust_eq_simpleNecessity`, `Kernel.toEpistemicFlavor`, `Kernel.ofCG`. Proved: `must_is_strong`, `must_entails_prejacent`, `empty_kernel_always_defined`, `direct_evidence_infelicity`, `settling_monotone`. Deep theorems formalizing VF&G's core arguments: `entailment_settling_gap` (∃K,φ: B_K⊆⟦φ⟧ but K doesn't settle φ — the central insight), `indirectness_neq_weakness` (3-way independence of presupposition and assertion), `modus_ponens_with_must` (Argument 4.3.1). Mastermind verification via `native_decide` theorems (no #eval).

## [0.191.0] - 2026-02-11

### Added
- **TruthConditional/Determiner/Numeral/Semantics.lean**: EXH–type-shifting duality (Section 7c). `exhNumeral` — scalar exhaustification for numerals (Spector 2013 §6.2). `exh_lowerBound_eq_exact` — EXH(lower-bound) = exact. `typeShift_exact_eq_lowerBound` — typeShift(exact) = lower-bound. `exh_typeShift_roundtrip` — round-trip identity. `typeShift_subsumes_exh` — type-shifting produces the same {exact, lower-bound} pair as EXH, making EXH redundant for numerals when type-shifted meanings are grammatically available (Partee 1987).

## [0.190.0] - 2026-02-11

### Added
- **TruthConditional/Noun/TypeShifting.lean**: `isPrincipalUltrafilter`, `roundtrip_preserves_principal` (proved), `roundtrip_changes_nonprincipal` — principal ultrafilter criterion for when Partee type-shifts change truth conditions. Round-trip A(BE(Q)) preserves truth conditions iff Q is a principal ultrafilter (proper names, pronouns, definites). For non-principal GQs (universals, degree quantifiers, numerals), the round-trip collapses. This determines when RSA should treat type-shifted meanings as alternative interpretations.
- **RSA/Core/Eval.lean**: `ksL1Interp`, `ksL1InterpJoint`, `ksL1InterpMarginal` — unified knowledge-state L1 with interpretation marginalization. Standard infrastructure for any RSA model where expressions have grammatically available type-shifted parses with different truth conditions. Generalizes Scontras & Pearl (2021) scope ambiguity to arbitrary interpretation dimensions.
- **docs/blog/kennedy-meets-goodman-stuhlmuller.md**: Added section on when type-shifting matters for RSA — a novel observation that standard RSA models have not grappled with: for non-principal-ultrafilter expressions, type-shifted meanings are latent variables the listener should marginalize over.

## [0.189.0] - 2026-02-11

### Added
- **TruthConditional/Determiner/Numeral/Semantics.lean**: `typeLower` — formal type-shifting operation (Partee 1987 BE + iota) deriving lower-bound from exact meaning. `lowerBound_from_exact_typeshift` theorem proves `LowerBound.meaning = typeLower (maxMeaning .eq)` for all standard worlds, formalizing Kennedy's (2015 §3.1) claim that `atLeastFromExact` is a derivational fact. `typeLower_uniqueness`, `universal_closure_fails` — the lower-bound is the unique output of type-shifting (existential closure is the only viable closure; universal closure is unsatisfiable).
- **RSA/Core/Eval.lean**: `softKsS1LogScore`, log-sum-exp normalized `softKsS1`, `softKsL1` — soft quality-filtered knowledge-state S1/L1 with noisy L0 (ε > 0, finite α). Uses log-sum-exp normalization to prevent Float underflow at high α. `noisyL0` implements L0_noisy(w|u) = (1-ε)×meaning/|compat| + ε/|W|.
- **RSA/Core/Model.lean**: `quality_blocks_exact_not_lb`, `quality_selects_interp`, `kennedy_gs13_prediction` — formal guarantees for Kennedy type-shifting + quality filter: when exact interpretation is quality-blocked but lower-bound passes, mixing over interpretations shifts to lower-bound reading. Derives G&S (2013) Experiment 2 from Kennedy (2015) semantics.
- **RSA/Implementations/GoodmanStuhlmuller2013.lean**: `KennedyInterp`, `kennedyMeaningInterp`, refactored to use unified `ksL1Interp` — Kennedy type-shifting ambiguity model. Bare "two" has exact (de-Fregean) and lower-bound (type-lowered) interpretations; RSA marginalizes over both. Key predictions: full access → exact reading (s2=14/17), partial access → lower-bound reading (s3=3/4). Interpretation marginals: full access P(exact)=8/17, P(lb)=9/17; partial access P(exact)=0, P(lb)=1. 3 theorems: `kennedy_ambig_bare_full_exact`, `kennedy_ambig_bare_partial_lowerbound`, `kennedy_ambig_exactness_weakens`.

## [0.188.0] - 2026-02-11

### Fixed
- **RSA/Core/Eval.lean**: Added `qualityFilter`, `ksS1Score`, `ksS1`, `ksL1` — general-purpose knowledge-state S1/L1 implementing G&S 2013 Eq. (2)-(3) log-utility. Quality filter kills utterances false at any world the speaker considers possible (ln(0) = -∞ penalty). For uniform L0, this is exact: pass quality filter, then score by 1/|compat|.
- **RSA/Core/Model.lean**: Added `expectedLogL0`, `expectedLogL0_neg_inf_iff_quality_fails`, `quality_pass_score`, `ksS1_kl_difference` — ℝ equivalence theorems connecting quality filter to E[ln L0] and KL divergence (sorry'd, require Mathlib EReal reasoning).
- **RSA/Implementations/GoodmanStuhlmuller2013.lean**: Fixed buggy `expectedL0_param` which computed E_b[L0] (arithmetic mean) instead of correct exp(E_b[ln L0]) (geometric mean via log utility). Replaced hand-rolled S1/L1 chain with unified `RSA.Eval.ksL1`. Key consequence: quality filter forces uncertain speakers to use "at least n" (bare and moreThan fail quality), deriving Kennedy Class B ignorance implicatures from RSA alone — no neo-Gricean machinery needed. Class B is now informative at partial access (L1 reads asymmetric observation distribution). 3 regression tests (`quality_blocks_moreThan_uncertain`, `quality_blocks_bare_uncertain`, `only_atLeast_survives_uncertain`). All existing quantifier and lower-bound theorems preserved.

## [0.187.0] - 2026-02-11

### Changed
- **RSA/Implementations/GoodmanStuhlmuller2013.lean**: Full rewrite (~460 lines, down from ~1040). Removes dead code (UnifiedAPIVersion, FintypeDemo, AppleConfig, hand-rolled truth tables, duplicate RSA chains, MontaguGrounding). Grounds quantifier meanings in `RSA.Domains.Quantity`, numeral meanings in Kennedy (2015) `maxMeaning`. Kennedy exact semantics is now the primary numeral theory with Class A/B alternative structure ({bare, moreThan, atLeast} for numeral n). Key findings: (1) bare numerals under Kennedy ARE knowledge-sensitive through the belief channel (not implicature cancellation), (2) Class B "at least" is uninformative in RSA — Kennedy's ignorance implicatures are neo-Gricean (¬K(=n) ∧ ¬K(>n)), not derivable from Bayesian updating. Lower-bound theory retained as comparison. 22 theorems, all by `native_decide`.

## [0.186.0] - 2026-02-11

### Added
- **Phenomena/NumeralModification/Embedding.lean**: 8 new Tier 1 test cases from recent literature: "almost" polar orientation (Nouwen 2006), "only" + focus (Coppock & Beaver 2014), factive "surprised" (Kiparsky & Kiparsky 1970), imperative compliance (Kaufmann 2012), neg-raising "doubt" (Gajewski 2007), QUD-convexity (Solt & Waldon 2019), acquisition data (Musolino 2004), degree "too" (Meier 2003). Now 20 data points, 18 embedding types, 8 generalizations.
- **Theories/TruthConditional/Determiner/Numeral/Embedding.lean**: `isProximal`, `almostMeaning` (Nouwen 2006 proximity + polar), `onlyMeaning` (= `exh`, proved `rfl`), `isConvex` (QUD-convexity predicate), `extendedWorlds` [0..5]. 8 new theorems: `almost_diverges_above`, `almost_asymmetry`, `only_informative_lowerBound`, `negation_convexity_divergence` (LB convex, BL non-convex), `imperative_compliance_divergence`, `factive_presupposition_divergence`, `degree_too_monotonicity`, `acquisition_musolino`. `embeddingDivergences` expanded to 10 entries (8 diverging).
- **Fragments/English/NumeralModifiers.lean**: `ModifierType.approximator`, `almost` and `nearly` entries (polar exclusion distinct from tolerance modifiers). `approximatorModifiers` collection. `approximators_not_sorites`, `approximators_distinct_from_tolerance` verification theorems.

## [0.185.0] - 2026-02-11

### Added
- **Phenomena/NumeralModification/Embedding.lean**: Theory-neutral empirical test cases for bare numerals in embedding environments. `EmbeddingType` (10 environment types), `NumeralEmbeddingDatum` (12 data points: negation, modals, "exactly" redundancy, attitudes, conditionals, restrictors, questions, existential scope, collective predicates). `EmbeddingGeneralization` (5 cross-cutting generalizations). Sources: Horn 1972, Kennedy 2015 §5, Bylinina & Nouwen 2020.
- **Theories/TruthConditional/Determiner/Numeral/Embedding.lean**: Formal predictions of LowerBound vs Bilateral under embedding. `BareNumeral.succ` (scalar alternative computation). 7 embedding functions: `negatedMeaning`, `possibilityMeaning`, `necessityMeaning`, `exactlyMeaning`, `conditionalMeaning`, `exh` (exhaustivity operator), `exhUnderPossibility`/`exhOverPossibility` (EXH scope interaction). 15 divergence theorems: `negation_divergence_above`, `entailment_reversal_under_negation`, `exactly_redundant_bilateral` (rfl), `exactly_informative_lowerBound`, `modal_possibility_divergence`, `modal_necessity_divergence`, `exh_strengthens_lowerBound`, `exh_vacuous_bilateral`, `exh_convergence`, `exh_scope_diverges_lowerBound`. `EmbeddingPrediction` summary infrastructure with `four_divergence_points`.

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
- **Cummins & Franke 2021** (CumminsFranke2021.lean): Conference registration scenario. `moreThanMeaning` with grounding theorems to `lowerBoundMeaning`. Semantic argStr computation: `moreThan110_semantically_stronger`. Pragmatic reversal: `wider_enrichment_weakens_argStr`. Exam scenario: `ExamStimulus`, `examDifficulty`, `truthfulQuantifiers`, `strongestTruthfulPositive` with weakening pattern verification (all→most→some). `quantifier_ordering_matches_scale` (→ Core.Scale).
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
