# Changelog

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
