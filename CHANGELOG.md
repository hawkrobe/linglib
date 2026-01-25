# Changelog

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
