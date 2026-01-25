# Changelog

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
