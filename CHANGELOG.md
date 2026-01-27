# Changelog

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
