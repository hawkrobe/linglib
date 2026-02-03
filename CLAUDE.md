# CLAUDE.md

This file provides guidance to Claude Code when working with this repository.

## Build Commands

```bash
lake build          # Build the entire project
lake build Linglib  # Build just the main library
```

## Project Overview

Linglib is a Lean 4 library for formalizing linguistic theories and connecting them to computational pragmatics (RSA - Rational Speech Acts). The library emphasizes **grounding**: RSA models derive their meaning functions from Montague compositional semantics rather than stipulating them.

## Architecture

### Core Principle: Compositional Grounding

RSA implementations should derive meaning from Montague semantics:

```
Montague/Lexicon/         →  Adjective/Numeral/Modal semantics
    ↓
Montague/Quantifiers      →  ⟦some⟧, ⟦all⟧, ⟦most⟧
    ↓
Fragments/                →  Reusable RSA domains (Quantities, Scales, Degrees)
    ↓
RSA/Implementations/      →  Paper replications with grounding theorems
```

Example grounding pattern:
```lean
-- In RSA/Implementations/GoodmanStuhlmuller2013.lean
-- RSA uses Montague quantifier semantics, doesn't stipulate its own
theorem rsa_some_meaning_from_montague :
    quantityMeaning .some_ = Montague.Quantifiers.existsSome := ...
```

### Directory Structure

```
Linglib/
├── Core/                    # Framework-agnostic infrastructure
│   ├── Basic.lean           # Shared types (Cat, Word, Lexicon)
│   ├── Grammar.lean         # Abstract Grammar typeclass
│   ├── Distribution.lean    # Probability distributions
│   ├── QUD.lean             # Question Under Discussion
│   ├── Polarity.lean        # Upward/downward entailing contexts
│   ├── Proposition.lean     # Prop' = World → Bool
│   └── Interfaces/          # Theory comparison interfaces
│
├── Fragments/               # Reusable RSA domains
│   ├── Quantities.lean      # Scalar quantity domain (some/all)
│   ├── Scales.lean          # Horn scales (⟨some, all⟩, ⟨good, amazing⟩)
│   ├── Degrees.lean         # Gradable adjective domains
│   ├── ReferenceGames.lean  # Reference game infrastructure
│   └── QUD.lean             # QUD partitions
│
├── Theories/
│   ├── Montague/            # Compositional semantics (see below)
│   ├── RSA/                 # Rational Speech Acts (see below)
│   ├── NeoGricean/          # Categorical implicature theory
│   ├── CCG/                 # Combinatory Categorial Grammar
│   ├── HPSG/                # Head-Driven Phrase Structure Grammar
│   ├── Minimalism/          # Minimalist Program
│   ├── DependencyGrammar/   # Word Grammar
│   └── Comparisons/         # Cross-theory comparisons
│
└── Phenomena/               # Empirical data (50+ files)
    ├── {Study}/Data.lean    # Experimental results
    └── Semantics/           # Truth condition judgments
```

### Theories/Montague/ - Compositional Semantics

The semantic foundation for RSA grounding:

```
Montague/
├── Basic.lean               # Prop' = World → Bool, pnot, pand, por
├── Quantifiers.lean         # ⟦some⟧, ⟦all⟧, ⟦most⟧
├── Lexicon/
│   ├── Degrees.lean         # Degree, Threshold, HasDegree typeclass
│   ├── Adjectives/Theory.lean  # Gradable adjective semantics
│   ├── Modals/              # Kratzer vs Simple modal semantics
│   └── Numerals/            # Lower-bound vs bilateral numeral semantics
├── Entailment/
│   ├── Basic.lean           # Entailment relation
│   ├── Monotonicity.lean    # Upward/downward monotonicity
│   └── Polarity.lean        # Polarity item licensing
└── Projection/              # Presupposition projection
```

### Theories/RSA/ - Rational Speech Acts

14 paper implementations with grounding:

```
RSA/
├── Core/
│   ├── Basic.lean           # RSAScenario (ℚ), L0, S1, L1
│   ├── Model.lean           # RSAScenarioR (ℝ) for proofs
│   └── Intensional.lean     # Belief states, speakerCredence
├── Extensions/
│   ├── LexicalUncertainty/  # Bergen et al. 2016
│   └── InformationTheory/   # Zaslavsky et al. rate-distortion
├── ScalarImplicatures/      # Embedded SI handling
└── Implementations/         # Paper replications
    ├── FrankGoodman2012.lean        # Reference games
    ├── GoodmanStuhlmuller2013.lean  # Scalar implicature + knowledge
    ├── KaoEtAl2014_Hyperbole.lean   # QUD-sensitive hyperbole
    ├── KaoEtAl2014_Metaphor.lean    # Feature-based metaphor
    ├── YoonEtAl2020.lean            # Politeness (compositional negation)
    ├── ScontrasPearl2021.lean       # Scope ambiguity
    ├── ScontrasTonhauser2025.lean   # BToM projection
    ├── TesslerFranke2020.lean       # Flexible negation
    ├── LassiterGoodman2017.lean     # Gradable adjectives
    └── ...                          # 14 total implementations
```

### RSAScenario: Unified Type

The `RSAScenario` structure supports all RSA variants via 5 latent variable categories:

| Latent Type | Purpose | Example Paper |
|-------------|---------|---------------|
| `World` | What's actually true | All papers |
| `BeliefState` | Speaker's private assumptions | Scontras & Tonhauser 2025 |
| `Goal` | QUD / communicative intention | Kao et al. 2014 |
| `Interp` | Compositional meaning choice | Scontras & Pearl 2021 |
| `Lexicon` | Word meaning uncertainty | Bergen et al. 2016 |

Smart constructors: `RSAScenario.basic`, `.ambiguous`, `.qud`, `.mentalState`, `.lexicalUncertainty`

### Phenomena/ - Empirical Data

**Pure empirical facts only** - no theoretical commitments:

```
Phenomena/
├── GoodmanStuhlmuller2013/Data.lean   # Scalar implicature rates
├── YoonEtAl2020/Data.lean             # Politeness experiment
├── ScontrasPearl2021/Data.lean        # Scope TVJ data
├── GeurtsPouscoulous2009/Data.lean    # Task effects on SI
├── ScalarImplicatures/Data.lean       # SI patterns
└── Semantics/                         # Truth condition judgments
```

**Anti-pattern**: Don't put semantic content in Phenomena/. That belongs in Theories/Montague/.

### Key Patterns

**1. Compositional Negation** (YoonEtAl2020)
```lean
-- Soft negation operator mirrors Montague's pnot
def softNot (p : SoftProp) : SoftProp := fun s => 1 - p s

-- Utterance semantics compositionally derived
def utteranceSemantics : Utterance → SoftProp
  | .notTerrible => softNot (adjMeaning .terrible)  -- compositional!
```

**2. Feature Predicates** (KaoEtAl2014_Metaphor)
```lean
-- Features as Montague adjective denotations (Entity → Bool)
def featureDenotation : Feature → FeaturePred
  | .dangerous => fun m => m.dangerous

-- QUD projection selects feature predicate
def qudEquivCompositional (g : Goal) (m1 m2 : Meaning) : Bool :=
  match goalToFeature g with
  | some f => featureDenotation f m1 == featureDenotation f m2
```

**3. Grounding Theorems**
```lean
-- Prove RSA meaning matches compositional derivation
theorem meaning_from_montague :
    rsaMeaning = compositionalDerivation.meaning := ...
```

## Git Conventions

- Use one-line commit messages (no multi-line body)
- No co-author tags or Claude branding in commits

## Lean Conventions

- `autoImplicit` is disabled (explicit type parameters required)
- `pp.unicode.fun` is enabled for pretty printing
- Exact rational arithmetic (ℚ) for RSA computations
- Real numbers (ℝ) only for mathematical proofs (Zaslavsky et al.)

## Formalization Conventions

**Prefer `sorry` over weakening theorem statements.** When a proof is difficult:
- State the full theorem as intended
- Use `sorry` to mark it incomplete
- Add a `TODO:` comment explaining the proof approach or what's blocking
- Include a proof sketch in the docstring when possible

This is preferable to "backing away" from the full statement by:
- Weakening hypotheses
- Strengthening conclusions
- Simplifying the formalization to make proofs easier

Rationale: It's hard to remember which formalizations are incomplete when they compile without warnings. A `sorry` warning explicitly marks incomplete work for later, while a weakened-but-proved theorem may be forgotten as not fully capturing the intended claim.

## References

### RSA Papers (Implemented)
- Frank & Goodman (2012). Predicting Pragmatic Reasoning in Language Games.
- Goodman & Stuhlmüller (2013). Knowledge and Implicature.
- Kao et al. (2014). Nonliteral Understanding of Number Words.
- Bergen et al. (2016). Pragmatic Reasoning through Semantic Inference.
- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.
- Yoon et al. (2020). Polite Speech Emerges From Competing Social Goals.
- Scontras & Pearl (2021). When pragmatics matters more for truth-value judgments.
- Tessler & Franke (2020). Not unreasonable: Carving vague negation.
- Scontras & Tonhauser (2025). The Semantics and Pragmatics of Gradable Predicates.

### Semantics
- Montague (1973). The Proper Treatment of Quantification.
- Kratzer (1991). Modality / Conditionals.
- Kennedy (2007). Vagueness and Grammar.

### Syntax
- Steedman (2000). The Syntactic Process (CCG).
- Pollard & Sag (1994). Head-Driven Phrase Structure Grammar.
- Chomsky (1995). The Minimalist Program.
