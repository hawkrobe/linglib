---
title: "Library Overview"
---

Linglib is an effort to build a unified library of formal linguistics in the Lean proof assistant, covering semantics, pragmatics, and their interfaces.

---

## RSA Implementations

Rational Speech Acts models from the literature. Each implementation includes the core model, example scenarios, and key predictions.

### Foundational
- **FrankGoodman2012** — Reference games, the original RSA paper
- **GoodmanStuhlmuller2013** — Scalar implicature with speaker knowledge
- **Franke2011** — Game-theoretic pragmatics, iterated best response

### Scalar Implicature
- **BergenGoodman2015** — Lexical uncertainty
- **PottsEtAl2016** — Embedded implicatures
- **CremersWilcoxSpector2023** — Exhaustivity vs anti-exhaustivity

### Non-literal Language
- **KaoEtAl2014_Hyperbole** — Hyperbole comprehension with affect
- **KaoEtAl2014_Metaphor** — Feature-based metaphor interpretation
- **TesslerFranke2020** — Flexible negation ("not unhappy")

### Gradable Expressions
- **LassiterGoodman2017** — Adjectival vagueness
- **ScontrasTonhauser2025** — Gradable predicates and projection
- **QingEtAl2016** — Degree semantics

### Social & Discourse
- **YoonEtAl2020** — Politeness (face-saving, information, honesty)
- **HawkinsGweonGoodman2021** — Pedagogy and learning
- **HawkinsEtAl2025** — Convention formation

### Questions & Scope
- **ScontrasPearl2021** — Scope ambiguity resolution
- **ScopeFreezing** — Inverse scope blocking

### Other Phenomena
- **ChampollionAlsopGrosu2019** — Free choice disjunction
- **TesslerGoodman2019** — Generic generalizations
- **GrusdtLassiterFranke2022** — Conditionals
- **BellerGerstenberg2025** — Causal language
- **HeKaiserIskarous2025** — Presupposition

---

## Montague Semantics

Compositional semantics following the Montague tradition.

### Core
- **Basic** — Propositions, truth conditions, entailment
- **Quantifiers** — Generalized quantifiers (∀, ∃, most)
- **Lexicon** — Word meanings and composition
- **Derivation** — Syntactic derivations to semantic values

### Nominals
- **Determiner** — Articles, demonstratives, quantificational determiners
- **Noun** — Common nouns, relational nouns, kind reference
- **Plural** — Plural semantics, distributivity, cumulativity

### Predicates
- **Adjective** — Gradable and non-gradable adjectives
- **Verb** — Event semantics, aspect, attitudes, habituals
- **Modal** — Kratzer-style modality, conditionals

### Sentence-level
- **Sentence** — Presupposition, entailment, focus
- **Question** — Partition semantics, exhaustivity, answerhood

### Extensions
- **Intensional** — Possible worlds, propositions as sets
- **Frames** — Frame semantics integration

---

## Phenomena

Empirical linguistic data organized by phenomenon. Each module contains judgments, experimental results, and cross-linguistic patterns.

### Implicature & Inference
- **ScalarImplicatures** — "some" → "not all", embedded SI
- **Presupposition** — Triggers, projection, accommodation
- **Entailment** — Monotonicity, polarity

### Reference & Anaphora
- **Reference** — Definites, indefinites, reference games
- **Anaphora** — Pronouns, reflexives, donkey sentences

### Questions & Focus
- **Questions** — Wh-questions, polar questions, exhaustivity
- **Focus** — Information structure, alternatives, verum focus

### Modification & Gradability
- **Gradability** — Vagueness, comparison, degree modification
- **Imprecision** — Approximation, "around N"

### Modality & Conditionals
- **Modality** — Epistemic, deontic, free choice
- **Conditionals** — Indicative, counterfactual, biscuit

### Quantification
- **Quantification** — Scope, binding, donkey anaphora
- **Plurals** — Distributivity, non-maximality, homogeneity

### Other
- **Politeness** — Face, indirectness
- **Generics** — Kind reference, characterizing sentences
- **Negation** — Constituent vs sentential, metalinguistic

---

## Syntax Theories

Multiple syntactic frameworks, primarily as infrastructure for semantic composition.

### Primary
- **CCG** — Combinatory Categorial Grammar (main syntax-semantics interface)

### Additional
- **HPSG** — Head-Driven Phrase Structure Grammar
- **Minimalism** — Minimalist Program (Merge, Move, phases)
- **DependencyGrammar** — Word Grammar, dependency structures

---

## Other Theories

### Neo-Gricean
- **Exhaustivity** — EXH operator, innocent exclusion
- **AlternativeGeneration** — Lexical and structural alternatives
- **BarLevFox2020** — Innocent inclusion for free choice

### Dynamic Semantics
- **DynamicSemantics** — File change semantics, DRT
- **BilateralUpdateSemantics** — Rejection conditions

### Comparisons
- **FreeChoice** — RSA vs grammatical approaches
- **ScopeFreezing** — CCG vs Minimalism mechanisms
- **CommandRelations** — Barker & Pullum lattice theory

---

## Core Infrastructure

### Probability & Information
- **Distribution** — Probability distributions over finite types
- **Softmax** — Soft argmax, entropy, temperature limits
- **InformationTheory** — KL divergence, mutual information

### Semantics
- **Proposition** — `Prop' = World → Bool`
- **QUD** — Questions under discussion
- **Polarity** — Upward/downward entailing contexts

### Utilities
- **Grammar** — Abstract grammar typeclass
- **Parse** — Simple parsing infrastructure
- **Pipeline** — Theory comparison pipelines

---

## Quick Links

- [API Documentation](/docs/Linglib.html) — Full auto-generated docs
- [GitHub Repository](https://github.com/hawkrobe/linglib)
- [Roadmap](/roadmap/) — Future work and TODOs
