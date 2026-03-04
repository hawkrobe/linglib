# CLAUDE.md

This file provides guidance to Claude Code when working with this repository.

## Build Commands

```bash
lake build          # Build the entire project
lake build Linglib  # Build just the main library
```

## Scratch Area

When writing temporary test files (e.g., to test a Lean snippet before integrating it), write them under `scratch/` in the project root rather than `/tmp`. This directory is gitignored and stays within the project sandbox, avoiding permission prompts.

```bash
mkdir -p scratch
# Write test files as scratch/test_foo.lean, etc.
```

## Project Overview

Linglib is a Lean 4 library for formalizing linguistic theories and connecting them to computational pragmatics (RSA - Rational Speech Acts). The library emphasizes **grounding**: RSA models derive their meaning functions from Montague compositional semantics rather than stipulating them.

## Architecture

### Core Principle: Compositional Grounding

RSA implementations should **directly import and use** meaning functions from compositional semantics (`Theories/Semantics/`), not stipulate their own. The grounding is structural — by construction, not by theorem.

```
Semantics/Montague/ + Semantics/Lexical/ →  Adjective/Numeral/Modal/Attitude semantics
    ↓
Semantics/Lexical/Determiner/Quantifier → ⟦some⟧, ⟦all⟧, ⟦most⟧
    ↓
Fragments/                →  Reusable RSA domains (Quantities, Scales, Degrees)
    ↓
Phenomena/X/Studies/  →  Paper replications that USE theory-layer semantics
```

Example grounding pattern:
```lean
-- In Phenomena/Imprecision/Studies/LassiterGoodman2017.lean
-- RSA imports and uses adjective theory semantics directly
import Linglib.Theories.Semantics.Lexical.Adjective.Theory

open Semantics.Lexical.Adjective (positiveMeaning negativeMeaning)

def tallMeaning (θ : Threshold) (h : Height) : Bool :=
  positiveMeaning h θ   -- grounded by construction, not by bridge theorem
```

**Anti-pattern**: stipulating meaning functions inline and then proving equivalence in a Bridge file. If the RSA model's meaning is the same as a theory-layer function, import and call it directly.

### Dependency Discipline: Theories → Fragments → Phenomena

The three main directories form a strict dependency hierarchy:

```
Theories/     = library code     (types, operators, predicates)
    ↑
Fragments/    = configuration    (lexical entries, parameterized by Theory types)
    ↑
Phenomena/    = test suite       (empirical data + theorems verifying predictions)
```

The dependency arrow is always **downstream**: Phenomena imports Fragments + Theories, Fragments imports Theories, and never the reverse. Each layer only knows about the layers above it.

**Fragments never import Phenomena.** Fragment entries are "pure" lexical data typed by Theory types. They don't know about empirical observations.

**Phenomena use a Data/Studies split.** Each phenomenon directory separates observations from explanations:

- **Data files** (top level of each phenomenon directory): Pure empirical observations — judgments, experimental results, cross-linguistic patterns. Imports only `Core.*`. No imports from `Theories/`. These are the shared facts that any theory must account for.
- **`Studies/` subdirectory**: Theoretical analyses of the data. Each study file connects a theory to the observations, proving predictions, deriving judgments, or replicating a paper's model. Study files can import `Theories/`, `Fragments/`, and data files from the same phenomenon.

Study files are **self-contained**: they include the paper's data, model, and predictions in one file. This makes it easy to formalize a new paper — everything about that paper lives in one place. If data from a study later proves useful to other theories, it can be promoted to a top-level data file, but there's no pressure to separate prematurely.

Study file naming uses author-year format: `Studies/Pollock1989.lean`, `Studies/SagWasowBender2003.lean`, `Studies/KaoEtAl2014.lean`. The study is the natural unit — whether it's an RSA paper replication, a Minimalist analysis, or a corpus study.

Namespace convention: `Phenomena.{Phenomenon}.Studies.{AuthorYear}`, matching the file path. Example: `Phenomena.WordOrder.Studies.Pollock1989`.

**Chronological dependency in study files.** Cross-references between study files must respect chronological order: a study file may reference and prove consistency with *older* papers, but not *newer* ones. For example, `CohnGordonEtAl2019.lean` can prove a theorem connecting to `SedivyEtAl1999.lean` (since 1999 predates 2019), but `SedivyEtAl1999.lean` must not reference Cohn-Gordon et al. 2019. This ensures each study file's claims are grounded in knowledge available at the time of publication, and avoids anachronistic dependencies.

**Derive, don't duplicate.** When Phenomena files reference Fragment data (e.g., particle forms, bias properties), they should derive values from Fragment fields rather than duplicating them as string literals. This makes the connection true by construction rather than requiring bridge theorems that test redundant copies.

**Dependency discipline is fully enforced**: 0 violations in both directions (Theories→Phenomena and Fragments→Phenomena).

**Study files live in `Phenomena/`, not `Theories/`.** Files that import both `Theories/` and `Phenomena/` data belong in the relevant phenomenon's `Studies/` subdirectory. `Theories/Pragmatics/RSA/Implementations/` is only for pure RSA theory (types, operators) that doesn't reference empirical data.

### Directory Structure

```
Linglib/
├── Core/                    # Framework-agnostic infrastructure
│   ├── Interfaces/          # Theory comparison interfaces (binding, scope, implicature, ...)
│   └── ~25 files            # Shared types, propositions, modality, scales, time, etc.
│
├── Fragments/               # Lexical entries parameterized by Theory types
│   ├── English/             # English lexicon (16 files)
│   ├── {Language}/          # 30 languages total (Japanese, Mandarin, German, ...)
│   └── *.lean               # Cross-linguistic RSA domains (Quantities, Scales, Degrees, ...)
│
├── Theories/                # Pure theory (types, operators, predicates — no Phenomena imports)
│   ├── Syntax/              # Syntactic frameworks (47 files)
│   │   ├── Minimalism/      # Minimalist Program
│   │   ├── CCG/             # Combinatory Categorial Grammar
│   │   ├── HPSG/            # Head-Driven Phrase Structure Grammar
│   │   ├── DependencyGrammar/ # Word Grammar
│   │   └── ConstructionGrammar/ # Construction Grammar
│   ├── Semantics/           # Semantic theories (200 files, see below)
│   ├── Pragmatics/          # Pragmatic frameworks (82 files)
│   │   ├── RSA/             # Rational Speech Acts (see below)
│   │   ├── NeoGricean/      # Categorical implicature theory
│   │   └── DTS/             # Decision-Theoretic Semantics
│   └── Morphology/          # Morphological theory
│
├── Phenomena/               # Empirical data + studies (see below)
│
└── Comparisons/             # Cross-theory comparisons (28 files)
```

### Theories/Semantics/ - Semantic Theories

The `Semantics/` directory is organized by architectural foundations (what kind of thing is a meaning?) and domain-specific theories (that plug into those foundations):

**Architectural foundations:**
- `Montague/` — Montague architecture (8 files): `Basic.lean` (Prop', pnot, pand, por), `Composition.lean` (FA, PM, TN), `Variables.lean` (assignments), `Modification.lean`, `Conjunction.lean` (Partee & Rooth), `PTQ.lean` (Montague 1973), `Lexicon.lean`, `Derivation.lean`
- `Intensional/` — Core intensional types (`Basic.lean`) + `Situations/` (situation semantics)
- `Dynamic/` — Dynamic semantics (entire subtree)
- `Events/` — Event semantics (entire subtree)
- `TypeTheoretic/` — Type-Theoretic Representations (TTR)
- `Probabilistic/` — `Graded/` (graded propositions), `Measurement/`, `Frames/`, `SDS/` (stochastic/decision-theoretic)

**Domain-specific theories:**
- `Modality/` — Modal semantics (Kratzer, simple, ability, kernel, comparison, etc.)
- `Conditionals/` — Material, strict, variably-strict, counterfactual conditionals
- `Attitudes/` — Propositional attitude verbs (doxastic, preferential, parasitic, etc.)
- `Tense/` — Tense/aspect: `Basic.lean` (intensional foundations), `Compositional.lean` (extensional tense), sequence of tense, evidentials, temporal adverbials/connectives
- `Questions/` — Question denotations, answerhood, decision theory, inquisitive semantics
- `Reference/` — Reference and binding
- `Causation/` — Causative verb semantics
- `Focus/` — Focus interpretation, particles, domain widening
- `Presupposition/` — Presupposition projection, local context, belief embedding
- `Entailment/` — Entailment, monotonicity, polarity, anti-additivity, Strawson entailment
- `Mood/` — Sentence mood (declarative, interrogative, imperative)

**Word-class semantics (`Lexical/`):**
- `Adjective/` — Gradable adjective semantics
- `Noun/` — Noun semantics
- `Verb/` — Aspect, habituals, change-of-state
- `Determiner/` — Quantifiers (`⟦some⟧`, `⟦all⟧`, `⟦most⟧`), definites, demonstratives
- `Numeral/` — Lower-bound vs bilateral numeral semantics
- `Particle/`, `Plural/`, `Expressives/`

### Theories/Pragmatics/RSA/ - Rational Speech Acts

RSA theory core (types, operators, the `RSAConfig` structure) lives in `Theories/Pragmatics/RSA/`. Paper implementations (RSA models of specific empirical phenomena) live in the relevant phenomenon's `Studies/` subdirectory under `Phenomena/` — e.g., `Phenomena/Modality/Studies/Alsop2024.lean`, `Phenomena/ScalarImplicatures/GoodmanStuhlmuller2013/`, `Phenomena/Nonliteral/Metaphor/KaoEtAl2014.lean`.

```
Theories/Pragmatics/RSA/
├── Core/
│   ├── Basic.lean           # RSAScenario (ℚ), L0, S1, L1
│   ├── Config.lean          # RSAConfig (ℝ), L1_marginal
│   ├── Model.lean           # RSAScenarioR (ℝ) for proofs
│   └── Intensional.lean     # Belief states, speakerCredence
├── Extensions/
│   ├── LexicalUncertainty/  # Bergen et al. 2016
│   └── InformationTheory/   # Zaslavsky et al. rate-distortion
└── ScalarImplicatures/      # Embedded SI handling (core)

Phenomena/
├── Modality/Studies/
│   ├── Alsop2024.lean                   # Free choice any (GI-RSA)
│   └── ChampollionAlsopGrosu2019.lean   # Free choice disjunction
├── ScalarImplicatures/GoodmanStuhlmuller2013/
│   └── ...                              # Numeral/quantifier implicatures
├── Nonliteral/Metaphor/KaoEtAl2014.lean # Metaphor comprehension
└── ...                                  # RSA studies organized by phenomenon
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

### Phenomena/ - Empirical Data & Theory Bridges

`Phenomena/` contains ~260 files organized into 38 basic-level phenomenon categories:

```
Phenomena/
│   WordOrder/
│   │   ├── Basic.lean                 # Observations (theory-neutral)
│   │   ├── SubjectAuxInversion.lean   # Observations (theory-neutral)
│   │   ├── Typology.lean              # Observations (theory-neutral)
│   │   └── Studies/                   # Theoretical analyses
│   │       ├── Pollock1989.lean       # Verb movement analysis
│   │       ├── SagWasowBender2003.lean # HPSG inversion analysis
│   │       ├── Hudson1990.lean        # DG inversion analysis
│   │       └── ...
│   ScalarImplicatures/
│   │   ├── Basic.lean                 # Observations
│   │   └── Studies/
│   │       ├── VanTielEtAl2016.lean   # Scale diversity data + analysis
│   │       ├── Ronai2024.lean         # Processing study
│   │       └── ...
│   ... (30+ phenomenon categories)
```

**Anti-pattern**: Don't put pure theory in Phenomena/. Pure theory (types, operators, predicates that don't reference empirical data) belongs in Theories/.

### Phenomena Grouping Principles

Phenomena are organized at the **basic level** — the level at which a linguist would naturally describe the phenomenon being studied, not at the level of individual studies or at overly broad superordinate categories.

**1. Group by phenomenon, not by study.** Directories are named for the phenomenon (`ScalarImplicatures/`, `Gradability/`), not for the paper (`GoodmanStuhlmuller2013/`). Individual studies go inside the phenomenon's `Studies/` subdirectory (e.g., `ScalarImplicatures/Studies/VanTielEtAl2016.lean`). When a study is complex enough, it gets its own subdirectory (e.g., `Aspect/Studies/AlstottAravind2026/`).

**2. Merge singletons into broader categories.** A phenomenon that would have only 1-2 files at the top level should be merged into a broader category. For example, `Metaphor/` and `Humor/` merge into `Nonliteral/`; `WeakEvidenceEffect/` and `ArgumentativeFraming/` merge into `ScalarImplicatures/`; `Islands/` merges into `FillerGap/`; `Honorifics/` merges into `Politeness/`.

**3. Aim for basic-level categories.** The right granularity is approximately 30-40 top-level directories. Categories should be neither too specific (one study per directory) nor too broad (dozens of unrelated files lumped together). Each directory should represent a recognizable subfield that a linguist could name.

**4. Studies live in `Studies/`, not in `Theories/`.** Files that import both `Theories/` and `Phenomena/` data belong in the relevant phenomenon's `Studies/` subdirectory. Each study file should connect theories to one phenomenon — don't create cross-phenomenon study files.

**5. Cross-cutting phenomena stay at the top level.** Phenomena like `Negation/` or `Coordination/` that span syntax, semantics, and pragmatics are not forced into a single linguistic level — they stay as top-level phenomenon directories.

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

## Writing Voice (Blog & Prose)

When writing blog posts, documentation prose, or any non-code text for this project, match this style:

- **Lead with puzzles and tensions.** Open sections by setting up a concrete empirical or theoretical puzzle — two accounts that seem to predict the same thing, a surprising gap between theory and data, a question that is "easy to pose informally and hard to answer rigorously." Then use the rest of the section to resolve or sharpen the tension.
- **Anchor abstract points in concrete examples.** Don't say "formalization forces precision" — say what specific thing became precise (e.g., "informativity with respect to *what*? Over which set of alternatives? With what prior?"). Use real linguistic examples ("some students passed," "the upside-down martini glass in a wire stand").
- **Enthusiastic but rigorous.** The tone is a working scientist genuinely excited about the intellectual structure, not a tutorial writer explaining basics. Use phrases like "remarkable," "striking," "turns out to be illuminating" when warranted, but always back them with substance. Never hype without content.
- **Short, punchy sentences for key claims.** Alternate longer expository sentences with short declarative ones for emphasis: "The quantifiers are *determined* by their inferential behavior." "Either way, the dependency is explicit rather than implicit."
- **First-person plural ("we") for project decisions**, but not the royal we — it should feel like narrating shared intellectual work, as in an academic paper.
- **No bullet-point style for the main text.** Use flowing prose with section headers. Bullet lists are fine for inventories (e.g., "What's here so far") but the argumentative core should be paragraphs.
- **Connect to the broader field.** Reference the relevant literature naturally (e.g., "Barwise and Cooper (1981) called this a *generalized quantifier*"), and situate linglib's design choices in the context of existing debates.

## Bibliography

The blog bibliography is generated from `blog/data/references.bib` (BibTeX). When adding or formalizing a new paper:

1. **Add the entry to `references.bib`** using standard BibTeX format. Use the key format `lastname-lastname-year` (lowercase, hyphenated). Include custom fields `subfield`, `role`, and `sources` (see comments at top of file for values).
2. **Always validate DOIs and URLs against the actual publication.** Do not guess or fabricate DOIs — look them up on the publisher's site, Google Scholar, or Semantic Scholar. Hallucinated DOIs are worse than missing DOIs. If you cannot verify a DOI, omit it.
3. **Add `@cite{key}` in the Lean file's docstring** to cross-reference it (see below).
4. **Regenerate the markdown**: `python3 blog/scripts/gen_bibliography.py`
5. **Commit both files** (`references.bib` and the generated `bibliography.md`).

### `@cite{key}` — Cross-referencing papers in Lean files

**Every academic citation in a `.lean` file must use `@cite{key}` — no raw inline citations.** This applies everywhere: module docstrings (`/-! ... -/`), declaration docstrings (`/-- ... -/`), and regular comments (`-- ...`). Never write `Kratzer (1991)` or `Kratzer 1991` — always write `@cite{kratzer-1991}`. For possessives, write `@cite{kratzer-1991}'s`. For parenthetical year-only references after the key is established, write `(@cite{kratzer-1991})`.

If a paper has no entry in `references.bib`, add one before using `@cite{key}`.

```lean
/-!
# Frank & Goodman (2012) @cite{frank-goodman-2012}

Predicting Pragmatic Reasoning in Language Games. Science 336(6084): 998.
...
-/
```

The generator script scans all `.lean` files for `@cite{...}` patterns and:
- Appends a "cited in" reverse index to each bibliography entry on the blog
- Validates that every `@cite{key}` matches an entry in `references.bib`
- Reports unknown keys as warnings (run `--check` to validate without regenerating)

Place `@cite{key}` in the module docstring header, next to the author/year line. For files that cite multiple papers, use multiple `@cite{key}` tags. The key must exactly match the BibTeX entry key in `references.bib`.

### Hallucination prevention for bibliography entries

New bib entries are high-risk for hallucinated metadata. Every field — title, journal, year, volume, pages, DOI — must be verified against the actual publication, not recalled from memory. Specific rules:

1. **Always include a DOI when one exists.** Look it up on the publisher's site, Google Scholar, or Semantic Scholar. If you cannot verify a DOI exists, omit it — a missing DOI is better than a fabricated one.
2. **Validate title and journal name exactly.** Do not paraphrase titles. Copy them character-for-character from the publication. Journal names must match the official name (e.g., "Psychological Review" not "Cognitive Psychology"; "Language Acquisition" not "Journal of Child Language").
3. **Verify volume/issue/pages against the actual publication.** These are frequently hallucinated — especially for recent papers (2023+) that may not be in training data.
4. **When in doubt, leave fields blank rather than guessing.** A bib entry with just `author`, `year`, `title`, and `doi` is more trustworthy than one with fabricated page numbers.

## Git Conventions

- Use one-line commit messages (no multi-line body)
- No co-author tags or Claude branding in commits
- **Update `CHANGELOG.md` before committing/pushing new work** — bump the version and describe changes
- **Versioning**: Use `0.MAJOR.MINOR` — bump the minor version (third number) for incremental additions and refactoring within a development phase; reserve bumping the major version (second number) for significant milestones (e.g., new theoretical framework, major architectural change). Example: after 0.213.0, the next versions are 0.213.1, 0.213.2, ..., not 0.214.0

## Lean Conventions

- `autoImplicit` is disabled (explicit type parameters required)
- `pp.unicode.fun` is enabled for pretty printing
- Prefer Unicode `λ` over `fun` in code
- Exact rational arithmetic (ℚ) for RSA computations
- Real numbers (ℝ) only for mathematical proofs (Zaslavsky et al.)
- Every `.lean` file should have a `/-! ... -/` module docstring summarizing the file's purpose and key definitions. **The docstring must come after all `import` statements** — Lean requires imports to be the very first non-comment lines in a file; placing a `/-! ... -/` block before imports causes `invalid 'import' command` errors
- Always close `section` blocks with matching `end` — unclosed sections silently persist scope, causing variables and hypotheses to leak into subsequent declarations
- Scope `set_option` to individual declarations (`set_option maxHeartbeats 400000 in theorem ...`), not at file level
- Prefer `simp only [lemma1, lemma2]` over bare `simp` — bare `simp` is fragile because changes to the default simp set break proofs at a distance
- Only import what's needed — unnecessary imports slow builds and create false dependency edges

### Proof Style

**Tactic preference hierarchy** (most preferred first):
1. `exact`/`rfl`/`⟨rfl, rfl⟩` — direct term proofs when the goal is definitionally equal
2. `omega`, `linarith`, `ring` — decision procedures for their domains
3. `simp only [lemma1, lemma2]` — targeted rewriting with explicit lemma sets
4. `native_decide` — for finite data-checking theorems over `World4`, `Bool`, etc.
5. Bare `simp` — avoid; fragile and opaque

Never silently replace a `sorry` with `native_decide` or `decide` on a theorem that isn't a finite data check. If a theorem expresses a general property (universally quantified over `Kernel`, `BProp`, etc.), it should have a structured proof even if the current types are finite enough for `decide` to close it.

**Structured proofs for readability.** For non-trivial proofs:
- Use `have` to name intermediate results, `suffices` to reduce to a key subgoal, and `obtain` to destructure existentials
- Use `calc` blocks for chains of equalities or inequalities
- Extract reusable proof steps into private helper lemmas (e.g., `filter_isEmpty_eq_all_not` in `Kernel.lean`) — if two proofs need the same step, factor it out

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

**Do not encode conclusions as definitions — derive them from deeper principles.**

Bad pattern (stipulative):
```lean
def naCanBridge := true
def bareCanBridge (n) := n.isRelational
theorem na_can_bridge : naCanBridge = true := rfl  -- Trivially true by definition!
```

Good pattern (derived):
```lean
-- Define structural properties
inductive Pred (E S : Type) : Arity → Type where
  | pred1 : (E → S → Bool) → Pred E S .one
  | pred2 : (E → E → S → Bool) → Pred E S .two

-- Define π as a type-changing operation
def π (P : Pred E S .one) (R : Pred2 E S) : Pred E S .two := ...

-- Define bridging capability structurally
def canBridge (a : Arity) := a == .two

-- DERIVE that π enables bridging (follows from types)
theorem pi_enables_bridging (P : Pred E S .one) (R : Pred2 E S) :
    canBridge (π P R).arity = true := rfl  -- Non-trivial: follows from π's type signature
```

The difference:
- In the bad pattern, the "theorem" just unpacks what we stipulated
- In the good pattern, the theorem follows from deeper structural properties
- The good pattern is genuinely explanatory and enables cumulative building

**Build cumulatively — later modules should import and use earlier ones.**

When formalizing related papers:
- Identify shared theoretical foundations (e.g., Barker's π for all possession/bridging work)
- Put shared foundations in a common module
- Have paper-specific modules IMPORT and USE the shared definitions
- Derive paper-specific results from the shared framework

Example: Ahn & Zhu (2025) should import Barker (2011)'s π operator, not redefine it. Their bridging results should derive from Barker's type-shifting framework.

**Maximize interconnection density — changes should break things.**

The point of linglib is to hook everything together as densely as possible so we can detect incompatibility, contradiction, or cascading breakage when one thing changes. Prefer:
- Per-datum verification theorems (one per verb/entry so changing a field breaks exactly one theorem)
- Bridge theorems connecting Fragment entries to Theory predictions (like `BuilderProperties.lean`, `LeftPeriphery.lean` section I)
- Grounding theorems connecting abstract Boolean layers to compositional semantics
- Cross-layer agreement theorems proving different representations are consistent (e.g., three independent derivations of SelectionClass all agree)

**Do not cite equation, table, or section numbers from memory.** References to specific locations within a paper — "eq. (39)", "Table 1", "§5.1", "Theorem 6" — are the single most hallucinated category in this project's history. Rules:

- **Never cite equation/table/section/theorem numbers unless you are looking at the paper.** If you cannot verify the number, describe the content instead (e.g., "the granularity function" rather than "eq. (45)").
- **Never cite specific parameter values (α = 3, r² = 0.99, P(whale) = 1/100) without verification.** State that the model uses a rationality parameter rather than asserting its exact value.
- **Never cite specific page ranges from memory.** Page numbers are arbitrary and impossible to recall accurately. Omit them or verify against the PDF.
- **Prefer content descriptions over location references.** "Kratzer's ordering source semantics" is verifiable; "Kratzer (1991) p. 644" requires checking. The former survives paper re-pagination; the latter doesn't.

If a docstring needs to reference a specific result in a paper, use `-- UNVERIFIED: eq. 39` to flag it for human review. This makes unverified location claims grep-able and auditable.

**Test both layers of multi-component state.** When a formalization has state with multiple independent components (e.g., PIP's `Discourse = info × labels`), test each component independently. A bug in one component can hide behind passing tests on the other — label-only tests can pass while the info state is vacuously empty. Include:
- **Positive consistency tests**: show the output is non-empty from reasonable input (e.g., `stone_discourse_consistent`, `bathroom_sentence_consistent`). Construct a specific witness assignment and prove it survives the full pipeline.
- **Negative rejection tests**: show specific values are correctly rejected (e.g., `stone_discourse_rejects_unbound`, `bathroom_rejects_nonupstairs`). These confirm the operators genuinely filter rather than vacuously accepting everything.
- **Structural property tests**: verify key properties of intermediate operators (e.g., `modalExpand_adds_accessible`, `register_preserves`). These catch architectural bugs before they manifest in end-to-end tests.

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
