import Linglib.Core.Basic

/-!
# Morphological Infrastructure

Framework-agnostic types for morphological analysis and compositional
morphological rules.

## Typological Classification

- `AttachmentSide`: prefix, suffix, infix, circumfix
- `SelectionDegree`: how restrictive a morpheme's host selection is
- `MorphStatus`: free word / simple clitic / special clitic / affix
- `ParadigmCell`: one cell in a morphological paradigm (form + features)

## Bybee (1985) Relevance Hierarchy

`MorphCategory` classifies morpheme functional categories ordered by
semantic relevance to the stem:

  stem < derivation < valence < voice < aspect < tense < mood < negation < agreement

## Compositional Rules

- `MorphRule σ`: a morphological rule carrying formal AND semantic effects
- `Stem σ`: a lexical stem with its inflectional paradigm

A `MorphRule σ` transforms a stem's surface form, morphosyntactic features,
and meaning of type `σ` simultaneously. Rules where the semantic effect is
`id` (e.g., verb agreement) are marked `isVacuous := true`.

## References

- Bybee, J. L. (1985). Morphology: A Study of the Relation between
  Meaning and Form. Benjamins.
- Zwicky, A. M. (1977). On Clitics. Indiana University Linguistics Club.
- Zwicky, A. M. & Pullum, G. K. (1983). Cliticization vs. Inflection:
  English N'T. *Language* 59(3), 502–513.
- Link, G. (1983). The logical analysis of plurals and mass terms.
- Champollion, L. (2017). Parts of a Whole. OUP.
-/

namespace Core.Morphology

-- ============================================================================
-- §1: Attachment Side
-- ============================================================================

/-- Side on which a bound morpheme attaches to its host. -/
inductive AttachmentSide where
  | prefix     -- attaches before stem (English *un-*, *re-*)
  | suffix     -- attaches after stem (English *-ed*, *-s*, *-n't*)
  | infix      -- inserts within stem (Tagalog *-um-*)
  | circumfix  -- wraps around stem (German *ge-...-t*)
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- §2: Selection Degree
-- ============================================================================

/-- How restrictive a morpheme is about what it can attach to.

Zwicky & Pullum (1983) criterion A: clitics exhibit low selection
(attach to virtually any word), while affixes exhibit high selection
(attach only to specific stems or categories). -/
inductive SelectionDegree where
  /-- Attaches to words of virtually any category (prepositions, verbs,
      adjectives, adverbs). Characteristic of simple clitics. -/
  | low
  /-- Attaches to words of a single major category (e.g., past tense
      *-ed* to verbs, plural *-s* to nouns). Characteristic of
      inflectional affixes. -/
  | singleCategory
  /-- Attaches only to a closed list of stems (e.g., *-n't* only to
      finite auxiliaries). Maximally selective. -/
  | closedClass
  deriving DecidableEq, Repr, BEq

/-- Affixes are more selective than clitics. -/
def SelectionDegree.isHighSelection : SelectionDegree → Bool
  | .low => false
  | .singleCategory => true
  | .closedClass => true

-- ============================================================================
-- §3: Morpheme Status
-- ============================================================================

/-- Morphological status of a linguistic form.

Classifies forms by their degree of syntactic independence and
mode of combination. The clitic–affix boundary is the central
question of Zwicky & Pullum 1983: the criteria A–F serve to
locate a given morpheme on this scale. -/
inductive MorphStatus where
  /-- Syntactically independent word. -/
  | freeWord
  /-- Simple clitic (Zwicky 1977): phonologically reduced variant of
      a free word, occurring in the same syntactic positions.
      English contracted auxiliaries *'s*, *'ve*, *'d*. -/
  | simpleClitic
  /-- Special clitic (Zwicky 1977): either no corresponding free word
      exists, or the distribution differs from the free word.
      Romance pronominal clitics, Latin *-que*. -/
  | specialClitic
  /-- Inflectional affix: paradigmatic, category-preserving, highly
      selective, with possible gaps and idiosyncrasies.
      English *-ed*, *-s*, *-est*, *-n't*. -/
  | inflAffix
  /-- Derivational affix: potentially category-changing, often
      productive but may show lexical restrictions.
      English *-ness*, *un-*, *-ize*. -/
  | derivAffix
  deriving DecidableEq, Repr, BEq

/-- Is this form bound (i.e., not a free word)? -/
def MorphStatus.isBound : MorphStatus → Bool
  | .freeWord => false
  | _ => true

/-- Is this an affix (inflectional or derivational)? -/
def MorphStatus.isAffix : MorphStatus → Bool
  | .inflAffix => true
  | .derivAffix => true
  | _ => false

/-- Is this a clitic (simple or special)? -/
def MorphStatus.isClitic : MorphStatus → Bool
  | .simpleClitic => true
  | .specialClitic => true
  | _ => false

-- ============================================================================
-- §4: Paradigm Cells
-- ============================================================================

/-- A single cell in a morphological paradigm: one form of a lexeme
in a particular morphosyntactic context.

The type parameter `F` is the feature bundle type (e.g., `UD.MorphFeatures`
for a full UD specification, or a simpler domain-specific type). -/
structure ParadigmCell (F : Type) where
  /-- The morphosyntactic features selecting this cell. -/
  features : F
  /-- The surface form, or `none` for a paradigm gap. -/
  form : Option String
  /-- Is this form predictable from the stem by regular rule? -/
  regular : Bool := true
  deriving Repr, BEq

/-- Does this cell represent a paradigm gap? -/
def ParadigmCell.isGap {F : Type} (c : ParadigmCell F) : Bool :=
  c.form.isNone

/-- Does this cell show irregularity (suppletion or unpredictable allomorphy)? -/
def ParadigmCell.isIrregular {F : Type} (c : ParadigmCell F) : Bool :=
  !c.regular && c.form.isSome

-- ============================================================================
-- §5: Bybee (1985) Relevance Hierarchy
-- ============================================================================

/-- Morpheme functional category (Bybee 1985).

Categories are ordered by semantic relevance to the verb stem:
more relevant categories appear closer to the stem in suffixal
morphology. -/
inductive MorphCategory where
  | stem
  | derivation    -- derives verbs from other categories (e.g., *suru*)
  | valence       -- causative, applicative, reciprocal
  | voice         -- passive, potential
  | aspect        -- perfective, imperfective
  | tense         -- past, future, present
  | mood          -- desiderative, subjunctive, imperative
  | negation      -- negation markers
  | agreement     -- subject/object agreement, politeness
  | nonfinite     -- nonfinite markers, interrogative/relative
  | number        -- number marking on nouns (not verb agreement)
  | degree        -- comparative/superlative on adjectives
  deriving Repr, DecidableEq, BEq

/-- Relevance rank: lower = closer to the stem (Bybee 1985).

Stem = 0 (most relevant to verb meaning).
Derivation = 1 (changes verb category).
...
Agreement = 8 (least relevant to verb meaning).

`number` on nouns is ranked 3 (same as voice): it changes the
noun's denotation via Link (1983), unlike verb agreement which
is semantically vacuous.

`degree` on adjectives is ranked 5 (same as tense on verbs):
comparative/superlative morphology compositionally modifies
the adjective's interpretation, analogous to how tense modifies
the verb's temporal reference. -/
def MorphCategory.relevanceRank : MorphCategory → Nat
  | .stem       => 0
  | .derivation => 1
  | .valence    => 2
  | .number     => 3
  | .voice      => 3
  | .aspect     => 4
  | .degree     => 5
  | .tense      => 5
  | .mood       => 6
  | .negation   => 7
  | .agreement  => 8
  | .nonfinite  => 9

/-- A morpheme ordering respects the relevance hierarchy if ranks
are non-decreasing from stem outward. -/
def respectsRelevanceHierarchy (slots : List MorphCategory) : Bool :=
  let ranks := slots.map MorphCategory.relevanceRank
  let pairs := ranks.zip ranks.tail
  pairs.all (λ (a, b) => a ≤ b)

-- ============================================================================
-- §6: Morphological Rules with Semantic Effects
-- ============================================================================

/-- A morphological rule: carries formal AND semantic effects.

    The type parameter `σ` is the meaning type, so this works uniformly
    across `Bool`/`Frac`/`Float` semantic backends.

    Design principle: `semEffect` can be `id` for semantically vacuous
    morphology (e.g., verb agreement `-s`), making it explicit which
    inflections carry semantic content and which don't. -/
structure MorphRule (σ : Type) where
  /-- Which morphological category this rule realizes -/
  category : MorphCategory
  /-- The feature value this rule realizes -/
  value : String
  /-- How the surface form changes -/
  formRule : String → String
  /-- How morphosyntactic features change -/
  featureRule : Features → Features
  /-- Semantic effect (identity if semantically vacuous) -/
  semEffect : σ → σ
  /-- Is this rule semantically vacuous? (agreement, etc.) -/
  isVacuous : Bool := false

/-- A lexical stem: a root meaning plus its morphological paradigm. -/
structure Stem (σ : Type) where
  /-- Base form (lemma) -/
  lemma_ : String
  /-- Syntactic category -/
  cat : UD.UPOS
  /-- Base morphosyntactic features -/
  baseFeatures : Features := {}
  /-- Available inflectional rules -/
  paradigm : List (MorphRule σ)

variable {σ : Type}

/-- Apply a morphological rule to generate an inflected form + meaning. -/
def Stem.inflect (s : Stem σ) (rule : MorphRule σ) (baseMeaning : σ) :
    String × Features × σ :=
  ( rule.formRule s.lemma_
  , rule.featureRule s.baseFeatures
  , rule.semEffect baseMeaning )

/-- Generate all forms in the paradigm (base + inflected). -/
def Stem.allForms (s : Stem σ) (baseMeaning : σ) :
    List (String × Features × σ) :=
  (s.lemma_, s.baseFeatures, baseMeaning) ::
    s.paradigm.map (s.inflect · baseMeaning)

end Core.Morphology
