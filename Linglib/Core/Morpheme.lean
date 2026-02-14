/-!
# Morpheme Infrastructure

Framework-agnostic types for morphological analysis: morpheme status,
attachment mode, paradigm structure, and the Bybee (1985) relevance
hierarchy.

## Morpheme Status

The five-way classification of linguistic forms by their degree of
syntactic independence and mode of combination (Zwicky & Pullum 1983,
Zwicky 1977):

| Status | Selection | Gaps | Idiosyncrasies | Example |
|--------|-----------|------|----------------|---------|
| Free word | — | — | — | English *not* |
| Simple clitic | low | none | none | English *'s*, *'ve* |
| Special clitic | varies | varies | varies | Romance pronominal clitics |
| Inflectional affix | high | common | common | English *-ed*, *-s*, *-n't* |
| Derivational affix | high | common | common | English *-ness*, *un-* |

## Bybee Relevance Hierarchy

Morpheme functional categories ordered by semantic relevance to the
stem (Bybee 1985). Categories closer to the stem are more relevant
to verb meaning.

  stem < derivation < valence < voice < aspect < tense < mood < negation < agreement

## References

- Bybee, J. L. (1985). Morphology: A Study of the Relation between
  Meaning and Form. Benjamins.
- Zwicky, A. M. (1977). On Clitics. Indiana University Linguistics Club.
- Zwicky, A. M. & Pullum, G. K. (1983). Cliticization vs. Inflection:
  English N'T. *Language* 59(3), 502–513.
-/

namespace Core.Morpheme

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
  deriving Repr, DecidableEq, BEq

/-- Relevance rank: lower = closer to the stem (Bybee 1985).

Stem = 0 (most relevant to verb meaning).
Derivation = 1 (changes verb category).
...
Agreement = 8 (least relevant to verb meaning). -/
def MorphCategory.relevanceRank : MorphCategory → Nat
  | .stem       => 0
  | .derivation => 1
  | .valence    => 2
  | .voice      => 3
  | .aspect     => 4
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

end Core.Morpheme
