import Linglib.Core.Lexical.Word

/-!
# Morphological Infrastructure
@cite{bybee-1985} @cite{champollion-2017} @cite{link-1983} @cite{zwicky-pullum-1983}

Framework-agnostic types for morphological analysis and compositional
morphological rules.

## Typological Classification

- `AttachmentSide`: prefix, suffix, infix, circumfix
- `SelectionDegree`: how restrictive a morpheme's host selection is
- `MorphStatus`: free word / simple clitic / special clitic / affix
- `ParadigmCell`: one cell in a morphological paradigm (form + features)

## @cite{bybee-1985} Relevance Hierarchy

`MorphCategory` classifies morpheme functional categories ordered by
semantic relevance to the stem:

  stem < derivation < valence < voice < aspect < tense < mood < negation < agreement

## Compositional Rules

- `MorphRule σ`: a morphological rule carrying formal AND semantic effects
- `Stem σ`: a lexical stem with its inflectional paradigm

A `MorphRule σ` transforms a stem's surface form, morphosyntactic features,
and meaning of type `σ` simultaneously. Rules where the word-level semantic
contribution is delegated to a higher composition layer (e.g., tense rules
that delegate to `Theories/Semantics/Tense/`, agreement rules that contribute
no truth-conditional meaning) carry `delegatedSemantics := true`. The Bool
flag is **not** a claim that the morpheme is meaningless — Bybee 1985 Ch 1
§3 explicitly argues against the vacuity-of-inflection position. It tracks
*where* the meaning is computed (delegate to Theory layer vs. compute at
the morphological word level), not whether meaning exists.

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
  deriving DecidableEq, Repr

/-- Typological position classification for formatives.
    @cite{bickel-nichols-2001} Table 2.

    Superset of `AttachmentSide`: adds simulfixation (process morphology),
    detached formatives (Wackernagel clitics, free auxiliaries), and
    endoclisis (clitic insertion inside a word). -/
inductive FormativePosition where
  | praefixed     -- formative precedes host (= `AttachmentSide.prefix`)
  | postfixed     -- formative follows host (= `AttachmentSide.suffix`)
  | infixed       -- formative inserted within host (= `AttachmentSide.infix`)
  | circumfixed   -- formative wraps host (= `AttachmentSide.circumfix`)
  | simultaneous  -- non-segmental: ablaut, umlaut, tonal change, reduplication
  | detached      -- syntactically free formative (auxiliary, Wackernagel clitic)
  | endoclitic    -- clitic inserted inside a word (Udi, European Portuguese)
  deriving DecidableEq, Repr

/-- Map `AttachmentSide` to the richer `FormativePosition` classification. -/
def AttachmentSide.toFormativePosition : AttachmentSide → FormativePosition
  | .prefix    => .praefixed
  | .suffix    => .postfixed
  | .infix     => .infixed
  | .circumfix => .circumfixed

-- ============================================================================
-- §2: Selection Degree
-- ============================================================================

/-- How restrictive a morpheme is about what it can attach to.

@cite{zwicky-pullum-1983} criterion A: clitics exhibit low selection
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
  deriving DecidableEq, Repr

/-- Affixes are more selective than clitics. -/
def SelectionDegree.IsHighSelection (s : SelectionDegree) : Prop :=
  s ≠ .low

instance : DecidablePred SelectionDegree.IsHighSelection := fun s => by
  unfold SelectionDegree.IsHighSelection; exact inferInstance

-- ============================================================================
-- §3: Morpheme Status
-- ============================================================================

/-- Morphological status of a linguistic form.

Classifies forms by their degree of syntactic independence and
mode of combination. The clitic–affix boundary is the central
question of @cite{zwicky-pullum-1983}: the criteria A–F serve to
locate a given morpheme on this scale. -/
inductive MorphStatus where
  /-- Syntactically independent word. -/
  | freeWord
  /-- Simple clitic: phonologically bound form that can attach to
      hosts of virtually any syntactic category.
      @cite{bickel-nichols-2001}: defined primarily by low selectivity
      (categorical freedom) + phonological dependence, not necessarily
      by being a reduced variant of a free word. Many simple clitics
      have no free-word counterpart (Latin *-que*). English contracted
      auxiliaries (*'s*, *'ve*, *'d*) are a subcase where a free variant
      exists. -/
  | simpleClitic
  /-- Special clitic: either no corresponding free word
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
  deriving DecidableEq, Repr

/-- Is this an affix (inflectional or derivational)? -/
def MorphStatus.IsAffix (s : MorphStatus) : Prop :=
  s = .inflAffix ∨ s = .derivAffix

instance : DecidablePred MorphStatus.IsAffix :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Is this a clitic (simple or special)? -/
def MorphStatus.IsClitic (s : MorphStatus) : Prop :=
  s = .simpleClitic ∨ s = .specialClitic

instance : DecidablePred MorphStatus.IsClitic :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

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
def ParadigmCell.isGap {F : Type} (c : ParadigmCell F) : Prop :=
  c.form = none

instance {F : Type} (c : ParadigmCell F) : Decidable c.isGap :=
  inferInstanceAs (Decidable (c.form = none))

/-- Does this cell show irregularity (suppletion or unpredictable allomorphy)? -/
def ParadigmCell.isIrregular {F : Type} (c : ParadigmCell F) : Prop :=
  c.regular = false ∧ c.form ≠ none

instance {F : Type} (c : ParadigmCell F) : Decidable c.isIrregular :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- §5: @cite{bybee-1985} Relevance Hierarchy
-- ============================================================================

/-- Morpheme functional category.

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
  deriving Repr, DecidableEq

/-- Peripherality: numerical embedding of Bybee's relevance hierarchy
where **higher = farther from stem = less semantically relevant**.

In Bybee's text, "high relevance" means *more* semantically
integrated with the stem (`@cite{bybee-1985}` Ch 2 §2.1 p. 13). The
substrate uses the *opposite* numerical direction: stem = 0 (most
relevant), agreement = 8 (least relevant), so that Nat ordering
mirrors stem-outward linear position in suffixing morphology
(Ch 2 §6 iconicity, p. 33). The field name `peripherality` makes
this directionality explicit and avoids the wrong-on-its-face
gloss "high relevance rank means low relevance."

**Categories from Bybee 1985 Ch 2 §3** (verified against the book):
valence, voice, aspect, tense, mood, agreement.

**Linglib extensions** (NOT in Bybee 1985 — flag in any consumer
that reads these ranks):
- `derivation` (rank 1): Bybee Ch 4 argues lex/deriv/infl is a
  *continuum*, not a discrete level on the relevance scale.
- `number` (rank 3): Bybee discusses verbal-number agreement at
  the low end (with person agreement). Noun number is treated
  separately (Ch 2 §6 cites Greenberg 1963 only, "stem < number
  < case" for nouns). Cross-comparison of noun-number rank with
  verb-aspect rank is an artifact of unifying both onto one scale.
- `degree` (rank 5): Bybee never discusses adjectival degree
  morphology. Comparative morphology is often *derivational*
  cross-linguistically (Stassen WALS).
- `negation` (rank 7): Bybee discusses negation as a kind of mood
  (Part II Ch 8 §5), not a separate level. Rank 7 is plausible
  per Miestamo 2005 cross-linguistic ordering data, but is a
  linglib extension.
- `nonfinite` (rank 9): not on Bybee's hierarchy at all (nonfinite
  morphology often changes syntactic category, outside the scope
  of inflectional categories proper). -/
def MorphCategory.peripherality : MorphCategory → Nat
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

/-- A morpheme ordering respects the relevance hierarchy if peripherality
is non-decreasing from stem outward (stem-adjacent first). -/
def RespectsRelevanceHierarchy (slots : List MorphCategory) : Prop :=
  (slots.map MorphCategory.peripherality).Pairwise (· ≤ ·)

instance : DecidablePred RespectsRelevanceHierarchy := fun _ => by
  unfold RespectsRelevanceHierarchy; exact inferInstance

-- ============================================================================
-- §6: Morphological Rules with Semantic Effects
-- ============================================================================

/-- A morphological rule: carries formal AND semantic effects.

    The type parameter `σ` is the meaning type, so this works uniformly
    across `Bool`/`Frac`/`Float` semantic backends.

    Design principle: `semEffect` can be `id` for rules whose word-level
    semantic contribution is delegated to a higher composition layer
    (verb agreement `-s` carries no truth-conditional meaning at the word
    level; tense rules delegate to the intensional layer), making it
    explicit which inflections compute meaning at the word level and
    which delegate. -/
structure MorphRule (σ : Type) where
  /-- Which morphological category this rule realizes -/
  category : MorphCategory
  /-- The feature value this rule realizes -/
  value : String
  /-- How the surface form changes -/
  formRule : String → String
  /-- How morphosyntactic features change -/
  featureRule : Features → Features
  /-- Semantic effect (`id` when meaning is delegated to a higher layer) -/
  semEffect : σ → σ
  /-- Is the word-level semantic contribution delegated to a higher
      composition layer? (Set `true` for agreement, tense, etc., where
      `Theories/Semantics/{Tense,Aspect,Modality,Agreement}/` handle
      the meaning. NOT a claim that the morpheme is meaningless —
      see file docstring.) -/
  delegatedSemantics : Bool := false

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

-- ============================================================================
-- §7: Inflectional Distribution in Periphrastic Constructions
-- ============================================================================

/-- Distribution of inflectional categories between two elements of a
    periphrastic construction (e.g., auxiliary and lexical verb in an AVC).
    @cite{anderson-2006} @cite{bybee-1985}

    In an aux-headed AVC, `onLex` is minimal (stem only or empty).
    In a lex-headed AVC, `onAux` is empty.
    In a split AVC, `onAux` and `onLex` host different category types.
    In a doubled AVC, `onAux` and `onLex` overlap. -/
structure InflDistribution where
  onAux : List MorphCategory
  onLex : List MorphCategory
  deriving Repr, DecidableEq

end Core.Morphology
