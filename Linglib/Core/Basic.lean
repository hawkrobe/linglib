import Linglib.Core.UD

/-!
# Basic

Core types shared across all theoretical frameworks.

## Universal Dependencies Integration

Morphological features are aliased to UD types:
- `Number` = `UD.Number` (with compatibility constructors `sg`, `pl`)
- `Person` = `UD.Person` (with compatibility constructors `first`, `second`, `third`)
- `Case` = `UD.Case` (with compatibility constructors `nom`, `acc`, `gen`)
- `Voice` = `UD.Voice` (with compatibility constructors `active`, `passive`)
- `VForm` = `UD.VerbForm` (with compatibility constructors)

Syntactic categories use `UD.UPOS` directly (the 17 universal POS tags).

Types without UD equivalents remain defined here:
- `Valence` (argument structure)
- `ClauseType` (sentence type)
-/

-- ============================================================================
-- Aliased Types (backed by UD)
-- ============================================================================

/-- Grammatical number. Aliased to UD.Number for cross-linguistic compatibility. -/
abbrev Number := UD.Number

namespace Number
/-- Singular (compatibility alias for UD.Number.Sing) -/
abbrev sg : Number := .Sing
/-- Plural (compatibility alias for UD.Number.Plur) -/
abbrev pl : Number := .Plur
end Number

/-- Grammatical person. Aliased to UD.Person for cross-linguistic compatibility.

    Constructors are: `.first`, `.second`, `.third`, `.zero`
    (no compatibility aliases needed - names match) -/
abbrev Person := UD.Person

/-- Grammatical case. Aliased to UD.Case for cross-linguistic compatibility. -/
abbrev Case := UD.Case

namespace Case
/-- Nominative (compatibility alias) -/
abbrev nom : Case := .Nom
/-- Accusative (compatibility alias) -/
abbrev acc : Case := .Acc
/-- Genitive (compatibility alias) -/
abbrev gen : Case := .Gen
end Case

/-- Voice: active vs passive. Aliased to UD.Voice. -/
abbrev Voice := UD.Voice

namespace Voice
/-- Active voice (compatibility alias) -/
abbrev active : Voice := .Act
/-- Passive voice (compatibility alias) -/
abbrev passive : Voice := .Pass
end Voice

/-- Verb form. Aliased to UD.VerbForm. -/
abbrev VForm := UD.VerbForm

namespace VForm
/-- Finite (compatibility alias) -/
abbrev finite : VForm := .Fin
/-- Infinitive (compatibility alias) -/
abbrev infinitive : VForm := .Inf
/-- Past participle (compatibility alias - maps to Part) -/
abbrev pastParticiple : VForm := .Part
/-- Present participle (compatibility alias - maps to Part) -/
abbrev presParticiple : VForm := .Part
end VForm

-- ============================================================================
-- Thematic Roles (Language-Independent)
-- ============================================================================

/-- Theta roles for argument structure (Dowty 1991, Parsons 1990).
    Language-independent semantic categories classifying the relationship
    between a verb's arguments and the event it describes. Used by both
    Theory-layer modules (Semantics.Events.ThematicRoles) and Fragment-layer
    modules (English/Korean/Japanese/... Predicates). -/
inductive ThetaRole where
  | agent       -- Volitional causer (John kicked the ball)
  | patient     -- Affected entity (John kicked the ball)
  | theme       -- Entity in a state/location (The book is on the table)
  | experiencer -- Perceiver/cognizer (John knows that p)
  | goal        -- Recipient/target (John gave Mary a book)
  | source      -- Origin (John came from Paris)
  | instrument  -- Means (John opened the door with a key)
  | stimulus    -- Cause of experience (The noise frightened John)
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- Types Without UD Equivalents
-- ============================================================================

/-- Transitivity / argument structure. No direct UD equivalent. -/
inductive Valence where
  | intransitive  -- sleep, arrive
  | transitive    -- see, eat
  | ditransitive  -- give, send (double object)
  | dative        -- give X to Y (prepositional dative)
  | locative      -- put X on Y
  | copular       -- be (takes predicate)
  deriving Repr, DecidableEq, Inhabited

/-- Head direction of a syntactic construction.
    Used for word-order typology (Dryer 1992, Greenberg 1963) and
    constraints like FOFC (Biberauer, Holmberg & Roberts 2014). -/
inductive HeadDirection where
  | headInitial  -- head precedes complement (VO, preposition, head-initial FocP, ...)
  | headFinal    -- head follows complement (OV, postposition, head-final FocP, ...)
  deriving Repr, DecidableEq, BEq

/-- Clause types - determines constraints on word order. -/
inductive ClauseType where
  | declarative
  | matrixQuestion      -- requires inversion in English
  | embeddedQuestion    -- no inversion in English
  | echo                -- no inversion even in matrix position
  deriving Repr, DecidableEq

-- ============================================================================
-- Feature Bundle and Word
-- ============================================================================

/-- Feature bundle for words. Uses aliased UD types. -/
structure Features where
  wh : Bool := false
  finite : Bool := true
  number : Option Number := none
  person : Option Person := none
  case_ : Option Case := none
  valence : Option Valence := none
  voice : Option Voice := none
  vform : Option VForm := none
  countable : Option Bool := none  -- for count vs mass nouns
  deriving Repr, DecidableEq

/-- A word: form + category + features. -/
structure Word where
  form : String
  cat : UD.UPOS
  features : Features := {}
  deriving Repr

/-- Convenience constructor for a featureless word (form + category only). -/
def Word.mk' (form : String) (cat : UD.UPOS) : Word := ⟨form, cat, {}⟩

instance : BEq Word where
  beq w1 w2 := w1.form == w2.form && w1.cat == w2.cat

instance : ToString Word where
  toString w := w.form

/-- Convert a word list to a readable string. -/
def wordsToString (ws : List Word) : String :=
  " ".intercalate (ws.map (·.form))

-- ============================================================================
-- Grammar Typeclasses
-- ============================================================================

/-- A Grammar assigns derivations to strings. Derivations are proof objects. -/
class Grammar (G : Type) where
  /-- The type of derivations/analyses this grammar produces -/
  Derivation : Type
  /-- Whether a derivation yields a given string with given clause type -/
  realizes : Derivation → List Word → ClauseType → Prop
  /-- Whether the grammar can produce *some* derivation for a string -/
  derives : G → List Word → ClauseType → Prop

/-- If two grammars both derive the same string, they agree on that string. -/
theorem derives_agreement
    {G₁ G₂ : Type} [Grammar G₁] [Grammar G₂]
    (g₁ : G₁) (g₂ : G₂) (ws : List Word) (ct : ClauseType)
    (h₁ : Grammar.derives g₁ ws ct)
    (h₂ : Grammar.derives g₂ ws ct) :
    Grammar.derives g₁ ws ct ∧ Grammar.derives g₂ ws ct :=
  ⟨h₁, h₂⟩

-- ============================================================================
-- Minimal Pairs (Word-Based)
-- ============================================================================

/-- A minimal pair: grammatical vs ungrammatical, with context -/
structure MinimalPair where
  grammatical : List Word
  ungrammatical : List Word
  clauseType : ClauseType
  description : String
  citation : Option String := none

/-- Collection of minimal pairs for a phenomenon -/
structure PhenomenonData where
  name : String
  pairs : List MinimalPair
  generalization : String

/-- Check if a grammaticality predicate captures a minimal pair.

    Captures the pair iff the predicate accepts the grammatical sentence
    and rejects the ungrammatical sentence. -/
def capturesMinimalPairBy (pred : List Word → Bool) (pair : MinimalPair) : Bool :=
  pred pair.grammatical && !pred pair.ungrammatical

/-- Check if a grammaticality predicate captures all minimal pairs in a phenomenon dataset. -/
def capturesPhenomenonData (pred : List Word → Bool) (phenom : PhenomenonData) : Bool :=
  phenom.pairs.all (capturesMinimalPairBy pred)

/-- A grammar captures a minimal pair if it derives the good one and blocks the bad one -/
def Grammar.capturesPair (G : Type) [Grammar G] (g : G) (pair : MinimalPair) : Prop :=
  Grammar.derives g pair.grammatical pair.clauseType ∧
  ¬ Grammar.derives g pair.ungrammatical pair.clauseType

/-- A grammar captures a phenomenon if it captures all its minimal pairs -/
def Grammar.capturesPhenomenon (G : Type) [Grammar G] (g : G) (phenom : PhenomenonData) : Prop :=
  ∀ pair ∈ phenom.pairs, Grammar.capturesPair G g pair

/-- If two grammars both capture a phenomenon, they agree on grammatical sentences -/
theorem grammars_agree_on_phenomenon
    (G₁ G₂ : Type) [Grammar G₁] [Grammar G₂]
    (g₁ : G₁) (g₂ : G₂) (phenom : PhenomenonData)
    (h₁ : Grammar.capturesPhenomenon G₁ g₁ phenom)
    (h₂ : Grammar.capturesPhenomenon G₂ g₂ phenom)
    (pair : MinimalPair) (hp : pair ∈ phenom.pairs) :
    (Grammar.derives g₁ pair.grammatical pair.clauseType ↔
     Grammar.derives g₂ pair.grammatical pair.clauseType) := by
  constructor
  · intro _; exact (h₂ pair hp).1
  · intro _; exact (h₁ pair hp).1

-- ============================================================================
-- String-Based Phenomena (Theory-Neutral)
-- ============================================================================

/-- String-based minimal pair for theory-neutral phenomena.

Unlike `MinimalPair` which uses `List Word` (requiring feature specifications),
this type uses raw strings that can be parsed by any theory. This keeps
empirical data in `Phenomena/` free from theoretical commitments. -/
structure SentencePair where
  /-- The grammatical sentence -/
  grammatical : String
  /-- The ungrammatical sentence -/
  ungrammatical : String
  /-- Clause type (declarative, question, etc.) -/
  clauseType : ClauseType
  /-- Description of what the pair tests -/
  description : String
  /-- Optional citation for the data -/
  citation : Option String := none
  deriving Repr, BEq

/-- String-based phenomenon data for theory-neutral representation.

This is the string-based analogue of `PhenomenonData`. Phenomena files
should use this type so that empirical data is decoupled from any
particular grammatical theory's representation. -/
structure StringPhenomenonData where
  /-- Name of the phenomenon -/
  name : String
  /-- List of minimal pairs -/
  pairs : List SentencePair
  /-- Generalization captured by this data -/
  generalization : String
  deriving Repr

/-- A grammar with parsing can verify string-based phenomena -/
class GrammarWithParsing (G : Type) extends Grammar G where
  /-- Parse a string into a list of words (tokenization + lexical lookup) -/
  parse : G → String → Option (List Word)

/-- A grammar captures a string-based pair if it derives the grammatical
    and blocks the ungrammatical (after parsing) -/
def GrammarWithParsing.capturesStringPair
    (G : Type) [GrammarWithParsing G] (g : G) (pair : SentencePair) : Prop :=
  match GrammarWithParsing.parse g pair.grammatical,
        GrammarWithParsing.parse g pair.ungrammatical with
  | some ws_good, some ws_bad =>
      Grammar.derives g ws_good pair.clauseType ∧
      ¬ Grammar.derives g ws_bad pair.clauseType
  | _, _ => False  -- Parse failure means we can't verify

/-- A grammar captures a string-based phenomenon if it captures all pairs -/
def GrammarWithParsing.capturesStringPhenomenon
    (G : Type) [GrammarWithParsing G] (g : G) (phenom : StringPhenomenonData) : Prop :=
  ∀ pair ∈ phenom.pairs, GrammarWithParsing.capturesStringPair G g pair
