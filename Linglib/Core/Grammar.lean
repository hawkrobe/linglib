import Linglib.Core.Word

/-!
# Grammar

Grammar comparison interface and empirical testing infrastructure.

Defines:
- `ClauseType` — sentence types (declarative, question variants)
- `Grammar` typeclass — assigns derivations to strings
- `MinimalPair` / `PhenomenonData` — word-based grammaticality testing
- `SentencePair` / `StringPhenomenonData` — theory-neutral string-based testing
- Capture predicates and agreement theorems
-/

-- ============================================================================
-- Clause Types
-- ============================================================================

/-- Clause types - determines constraints on word order. -/
inductive ClauseType where
  | declarative
  | matrixQuestion      -- requires inversion in English
  | embeddedQuestion    -- no inversion in English
  | echo                -- no inversion even in matrix position
  deriving Repr, DecidableEq

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
