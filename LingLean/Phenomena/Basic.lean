/-
# LingLean.Phenomena.Basic

Core types for specifying linguistic phenomena.
-/

import LingLean.Syntax.Basic
import LingLean.Syntax.Grammar

-- ============================================================================
-- Minimal Pairs
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

-- ============================================================================
-- Phenomenon Coverage
-- ============================================================================

/-- A grammar captures a minimal pair if it derives the good one and blocks the bad one -/
def Grammar.capturesPair (G : Type) [Grammar G] (g : G) (pair : MinimalPair) : Prop :=
  Grammar.derives g pair.grammatical pair.clauseType ∧
  ¬ Grammar.derives g pair.ungrammatical pair.clauseType

/-- A grammar captures a phenomenon if it captures all its minimal pairs -/
def Grammar.capturesPhenomenon (G : Type) [Grammar G] (g : G) (phenom : PhenomenonData) : Prop :=
  ∀ pair ∈ phenom.pairs, Grammar.capturesPair G g pair

-- ============================================================================
-- Framework-Neutral Theorems
-- ============================================================================

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
