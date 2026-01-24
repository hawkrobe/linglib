/-
# LingLean.Core.SemanticTypes

Core semantic types and interfaces.
-/

-- ============================================================================
-- Models
-- ============================================================================

/-- A semantic model provides a domain of entities and truth values -/
structure Model where
  entities : Type
  -- Extensions can add relations, events, worlds, etc.

-- ============================================================================
-- Denotations
-- ============================================================================

/-- Types of semantic values -/
inductive SemType where
  | e       -- entities
  | t       -- truth values
  | fn : SemType → SemType → SemType  -- functions
  deriving Repr, DecidableEq

notation:50 α " → " β => SemType.fn α β
