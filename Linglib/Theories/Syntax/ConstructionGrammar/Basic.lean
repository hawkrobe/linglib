import Linglib.Core.Grammar
import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Semantics.CommonGround

/-!
# Construction Grammar: Core Types
@cite{diessel-2023} @cite{goldberg-1995} @cite{goldberg-2003} @cite{goldberg-2006}

Minimal infrastructure for Construction Grammar (CxG), the framework in which
constructions — learned pairings of form and function — are the basic units
of grammatical knowledge.

-/

namespace ConstructionGrammar

/-- How specified a construction's form side is (Goldberg 2003:220, Table 8).

| Specificity | Example |
|---|---|
| lexicallySpecified | "veggie-wrap", "must-read" |
| partiallyOpen | "N-wrap", "a simple ⟨PAL⟩" |
| fullyAbstract | [N⁰ N⁰ N⁰], [N' PAL⁰ N] |
-/
inductive Specificity where
  | lexicallySpecified
  | partiallyOpen
  | fullyAbstract
  deriving Repr, DecidableEq, BEq

/-- Inheritance mode between constructions.

Normal inheritance allows overriding of inherited defaults;
complete inheritance requires strict preservation of all properties. -/
inductive InheritanceMode where
  | normal    -- defaults, child can override (most CxG links)
  | complete  -- all properties inherited strictly
  deriving Repr, DecidableEq, BEq

/-- A construction: a learned pairing of form and function.

Constructions range from fully lexically specified (idioms, words)
to fully abstract (argument-structure constructions). -/
structure Construction where
  name : String
  form : String              -- syntactic schema description
  meaning : String           -- semantic/pragmatic function description
  specificity : Specificity
  pragmaticFunction : Option String := none  -- e.g. "presupposes familiarity"
  deriving Repr, BEq

/-- An inheritance link between two constructions in the network. -/
structure InheritanceLink where
  parent : String
  child : String
  mode : InheritanceMode
  sharedProperties : List String
  overriddenProperties : List String := []
  deriving Repr, BEq

/-- A constructicon: a network of constructions connected by inheritance links. -/
structure Constructicon where
  constructions : List Construction
  links : List InheritanceLink
  deriving Repr

end ConstructionGrammar
