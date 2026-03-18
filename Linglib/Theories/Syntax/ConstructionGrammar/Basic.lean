import Linglib.Core.Grammar
import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Semantics.CommonGround

/-!
# Construction Grammar: Core Types
@cite{goldberg-1995} @cite{goldberg-2003} @cite{goldberg-2006}

Minimal infrastructure for Construction Grammar (CxG), the framework in which
constructions — learned pairings of form and function — are the basic units
of grammatical knowledge.

-/

namespace ConstructionGrammar

/-- How specified a construction's form side is (@cite{goldberg-2003}:220, Table 8).

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

/-- Mode of information transfer in an inheritance link
(@cite{goldberg-1995} §3.3.1, p. 73–74).

@cite{goldberg-1995} distinguishes two modes, orthogonal to link type:
- **Normal**: child inherits defaults from parent but may override them.
  Allows subregularities and exceptions. The only mode used in
  @cite{goldberg-1995}'s system.
- **Complete**: all information from dominating nodes is inherited strictly;
  no conflicts allowed. Used in unification-based grammars (HPSG, GPSG)
  but not exploited in @cite{goldberg-1995}'s constructional analysis. -/
inductive InheritanceMode where
  | normal     -- child inherits defaults, may override
  | complete   -- all properties inherited strictly (not used in Goldberg 1995)
  deriving Repr, DecidableEq, BEq

/-- Type of semantic relation in an inheritance link
(@cite{goldberg-1995} §3.3.2, p. 75).

@cite{goldberg-1995} distinguishes four major link types:
- **I_P (Polysemy)**: relates the central sense of a construction to its
  extensions. Each extension inherits syntax but differs in meaning
  (e.g., the six senses of the ditransitive, pp. 75–77).
- **I_M (Metaphorical extension)**: source and target related by systematic
  metaphor (e.g., caused-motion → resultative via the motion→change
  metaphor, p. 81).
- **I_S (Subpart)**: one construction is a proper subpart of another
  (e.g., intransitive motion is a subpart of caused-motion, p. 78).
- **I_I (Instance)**: one construction is a more fully specified version
  of another (e.g., *drive*-crazy is an instance of the resultative, p. 79). -/
inductive LinkType where
  | polysemy       -- I_P: central sense → extension
  | metaphorical   -- I_M: source → target via metaphor
  | subpart        -- I_S: child is proper subpart of parent
  | instance       -- I_I: child is special case of parent
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

/-- An inheritance link between two constructions in the network.

Each link specifies both how information flows (`mode`, §3.3.1) and
what semantic relation holds (`linkType`, §3.3.2). Links without a
specific semantic relation (e.g., general taxonomic inheritance of
shared morphophonological properties) use `linkType := none`. -/
structure InheritanceLink where
  parent : String
  child : String
  mode : InheritanceMode
  linkType : Option LinkType := none
  sharedProperties : List String
  overriddenProperties : List String := []
  deriving Repr, BEq

/-- A constructicon: a network of constructions connected by inheritance links. -/
structure Constructicon where
  constructions : List Construction
  links : List InheritanceLink
  deriving Repr

end ConstructionGrammar
