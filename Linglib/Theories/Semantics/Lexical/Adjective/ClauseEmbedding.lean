import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# Clause-Embedding Adjectives

Cross-linguistic type for adjectives that take propositional complements:
"annoyed (that p)", "sorry (that p)", "aware (that p)", "certain (that p)".

These are distinct from gradable adjectives (@cite{kennedy-2007}), which
denote scalar properties of individuals. Clause-embedding adjectives
denote attitudes or evaluations toward propositions.

Whether predication requires a copula is a **language-level** property
(tracked in `Phenomena/Copulas/Typology.lean`), not a property of the
adjective. English requires "be", Mandarin and Japanese do not. The
copula and its syntax belong in the Theory/Syntax layer, not here.
-/

namespace Semantics.Lexical.Adjective

open Core.Verbs (ComplementType PresupTriggerType AttitudeBuilder)
open Core.NaturalLogic (EntailmentSig)

/-- A clause-embedding adjective: an adjective that takes a propositional
    complement. Carries the semantic spine shared with clause-embedding verbs
    (complement type, presupposition, attitude builder) but no verbal
    morphology or verb-specific features. -/
structure ClauseEmbeddingAdj where
  /-- Citation form of the adjective ("annoyed", "right", "happy") -/
  adjForm : String
  /-- What kind of clause does the adjective embed? -/
  complementType : ComplementType := .finiteClause
  /-- Is the adjective a presupposition trigger? -/
  presupType : Option PresupTriggerType := none
  /-- Attitude semantics (if applicable) -/
  attitudeBuilder : Option AttitudeBuilder := none
  /-- Does the adjective create an opaque context? -/
  opaqueContext : Bool := false
  /-- Entailment signature of the complement position -/
  complementSig : Option EntailmentSig := none
  deriving Repr, BEq

end Semantics.Lexical.Adjective
