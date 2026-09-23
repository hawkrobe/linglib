module

public import Linglib.Syntax.Category.Adjective.Basic
public import Linglib.Syntax.Category.Verb.Basic

/-!
# Clause-embedding adjectives

Adjectives that take propositional complements — *annoyed (that p)*,
*sorry (that p)*, *aware (that p)*, *certain (that p)*. On the pattern
of `GradableAdjective` in `Semantics/Gradability`,
`ClauseEmbeddingAdjective` extends the `Adjective` core with the
clausal-selection spine it shares with clause-embedding verbs:
complement type, presupposition trigger class, attitude, opacity, and
entailment signature.

Whether predication requires a copula is a language-level property
([stassen-2013]), not a property of the adjective: English realizes
these predicates as *be* + adjective (`ClauseEmbeddingAdjective.toVerb`
in `Fragments/English/Verbs/Copular.lean`), Mandarin and Japanese
without a copula.
-/

@[expose] public section

open NaturalLogic (Signature)

/-- A clause-embedding adjective: the `Adjective` core plus the
    clausal-selection spine shared with clause-embedding verbs, but no
    verbal morphology. -/
structure ClauseEmbeddingAdjective extends Adjective where
  /-- The frame of the clause the adjective embeds. -/
  frame : ArgumentFrame := .finiteClause
  /-- The [karttunen-1971b] factivity class, if the adjective is factive. -/
  factivity : Option Presupposition.Factivity := none
  /-- Attitude semantics, if applicable. -/
  attitude : Option Attitude := none
  /-- Does the adjective create an opaque context? -/
  opaqueContext : Bool := false
  /-- Entailment signature of the complement position. -/
  complementSig : Option Signature := none
  deriving Repr, BEq
