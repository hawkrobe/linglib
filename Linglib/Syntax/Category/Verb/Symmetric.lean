import Linglib.Syntax.Category.Verb.Defs
import Linglib.Semantics.Plurality.Groups

/-!
# Symmetric verbs

A symmetric verb denotes mutual atomic events — intransitive *kiss*,
*meet*, *collide*, *quarrel*: the participants are identically involved in
a single event, and linguistic diagnostics (count adverbials,
modification) see no parts. The denotational contract, after
[landman-2000], [dimitriadis-2008], and [siloni-2012]: the verb's events
are atomic, its role assigns the group atom over an unordered pair of
participants, and dissolution recovers two events of the transitive base
with crossed role values — a meaning postulate relating the two entries,
not a decomposition, which is why the underlying events stay invisible.
Formation-locus classification of reciprocal verbs lives in
`Verb.Reciprocal`; the symmetric entries are the lexicon-formed ones
(`Studies/Siloni2012.lean`).
-/

open Semantics.Plurality

/-- A symmetric verb entry: an intransitive verb whose lexical meaning
    codes symmetry; `base` is the transitive alternate when the vocabulary
    has one. -/
structure Verb.Symmetric extends Verb where
  /-- The transitive alternate, when one exists. -/
  base : Option Verb := none
  deriving Repr, BEq

section Denotation

variable {D E : Type*} [SemilatticeSup D] [SemilatticeSup E]

/-- The symmetric-verb denotational contract: `sym` is a set of atomic
    events whose role `agTh` assigns the group atom over an unordered
    pair, and each event dissolves into two events of `base` with crossed
    Agent and Theme values. -/
class Verb.SymmetricDenotation (GD : GroupStructure D) (GE : GroupStructure E)
    (base : Set E) (ag th : E → D) (sym : Set E) (agTh : E → D) : Prop where
  /-- Symmetric verbs denote singular events: no proper parts. -/
  atomic : ∀ e ∈ sym, Mereology.Atom e
  /-- The role assigns the group atom over an unordered pair. -/
  pairRole : ∀ e ∈ sym, ∃ d₁ d₂, d₁ ≠ d₂ ∧ agTh e = GD.up (d₁ ⊔ d₂)
  /-- The meaning postulate: dissolution yields two base events with
      crossed role values. -/
  postulate : ∀ e ∈ sym, ∀ d₁ d₂, d₁ ≠ d₂ → agTh e = GD.up (d₁ ⊔ d₂) →
    ∃ e₁ e₂, GE.down e = e₁ ⊔ e₂ ∧ e₁ ∈ base ∧ e₂ ∈ base ∧
      ag e₁ = d₁ ∧ th e₁ = d₂ ∧ ag e₂ = d₂ ∧ th e₂ = d₁

end Denotation
