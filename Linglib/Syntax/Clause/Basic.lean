import Linglib.Semantics.Mood.Defs
import Linglib.Features.Complementation
import Linglib.Features.Case.Basic

/-!
# The clause interface

A clause is a predication — at minimum a predicate and an explicit or
implied subject, expressing a proposition. What a clause *is*
concretely is framework-relative (a Minimalist extended projection, an
HPSG sign, a dependency subtree), so `Clause` is the interface those
carriers instantiate: a clause object answers the theory-neutral
queries — its grade on the clause-size scale and the selectional
axes ([noonan-2007] coding, `Mood.Illocutionary` force) — and
consumers reason through the queries rather than importing a
framework. `Minimalist.ClauseSpine` is the first instance
(`Syntax/Minimalist/ExtendedProjection/ClauseSpine.lean`).

## Main definitions

* `Clause` — the interface: `size`, `coding?`, `force?`
* `Clause.Finiteness`, `Clause.Independence` — the fundamental clause
  predicates `Finite` and `Independent`, provided per carrier. No law
  connects them here: [van-gelderen-2013]'s claim that independent
  clauses are finite is paper content, and verbless independent
  clauses (`Clause.Construction`) contest it.
* `Clause.EmbeddedSubject` — the subject-requirement axis complement
  frames record (`Syntax/Category/Verb/Frame.lean`)
-/

/-- Carriers of clause structure. A framework's clause object answers
    the theory-neutral queries: its size grade and the selectional
    axes it determines (`none` = the object does not determine the
    axis). -/
class Clause (C : Type*) where
  /-- The clause's grade on the theory-neutral size scale — a rank in
      the functional hierarchy every framework can assign (Minimalist:
      `ClauseSpine.fLevel`). Transparency to a dependency bounded at
      `b` is `size c < b`; selective opacity is then monotone for free
      (the Williams Cycle in the abstract). -/
  size : C → ℕ
  /-- The [noonan-2007] coding the object realizes, when its structure
      determines one. -/
  coding? : C → Option Complement.Coding := λ _ => none
  /-- The illocutionary force, when the object determines one. -/
  force? : C → Option Mood.Illocutionary := λ _ => none

namespace Clause

/-- Carriers whose clause objects determine finiteness. -/
class Finiteness (C : Type*) where
  /-- The clause is finite: tense, agreement, and case anchor the
      event to a time and its participants ([van-gelderen-2013]'s
      anchoring characterization, stated functionally — the
      morphological checklist is language-specific). -/
  Finite : C → Prop

/-- Carriers whose clause objects determine root status. -/
class Independence (C : Type*) where
  /-- The clause can stand alone as a complete utterance — a root
      clause, bearing its own illocutionary force. -/
  Independent : C → Prop

export Finiteness (Finite)
export Independence (Independent)

/-- Subject requirement of a clause: obligatorily null (as in control
    complements) or overt, optionally with a fixed case. Genitive
    marking on the subject is [noonan-2007]'s criterion for the
    nominalization coding (§1.3.5); [bondarenko-2022] ch. 4 is the
    modern instance (Buryat genitive subjects of nominalized
    clauses). -/
inductive EmbeddedSubject where
  | obligatorilyNull
  | overt (subjCase : Option Case)
  deriving DecidableEq, Repr

end Clause
