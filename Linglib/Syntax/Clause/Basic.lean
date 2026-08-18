import Linglib.Features.Case.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Clause-token axes

Theory-neutral axes of an embedded clause token, consumed by the
complementation and particle APIs.

## Main definitions

* `Clause.EmbeddedSubject` — the subject-requirement axis complement
  frames record (`Syntax/Category/Verb/Complement/Basic.lean`)
* `Clause.EmbeddingContext` — where a clause token occurs, the
  [bhatt-dayal-2020] embedding cells
-/

namespace Clause

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

/-- A [bhatt-dayal-2020] / [dayal-2025] interrogative-embedding
    context: where the clause token occurs, not a property of the
    clause object. A particle's left-periphery layer
    (`Features.QParticleLayer`) is derivable from its distribution
    over these cells (`Studies/Dayal2025`). -/
inductive EmbeddingContext where
  | matrix
  | subordinated
  /-- Embedded root-like interrogatives (Hindi-Urdu *kya:*). -/
  | quasiSubordinated
  | quotation
  deriving DecidableEq, Repr, Fintype

end Clause
