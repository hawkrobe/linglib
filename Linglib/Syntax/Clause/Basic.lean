import Linglib.Syntax.Clause.Size
import Linglib.Syntax.Clause.Form
import Linglib.Features.Complementation
import Linglib.Features.Case.Basic

/-!
# The clause interface

A clause is a predication — at minimum a predicate and an explicit or
implied subject, expressing a proposition. What a clause *is*
concretely is framework-relative (a Minimalist extended projection, an
HPSG sign, a dependency subtree), so `Clause` is the interface those
carriers instantiate: a clause object answers the theory-neutral
queries — its grade on the `Clause.Size` scale and the selectional
axes ([noonan-2007] coding, `Clause.Form`) — and consumers reason
through the queries rather than importing a framework.
`Minimalist.ClauseSpine` is the first instance
(`Syntax/Minimalist/ExtendedProjection/ClauseSpine.lean`).

## Main definitions

* `Clause` — the interface: `size`, `coding?`, `form?`
* `Clause.EmbeddedSubject` — the subject-requirement axis complement
  frames record (`Syntax/Category/Verb/Frame.lean`)
-/

/-- Carriers of clause structure. A framework's clause object answers
    the theory-neutral queries: its `Clause.Size` grade and the
    selectional axes it determines (`none` = the object does not
    determine the axis). -/
class Clause (C : Type*) where
  /-- The clause's grade on the theory-neutral size scale. -/
  size : C → Clause.Size
  /-- The [noonan-2007] coding the object realizes, when its structure
      determines one. -/
  coding? : C → Option Complement.Coding := λ _ => none
  /-- The surface clause form, when the object determines one. -/
  form? : C → Option Clause.Form := λ _ => none

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

end Clause
