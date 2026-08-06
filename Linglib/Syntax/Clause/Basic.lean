import Linglib.Syntax.Clause.Construction
import Linglib.Syntax.Clause.Form
import Linglib.Features.Complementation
import Linglib.Features.Case.Basic

/-!
# The clause object

A clause is a predication: at minimum a predicate and an explicit or
implied subject, expressing a proposition. `Clause` records the axes
sources record about one — the construction it instantiates
(`Clause.Construction`), its surface form (`Clause.Form`), its
[noonan-2007] coding (`Complement.Coding`), and its subject requirement
(`Clause.EmbeddedSubject`). A `none` field is unrecorded, not a claim —
the record-what-sources-record convention of the Fragment layer, where
these values originate. The first consumer is the clausal case of
`Complement.Position` (`Syntax/Category/Verb/Frame.lean`), so a
complement frame's clausal position carries a `Clause` by construction.

## Main definitions

* `Clause.EmbeddedSubject` — the subject-requirement axis
* `Clause` — the predication record
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

end Clause

/-- A clause description: the recorded axes of one predication.
    `none` = unrecorded. -/
structure Clause where
  /-- The construction the clause instantiates. -/
  construction : Option Clause.Construction := none
  /-- Surface clause form (declarative vs embedded question). -/
  clauseForm : Option Clause.Form := none
  /-- [noonan-2007] coding. -/
  coding : Option Complement.Coding := none
  /-- Subject requirement. -/
  embeddedSubject : Option Clause.EmbeddedSubject := none
  deriving DecidableEq, Repr
