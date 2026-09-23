module

public import Linglib.Syntax.Clause.Complementation

/-!
# Complementation data schema

Typed schema for cross-linguistic complement-taking-predicate (CTP) rows,
the home of the canonical sample behind [noonan-2007]. Generated rows live in
`Data/Complementation/<Paper>.lean`, emitted from the canonical `<Paper>.json`
by `scripts/gen_complementation.py`.

This is substrate: it imports `Features/Complementation.lean` only. Consumers
(the paper's study file, bridge studies) import the generated module.

## Main definitions
* `Datum` — one CTP row: verb, CTP class, attested complement codings,
  equi-deletion, negative raising.
-/

@[expose] public section

namespace Data.Complementation

/-- One row of [noonan-2007]'s sample: a complement-taking predicate in one language, with
    its predicate class, the complement codings it is attested with, and its equi-deletion and
    negative-raising behavior. `verb` is citation provenance, not identity; rows are identified
    by their generated names and grouped into per-language lists, and a row's reality status is
    `Complement.PredicateClass.realityStatus` of its class. -/
structure Datum where
  verb : String
  predicateClass : Complement.PredicateClass
  codings : List Complement.Coding
  hasEquiDeletion : Bool := false
  hasNegativeRaising : Bool := false
  deriving DecidableEq, Repr

end Data.Complementation
