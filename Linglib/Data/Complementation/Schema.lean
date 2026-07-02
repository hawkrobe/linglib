import Linglib.Features.Complementation

/-!
# Complementation data schema

Typed schema for cross-linguistic complement-taking-predicate (CTP) rows,
the home of the canonical sample behind [noonan-2007]. Generated rows live in
`Data/Complementation/<Paper>.lean`, emitted from the canonical `<Paper>.json`
by `scripts/gen_complementation.py`.

This is substrate: it imports `Features/Complementation.lean` only. Consumers
(the paper's study file, bridge studies) import the generated module.

## Main definitions
* `Datum` — one CTP row: verb, CTP class, attested complement types,
  equi-deletion, negative raising.
-/

namespace Data.Complementation

/-- One row of [noonan-2007]'s CTP sample: a complement-taking predicate in
    one language, with its CTP class, the complement types it is attested
    with, and its equi-deletion / negative-raising behavior.

    `verb` is citation provenance, not identity — rows are identified by
    their generated def names and grouped into per-language lists.

    Dropped relative to the older `CTPDatum`: `language` (identity is the
    per-language grouping list), `realityStatus` (derivable as
    `ctpRealityStatus ctpClass`; the sample has zero overrides, as the old
    file's own `reality_status_consistent` theorem proved), and `hasRaising`
    (zero consumers). -/
structure Datum where
  verb : String
  ctpClass : CTPClass
  compTypes : List NoonanCompType
  hasEquiDeletion : Bool := false
  hasNegativeRaising : Bool := false
  deriving DecidableEq, Repr

end Data.Complementation
