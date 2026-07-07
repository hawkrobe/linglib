/-!
# Data.WALS.Aggregation

Shared row struct for WALS distribution tables. Promoted from
`Linglib/Typology/{Complementation, Morphology, Possession}.lean` and
`Linglib/Studies/Haspelmath1997.lean` to eliminate the
4-way duplication of this primitive.

`WALSCount` records a single category label paired with the number of
WALS-sampled languages exhibiting that category. `WALSCount.totalOf` sums
the counts over a list of rows (typically the per-chapter distribution).

Substrate-only: depends on no Data/WALS feature files. Each consumer
imports this module and constructs its `List WALSCount` from
`Data.WALS.F{N}A.allData`.
-/

set_option autoImplicit false

namespace Data.WALS

/-- A single row in a WALS frequency table: a category label and the
    number of WALS-sampled languages with that value. -/
structure WALSCount where
  label : String
  count : Nat
  deriving Repr, DecidableEq

/-- Sum of `count` over a list of `WALSCount` rows. -/
def WALSCount.totalOf (cs : List WALSCount) : Nat :=
  cs.foldl (λ acc c => acc + c.count) 0

end Data.WALS
