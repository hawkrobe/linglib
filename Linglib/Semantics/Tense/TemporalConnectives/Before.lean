import Mathlib.Order.Bounds.Basic

/-!
# `before`-clauses
[beaver-condoravdi-2003]

[beaver-condoravdi-2003]'s semantics for `before`: `before^{B&C}` takes a
body `p` (a partial time-predicate) and an evaluation interval `t`, and is
defined only if `t` is contained in the contextual restrictor `C`,
`EARLIEST_C({t' ∈ C | p t'})` is defined (`hasEarliest`), and a strict
predecessor in `C` exists; when defined it is true iff
`t < EARLIEST_C(...)`. The Inherent Presupposition Failure results that
[sharvit-2014] builds on this semantics live in `Studies.Sharvit2014`.
-/

namespace Tense.TemporalConnectives.Before

variable {Time : Type*} [LinearOrder Time]

/-- The `EARLIEST` definedness presupposition of `before^{B&C}`:
    `EARLIEST_C` is defined for body `p` iff the set of `C`-times where `p`
    holds has a least element (mathlib's `IsLeast`). -/
def hasEarliest (C : Set Time) (p : Time → Prop) : Prop :=
  ∃ t, IsLeast {t' | t' ∈ C ∧ p t'} t

end Tense.TemporalConnectives.Before
