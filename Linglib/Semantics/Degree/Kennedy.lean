import Linglib.Semantics.Degree.Defs

/-!
# Kennedy 2007: Interpretive Economy

Kennedy's classification of gradable adjectives by scale structure, and
the derivation of comparison-class sensitivity from scale boundedness
@cite{kennedy-2007} @cite{kennedy-mcnally-2005}. The key principle
(Interpretive Economy) says: when a scale has an endpoint, use it as the
standard — more informative than a contextual norm.

## Main definitions

* `interpretiveEconomy : Boundedness → PositiveStandard` — derivation of
  standard type from scale structure
* `IsClassA` — relative (Class A) adjectives, defined as those whose
  interpretive-economy standard requires a comparison class

## Main theorems

* `interpretiveEconomy_open`, `interpretiveEconomy_closed`,
  `interpretiveEconomy_lowerBounded`, `interpretiveEconomy_upperBounded`
  — the four entries of the IE table
-/

namespace Semantics.Degree

open Core.Scale (Boundedness)

/-- Interpretive Economy determines the standard from scale structure.
When a scale has an endpoint, Interpretive Economy requires using it as
the standard (more informative than a contextual norm). -/
def interpretiveEconomy : Boundedness → PositiveStandard
  | .open_        => .contextual
  | .lowerBounded => .minEndpoint
  | .upperBounded => .maxEndpoint
  | .closed       => .maxEndpoint

theorem interpretiveEconomy_open : interpretiveEconomy .open_ = .contextual := rfl
theorem interpretiveEconomy_closed : interpretiveEconomy .closed = .maxEndpoint := rfl
theorem interpretiveEconomy_lowerBounded :
    interpretiveEconomy .lowerBounded = .minEndpoint := rfl
theorem interpretiveEconomy_upperBounded :
    interpretiveEconomy .upperBounded = .maxEndpoint := rfl

/-- A boundedness is *Class A* (relative) iff its interpretive-economy
standard requires a comparison class — i.e. iff the scale is open.
Kennedy's *tall*, *expensive*, *big*. -/
def IsClassA (b : Boundedness) : Prop :=
  (interpretiveEconomy b).RequiresComparisonClass

instance : DecidablePred IsClassA :=
  fun b => inferInstanceAs (Decidable (interpretiveEconomy b).RequiresComparisonClass)

end Semantics.Degree
