import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Order.PartialUnify
import Linglib.Syntax.Person.Basic
import Linglib.Syntax.Number.Basic
import Linglib.Syntax.Gender.Basic
import Linglib.Syntax.Case.Basic

/-!
# Feature bundles

This file defines the dimensions in which agreement targets covary and the analytical
feature bundle over them, a value or nothing in each dimension.

A bundle is a dependent function from the dimensions to the flat order on each dimension's
value type, so the pointwise instances give it its partial order, its bottom, the wholly
unspecified bundle, and its unification: two bundles are compatible when they have a common
upper bound, an unspecified dimension acting as a wildcard. Corpus bundles in the Universal
Dependencies vocabulary are ingested by `Agreement.Bundle.ofUD`.

## Main definitions

* `Agreement.Dimension` — the five dimensions a target's form may covary in
* `Agreement.Dimension.Value` — the analytical value type of each dimension
* `Agreement.Bundle` — a value or `⊥` in each dimension
* `Agreement.Bundle.pn`, `Agreement.Bundle.ofUD` — the person–number bundle and the
  ingestion of a Universal Dependencies bundle

## Implementation notes

* Universal Dependencies number tags with no analytical value, the inverse, collective and
  count forms, ingest as `⊥`.

## References

* [corbett-1998] — the three indisputable agreement features and the two contested ones
* [norris-2019] — the dimensions of the concord survey
-/

namespace Agreement

/-- A feature dimension in which a target's form may covary with another element: the three
indisputable agreement features and the two contested ones ([corbett-1998]). -/
inductive Dimension where
  | person | number | gender | case | definiteness
  deriving DecidableEq, Repr, Fintype

/-- The analytical value type of each dimension. -/
abbrev Dimension.Value : Dimension → Type
  | .person => Person
  | .number => Number
  | .gender => Gender
  | .case => Case
  | .definiteness => UD.Definite

instance (d : Dimension) : DecidableEq d.Value := by cases d <;> exact inferInstance

/-- A feature bundle: a value or `⊥` in each dimension. -/
abbrev Bundle := (d : Dimension) → Flat d.Value

/-- The bundle valued in person and number alone. -/
def Bundle.pn (p : Person) (n : Number) : Bundle
  | .person => p
  | .number => n
  | _ => ⊥

/-- The bundle a Universal Dependencies bundle ingests as. -/
def Bundle.ofUD (f : UD.MorphFeatures) : Bundle
  | .person => f.person.map Person.fromUD
  | .number => f.number.bind Number.fromUD
  | .gender => f.gender.map Gender.fromUD
  | .case => f.case_.map Case.fromUD
  | .definiteness => f.definite

instance : Repr Bundle where
  reprPrec b _ := repr (b .person, b .number, b .gender, b .case, b .definiteness)

@[simp] theorem Bundle.pn_person (p : Person) (n : Number) : Bundle.pn p n .person = p := rfl

@[simp] theorem Bundle.pn_number (p : Person) (n : Number) : Bundle.pn p n .number = n := rfl

end Agreement
