module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.PartialUnify
public import Linglib.Morphology.Word.Features

/-!
# Feature bundles

This file defines the dimensions in which agreement targets covary and the analytical
feature bundle over them, a value or nothing in each dimension.

A bundle is a dependent function from the dimensions to the flat order on each dimension's
value type, so the pointwise instances give it its partial order, its bottom, the wholly
unspecified bundle, and its unification: two bundles are compatible when they have a common
upper bound, an unspecified dimension acting as a wildcard. A token's bundle is the
restriction of its features to the agreement dimensions, `Agreement.Bundle.ofFeatures`.

## Main definitions

* `Agreement.Dimension` — the five dimensions a target's form may covary in
* `Agreement.Dimension.Value` — the analytical value type of each dimension
* `Agreement.Bundle` — a value or `⊥` in each dimension
* `Agreement.Bundle.pn`, `Agreement.Bundle.ofFeatures` — the person–number bundle and the
  restriction of a token's features

## References

* [corbett-1998] — the three indisputable agreement features and the two contested ones
* [norris-2019] — the dimensions of the concord survey
-/

@[expose] public section

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

/-- The token feature a dimension is. -/
def Dimension.toFeature : Dimension → Morphology.Feature
  | .person => .person
  | .number => .number
  | .gender => .gender
  | .case => .case
  | .definiteness => .definiteness

/-- The restriction of a token's features to the agreement dimensions. -/
def Bundle.ofFeatures (f : Morphology.Features) : Bundle
  | .person => f .person
  | .number => f .number
  | .gender => f .gender
  | .case => f .case
  | .definiteness => f .definiteness

instance : Repr Bundle where
  reprPrec b _ := repr (b .person, b .number, b .gender, b .case, b .definiteness)

@[simp] theorem Bundle.pn_person (p : Person) (n : Number) : Bundle.pn p n .person = p := rfl

@[simp] theorem Bundle.pn_number (p : Person) (n : Number) : Bundle.pn p n .number = n := rfl

end Agreement
