module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.PartialUnify
public import Linglib.Morphology.Word.Features

/-!
# Feature bundles

This file defines the dimensions in which agreement targets covary and the analytical
feature bundle over them, a value or nothing in each dimension.

An agreement bundle is the generic feature bundle of `Core/Order/Bundle.lean` over the
dimensions, so its partial order, its bottom, the wholly unspecified bundle, and its
unification are the pointwise ones, and `single`, `set` and `comap` build and read it. Each
dimension is a token feature with that feature's values, and a token's bundle is its features
read along that inclusion, `Agreement.Bundle.ofFeatures`.

## Main definitions

* `Agreement.Dimension` — the five dimensions a target's form may covary in
* `Agreement.Dimension.toFeature`, `Agreement.Dimension.Value` — the token feature a dimension
  is, and its values
* `Agreement.Bundle` — a value or `⊥` in each dimension
* `Agreement.Bundle.personNumber` — the bundle valued in person and number alone
* `Agreement.Bundle.ofFeatures` — the restriction of a token's features

## Implementation notes

Inside `namespace Agreement`, `Bundle` names the agreement bundle; the generic operations are
reached by dot notation or as `_root_.Bundle.single` and its siblings.

## References

* [corbett-1998] — the three indisputable agreement features and the two contested ones
* [norris-2019] — the dimensions of the concord survey
-/

@[expose] public section

namespace Agreement

/-- A dimension is a feature in which a target's form may covary with another element, one of the
three indisputable agreement features or the two contested ones ([corbett-1998]). -/
inductive Dimension where
  | person | number | gender | case | definiteness
  deriving DecidableEq, Repr, Fintype

/-- The token feature a dimension is. It is reducible, so that the values of a dimension reduce
to those of its feature when coercions are sought. -/
abbrev Dimension.toFeature : Dimension → Morphology.Feature
  | .person => .person
  | .number => .number
  | .gender => .gender
  | .case => .case
  | .definiteness => .definiteness

/-- The values of a dimension are those of the token feature it is. -/
abbrev Dimension.Value (d : Dimension) : Type := d.toFeature.Value

instance (d : Dimension) : DecidableEq d.Value := by cases d <;> exact inferInstance

/-- A feature bundle assigns each dimension a value or `⊥`. -/
abbrev Bundle := _root_.Bundle Dimension Dimension.Value

namespace Bundle

/-- The bundle valued in person and number alone. -/
def personNumber (p : Person) (n : Number) : Bundle :=
  _root_.Bundle.set .number n (_root_.Bundle.single .person p)

@[simp] theorem personNumber_person (p : Person) (n : Number) : personNumber p n .person = p :=
  rfl

@[simp] theorem personNumber_number (p : Person) (n : Number) : personNumber p n .number = n :=
  rfl

@[simp] theorem personNumber_gender (p : Person) (n : Number) : personNumber p n .gender = ⊥ :=
  rfl

@[simp] theorem personNumber_case (p : Person) (n : Number) : personNumber p n .case = ⊥ := rfl

@[simp] theorem personNumber_definiteness (p : Person) (n : Number) :
    personNumber p n .definiteness = ⊥ :=
  rfl

/-- The restriction of a token's features to the agreement dimensions reads them along
`Dimension.toFeature`. -/
def ofFeatures (f : Morphology.Features) : Bundle := _root_.Bundle.comap Dimension.toFeature f

@[simp] theorem ofFeatures_apply (f : Morphology.Features) (d : Dimension) :
    ofFeatures f d = f d.toFeature :=
  rfl

end Bundle

instance : Repr Bundle where
  reprPrec b _ := repr (b .person, b .number, b .gender, b .case, b .definiteness)

end Agreement
