module

public import Linglib.Semantics.Reference.Animacy
public import Linglib.Semantics.Reference.Definiteness
public import Mathlib.Order.Nat
public import Mathlib.Tactic.DeriveFintype

/-!
# Referential prominence

Aissen's definiteness scale ranks personal pronouns above proper names above definite NPs above
specific indefinites above non-specific ones, extending the definiteness hierarchy to names and
pronouns; its cut at the definites is `Reference.Definiteness`. The other referential dimensions
have their own files, `Reference.Animacy` and `Reference.Nominality`, and a marking conditioned by
them fits an order on them when its marked zones are upper or lower sets (`Alignment.Fits`).

## Main declarations

* `DefinitenessScale`: Aissen's definiteness scale, as a linear order, with its cut
  `DefinitenessScale.definiteness` at the definites.

## References

* [J. Aissen, *Differential Object Marking: Iconicity vs. Economy* (2003)][aissen-2003]
-/

@[expose] public section

namespace Reference.Prominence

/-! ### The definiteness scale -/

/-- A position on Aissen's definiteness scale, Pronoun > Name > Definite > Indefinite Specific >
NonSpecific, which extends the hierarchy definite > specific > non-specific to proper names and
personal pronouns. -/
inductive DefinitenessScale where
  | nonSpecific
  | indefiniteSpecific
  | definite
  | properName
  | personalPronoun
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace DefinitenessScale

/-- The rank on the scale, 0 for the non-specific indefinites up to 4 for the personal
pronouns. -/
def rank : DefinitenessScale → ℕ
  | .nonSpecific => 0
  | .indefiniteSpecific => 1
  | .definite => 2
  | .properName => 3
  | .personalPronoun => 4

instance : LinearOrder DefinitenessScale := LinearOrder.lift' rank (by decide)

/-- The positions, most prominent first. -/
def all : List DefinitenessScale :=
  [.personalPronoun, .properName, .definite, .indefiniteSpecific, .nonSpecific]

/-- A position is definite when it is a pronoun, a name or a definite NP, and indefinite when
it is an indefinite, specific or not. -/
def definiteness (d : DefinitenessScale) : Definiteness :=
  if .definite ≤ d then .definite else .indefinite

theorem definiteness_monotone : Monotone definiteness := by
  intro a b; revert a b; decide

end DefinitenessScale

end Reference.Prominence
