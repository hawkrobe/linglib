module

public import Linglib.Semantics.Reference.Animacy
public import Linglib.Semantics.Reference.Definiteness
public import Mathlib.Order.Nat
public import Mathlib.Tactic.DeriveFintype

/-!
# Referential prominence

This file defines the scales of referential prominence that condition differential argument
marking and number marking.

The animacy scale is `Reference.Animacy`. The definiteness scale is Aissen's, which extends the
definiteness hierarchy to proper names and personal pronouns and whose cut at the definites is
`Reference.Definiteness`. The animacy hierarchy that conditions nominal plural marking is
Haspelmath's, which refines Corbett's version of Smith-Stark's by splitting the animals into higher
and lower and the inanimates into discrete and nondiscrete. A marking conditioned by these scales
fits them when its marked zones are upper or lower sets (`Alignment.Fits`).

## Main declarations

* `DefinitenessScale`: Aissen's definiteness scale, as a linear order, with its cut
  `DefinitenessScale.definiteness` at the definites.
* `AnimacyHierarchy`: the hierarchy of plural marking, from the speaker down to the nondiscrete
  inanimates.

What is specific to a paper lives with that paper: the scenario universals in
`Studies/Haspelmath2021.lean`, the OT typology in `Studies/Aissen2003.lean`, and the prominence
principle of differential indexing in `Studies/Just2024.lean`.

## References

* [J. Aissen, *Differential Object Marking: Iconicity vs. Economy* (2003)][aissen-2003]
* [G. G. Corbett, *Number* (2000)][corbett-2000]
* [M. Haspelmath, *Occurrence of Nominal Plurality* (2013)][haspelmath-2013b]
* [M. Haspelmath, *Role-Reference Associations and the Explanation of Argument Coding Splits*
  (2021)][haspelmath-2021]
* [T. C. Smith-Stark, *The Plurality Split* (1974)][smith-stark-1974]
-/

@[expose] public section

namespace Reference.Prominence

/-! ### The animacy hierarchy -/

/-- Haspelmath's animacy hierarchy of nominal plural marking runs speaker > addressee > third
person > kinship terms > other humans > higher animals > lower animals > discrete inanimates >
nondiscrete inanimates. Corbett's has one animate and one inanimate position, and splits the
animate one where Miya needs it. A language marking plural at a point on the hierarchy marks it
at all higher points. -/
inductive AnimacyHierarchy where
  | speaker
  | addressee
  | thirdPerson
  | kin
  | human
  | higherAnimal
  | lowerAnimal
  | discreteInanimate
  | nondiscreteInanimate
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The rank on the hierarchy, 8 for the speaker down to 0 for the nondiscrete inanimates. -/
def AnimacyHierarchy.rank : AnimacyHierarchy → ℕ
  | .speaker => 8
  | .addressee => 7
  | .thirdPerson => 6
  | .kin => 5
  | .human => 4
  | .higherAnimal => 3
  | .lowerAnimal => 2
  | .discreteInanimate => 1
  | .nondiscreteInanimate => 0

/-- The hierarchy is ordered by rank, the speaker at the top. -/
instance : LinearOrder AnimacyHierarchy := LinearOrder.lift' AnimacyHierarchy.rank (by decide)

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
