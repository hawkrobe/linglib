import Linglib.Core.Combinatorics.SimpleGraph.MaximalIndepSet
import Mathlib.Data.Sign.Defs

/-!
# Dimensions of social evaluation

This file defines the dimensions on which hearers evaluate a speaker and their poles. The
dimensions are competence and warmth, the two universal dimensions of social cognition of the
Stereotype Content Model [fiske-cuddy-glick-xu-2002] [fiske-cuddy-glick-2007], and
anti-solidarity, the factor of [beltrama-solt-burnett-2023]'s ratings that loads apart from
warmth. A pole is one end of a dimension, two poles are incompatible when they are the two ends
of one dimension, and a persona, a maximal set of compatible poles in the sense of
[burnett-2019], chooses one pole of each dimension.

## Main definitions

* `Dimension`: competence, warmth and anti-solidarity.
* `Pole`: the six ends of the dimensions, with `Pole.dimension` and `Pole.polarity`.
* `Pole.incompatible`: the graph joining the two poles of each dimension.

## Main results

* `Pole.eq_iff`: a pole is determined by its dimension and polarity.
* `Pole.mem_maximalIndepSets_iff`: the personae are the sets with exactly one pole of each
  dimension.

## References

* [fiske-cuddy-glick-xu-2002]
* [fiske-cuddy-glick-2007]
* [beltrama-solt-burnett-2023]
* [burnett-2019]
-/

namespace SocialMeaning

/-- The dimensions of social evaluation are competence and warmth, and anti-solidarity, the
factor on which pedantic and uptight load apart from the warmth scales. -/
inductive Dimension where
  | competence
  | warmth
  | antiSolidarity
  deriving DecidableEq

instance : Fintype Dimension :=
  ⟨{.competence, .warmth, .antiSolidarity}, λ d => by cases d <;> simp⟩

/-- A pole is one end of a dimension of social evaluation. -/
inductive Pole where
  | competent
  | incompetent
  | warm
  | cold
  | solidary
  | antiSolidary
  deriving DecidableEq

instance : Fintype Pole :=
  ⟨{.competent, .incompetent, .warm, .cold, .solidary, .antiSolidary}, λ p => by cases p <;> simp⟩

/-- The dimension a pole is an end of. -/
def Pole.dimension : Pole → Dimension
  | .competent | .incompetent => .competence
  | .warm | .cold => .warmth
  | .solidary | .antiSolidary => .antiSolidarity

/-- The polarity of a pole is positive at the end its dimension is named for, competent, warm
and antisolidary, and negative at the other. -/
def Pole.polarity : Pole → SignType
  | .competent | .warm | .antiSolidary => 1
  | .incompetent | .cold | .solidary => -1

/-- A pole is determined by its dimension and polarity. -/
theorem Pole.eq_iff {p q : Pole} :
    p = q ↔ p.dimension = q.dimension ∧ p.polarity = q.polarity := by
  revert p q; decide

/-- Two poles are incompatible when they are the two ends of one dimension. -/
def Pole.incompatible : SimpleGraph Pole where
  Adj p q := p ≠ q ∧ p.dimension = q.dimension
  symm := ⟨λ _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨λ _ h => h.1 rfl⟩

instance : DecidableRel Pole.incompatible.Adj :=
  λ p q => inferInstanceAs (Decidable (p ≠ q ∧ _))

theorem Pole.incompatible_adj (p q : Pole) :
    Pole.incompatible.Adj p q ↔ p.dimension = q.dimension ∧ p.polarity ≠ q.polarity := by
  revert p q; decide

/-- The personae are the sets with exactly one pole of each dimension. -/
theorem Pole.mem_maximalIndepSets_iff (s : Finset Pole) :
    s ∈ Pole.incompatible.maximalIndepSets ↔ ∀ d, (s.filter (·.dimension = d)).card = 1 := by
  revert s; decide +kernel

end SocialMeaning
