import Linglib.Semantics.Degree.Aggregation
import Linglib.Semantics.Degree.Measure.Basic
import Linglib.Semantics.Genericity.SortedOntology
import Mathlib.Algebra.Order.Field.Basic

/-!
# Solt (2018): Proportional Comparatives and Relative Scales

This file formalizes the measurement-based account of proportional comparatives of
[solt-2018b]. *More residents of Ithaca than New York City know their neighbors* has a
salient true reading comparing proportions although the absolute counts point the other
way, so the degrees a quantity comparative ranges over must include degrees of proportion.
Two accounts deliver them. On the ambiguity account, *many* and *few* have a cardinal and
a proportional lexical entry ([partee-1989], in the degree versions of [romero-2015]). On
the paper's account they are unambiguous gradable quantifiers over degrees ([solt-2015]),
and a null head Meas introduces a contextually determined measure function, monotone on
the part-whole order ([schwarzschild-2006]), which may be domain-restricted to the parts of
a totality and in particular proportional. `proportionalMeasure` divides a part's measure
by the totality's, an instance of the substrate's `spatialNormalizedScore`; it inherits
monotonicity (`proportionalMeasure_monotonic`), ranges over the unit interval, and is
invariant under rescaling of the underlying measure, so degree-denoting *n percent* is a
point on its scale (`percent_iff_proportionalMeasure`, against the lexical entry for
*percent* of [ahn-sauerland-2017]). `readings_diverge` states when the cardinal and
proportional readings of a comparative come apart.

The accounts part on the distribution of readings. With an individual-level predicate
([carlson-1977], [milsark-1977]) or in a partitive, the measure is domain-restricted; the
standard range of the positive morpheme then sits inside the bounded segment of the
scale, so the positive form is proportional only, while the comparative composes with the
measure directly and keeps its cardinal reading. `reading` states how each form reads a
kind of measure and `Licensed` the readings a context leaves open; `restricted_asymmetry`
derives the asymmetry. The ambiguity account has no relative-but-not-proportional
measurement, and once an individual-level predicate confines it to the proportional entry,
the comparative loses its cardinal reading too (`ambiguity_symmetric`).

## Implementation notes

The paper reports the populations of Ithaca and New York City in prose and no counts of
residents who know their neighbours, so the divergence of the two readings is stated
symbolically: a smaller part is the larger share exactly when its totality is small enough.
Solt's other 2018 paper, the multidimensionality chapter [solt-2018a], is formalized in
`Studies/Solt2018a.lean`.

## References

* [solt-2018b]
* [partee-1989]
* [romero-2015]
* [solt-2015]
* [schwarzschild-2006]
* [ahn-sauerland-2017]
* [carlson-1977]
* [milsark-1977]
-/

namespace Solt2018b

open Degree Degree.Aggregation Semantics.Kinds.SortedOntology

variable {α : Type*} (μ : α → ℚ)

/-! ### The proportional measure function -/

/-- The proportional measure function: a part's measure relative to the totality `tot`,
and 0 when the totality has measure 0, the zero-extent convention of
`spatialNormalizedScore`. -/
def proportionalMeasure (tot y : α) : ℚ :=
  spatialNormalizedScore [1] [μ] (λ _ => μ tot) y

theorem proportionalMeasure_eq (tot y : α) (h : μ tot ≠ 0) :
    proportionalMeasure μ tot y = μ y / μ tot := by
  simp [proportionalMeasure, spatialNormalizedScore, weightedScore, h]

theorem proportionalMeasure_zero (tot y : α) (h : μ tot = 0) :
    proportionalMeasure μ tot y = 0 :=
  spatialNormalizedScore_zero _ _ _ _ h

/-- The totality is the whole of itself. -/
theorem proportionalMeasure_self_eq_one (tot : α) (htot : 0 < μ tot) :
    proportionalMeasure μ tot tot = 1 := by
  rw [proportionalMeasure_eq _ _ _ htot.ne']
  exact div_self htot.ne'

/-- The monotonicity constraint on the measure `Meas` introduces (the substrate's
`admissibleMeasure`) is inherited by the proportional measure. -/
theorem proportionalMeasure_monotonic [Preorder α] (hμ : admissibleMeasure μ)
    (tot : α) {y z : α} (htot : 0 < μ tot) (hyz : y < z) :
    proportionalMeasure μ tot y < proportionalMeasure μ tot z := by
  rw [proportionalMeasure_eq _ _ _ htot.ne', proportionalMeasure_eq _ _ _ htot.ne']
  exact (div_lt_div_iff_of_pos_right htot).mpr (hμ hyz)

theorem proportionalMeasure_nonneg (hnn : ∀ x, 0 ≤ μ x) (tot y : α) :
    0 ≤ proportionalMeasure μ tot y :=
  spatialNormalizedScore_nonneg _ _ _ _ (by simpa [weightedScore] using hnn y) (hnn tot)

theorem proportionalMeasure_le_one [Preorder α] (hμ : Monotone μ)
    (tot y : α) (hy : y ≤ tot) (htot : 0 < μ tot) :
    proportionalMeasure μ tot y ≤ 1 :=
  spatialNormalizedScore_le_one _ _ _ _ (by simpa [weightedScore] using hμ hy) htot

/-- The proportional scale is the unit interval: a part of the totality measures between
0 and 1. -/
theorem proportionalMeasure_mem_unit_interval [Preorder α]
    (hnn : ∀ x, 0 ≤ μ x) (hμ : Monotone μ) (tot y : α) (hy : y ≤ tot) (htot : 0 < μ tot) :
    proportionalMeasure μ tot y ∈ Set.Icc (0 : ℚ) 1 :=
  ⟨proportionalMeasure_nonneg μ hnn tot y, proportionalMeasure_le_one μ hμ tot y hy htot⟩

/-- Rescaling the underlying measure leaves proportions unchanged: only the cardinal
reading depends on the unit of measurement. -/
theorem proportionalMeasure_scale_invariant (k : ℚ) (hk : k ≠ 0)
    (tot y : α) (htot : μ tot ≠ 0) :
    proportionalMeasure (λ x => k * μ x) tot y = proportionalMeasure μ tot y := by
  rw [proportionalMeasure_eq _ tot y (mul_ne_zero hk htot),
      proportionalMeasure_eq _ tot y htot, mul_div_mul_left _ _ hk]

/-- *n percent of x are P* on the lexical entry for *percent* of [ahn-sauerland-2017],
which lexicalizes the division, holds exactly when the proportional measure of the
P-part of `x` is the degree `n / 100`, a point on the proportional scale. -/
theorem percent_iff_proportionalMeasure [SemilatticeInf α] (x p : α) (n : ℚ)
    (hx : μ x ≠ 0) :
    μ (x ⊓ p) / μ x = n / 100 ↔ proportionalMeasure μ x (x ⊓ p) = n / 100 := by
  rw [proportionalMeasure_eq _ _ _ hx]

/-! ### The two readings of a quantity comparative -/

/-- *More A than B Q* on the cardinal reading: the A-part with the property outmeasures
the B-part. -/
def CardinalReading (a b : α) : Prop := μ b < μ a

/-- *More A than B Q* on the proportional reading, with the measure `Meas` introduces
proportional to each clause's totality: the A-part is the larger share of its totality. -/
def ProportionalReading (A B a b : α) : Prop :=
  proportionalMeasure μ B b < proportionalMeasure μ A a

theorem proportionalReading_iff {A B a b : α} (hA : 0 < μ A) (hB : 0 < μ B) :
    ProportionalReading μ A B a b ↔ μ b * μ A < μ a * μ B := by
  rw [ProportionalReading, proportionalMeasure_eq _ _ _ hA.ne',
    proportionalMeasure_eq _ _ _ hB.ne', div_lt_div_iff₀ hB hA]

/-- The readings come apart: a part that is outmeasured by the other is nonetheless the
larger share whenever its totality is small enough, as with Ithaca's thirty thousand
residents against New York City's eight million. -/
theorem readings_diverge {A B a b : α} (hA : 0 < μ A) (hB : 0 < μ B)
    (h : μ a < μ b) (h' : μ b * μ A < μ a * μ B) :
    ¬ CardinalReading μ a b ∧ ProportionalReading μ A B a b :=
  ⟨not_lt.2 h.le, (proportionalReading_iff μ hA hB).2 h'⟩

/-! ### The distribution of readings -/

/-- The varieties of measure function `Meas` may introduce: unrestricted, restricted to
the parts of a totality, and the proportional special case of the latter. -/
inductive MeasureKind where
  | unrestricted
  | domainRestricted
  | proportional
  deriving DecidableEq, Repr

/-- The kinds whose range is a bounded segment of the scale. -/
def MeasureKind.IsRestricted : MeasureKind → Prop
  | .unrestricted => False
  | .domainRestricted => True
  | .proportional => True

instance (k : MeasureKind) : Decidable k.IsRestricted := by
  cases k <;> unfold MeasureKind.IsRestricted <;> infer_instance

/-- The kinds a predicate leaves available: an individual-level predicate forces a
domain-restricted measure. -/
def allowedKinds : PredicateLevel → MeasureKind → Prop
  | .stageLevel, _ => True
  | .individualLevel, k => k.IsRestricted

/-- Cardinal or proportional reading of a quantity word. -/
inductive Reading where
  | cardinal
  | proportional
  deriving DecidableEq, Repr

/-- The positive form, bound by the positive morpheme, and the comparative. -/
inductive QForm where
  | positive
  | comparative
  deriving DecidableEq, Repr

/-- How each form reads a kind of measure. The comparative compares the degrees the
measure delivers, cardinal unless the measure is proportional. The positive morpheme's
standard range sits inside the bounded segment that is a restricted measure's range, so
either restricted kind gives the positive form its proportional reading. -/
def reading : QForm → MeasureKind → Reading
  | .comparative, .proportional => .proportional
  | .comparative, _ => .cardinal
  | .positive, .unrestricted => .cardinal
  | .positive, _ => .proportional

/-- A context whose available kinds are `allowed` licenses a reading of a form when some
available kind yields it. -/
def Licensed (allowed : MeasureKind → Prop) (f : QForm) (r : Reading) : Prop :=
  ∃ k, allowed k ∧ reading f k = r

/-- A stage-level predicate licenses both readings of both forms, as in *few egg-laying
mammals were found in our survey, perhaps because there are few*. -/
theorem stageLevel_licensed (f : QForm) (r : Reading) :
    Licensed (allowedKinds .stageLevel) f r := by
  cases f <;> cases r <;> first
    | exact ⟨.unrestricted, trivial, rfl⟩
    | exact ⟨.proportional, trivial, rfl⟩

/-- With only restricted kinds available, the positive form is proportional: *few
egg-laying mammals suckle their young* cannot mean that there are few. -/
theorem restricted_positive_iff (r : Reading) :
    Licensed MeasureKind.IsRestricted .positive r ↔ r = .proportional := by
  constructor
  · rintro ⟨k, hk, rfl⟩; cases k <;> simp_all [MeasureKind.IsRestricted, reading]
  · rintro rfl; exact ⟨.domainRestricted, trivial, rfl⟩

/-- The asymmetry that adjudicates: with only restricted kinds available, under an
individual-level predicate or in a partitive, the comparative keeps its cardinal reading
through an ordinary domain-restricted measure while the positive form loses it. -/
theorem restricted_asymmetry :
    Licensed MeasureKind.IsRestricted .comparative .cardinal ∧
    ¬ Licensed MeasureKind.IsRestricted .positive .cardinal :=
  ⟨⟨.domainRestricted, trivial, rfl⟩, by simp [restricted_positive_iff]⟩

theorem allowedKinds_individualLevel :
    allowedKinds .individualLevel = MeasureKind.IsRestricted := rfl

/-- The ambiguity account's inventory: a cardinal and a proportional entry, and no
relative-but-not-proportional measurement. -/
def ambiguityKinds : MeasureKind → Prop
  | .domainRestricted => False
  | _ => True

/-- On the ambiguity account, whatever confines the positive form to its proportional
reading confines the comparative too: with the inventory reduced to the proportional
entry, both forms read alike, and the cardinal reading of *more residents of Ithaca than
New York City know their neighbors* is lost. -/
theorem ambiguity_symmetric (r : Reading) :
    Licensed (λ k => ambiguityKinds k ∧ k.IsRestricted) .positive r ↔
      Licensed (λ k => ambiguityKinds k ∧ k.IsRestricted) .comparative r := by
  constructor <;> rintro ⟨k, hk, rfl⟩ <;>
    cases k <;> simp_all [ambiguityKinds, MeasureKind.IsRestricted, reading] <;>
    exact ⟨.proportional, ⟨trivial, trivial⟩, rfl⟩

end Solt2018b
