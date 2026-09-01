import Linglib.Core.Order.ComparativeScale
import Linglib.Semantics.Degree.Comparison

/-!
# Polar measures

This file defines polar measures: a measure function `μ : E → D` bundled with the
lexical classification of the scale it lexicalizes — its boundedness (the
`ComparativeScale` it extends) and the pole of the scale the predicate names. A
gradable adjective's lexical entry is a scale together with a polarity along it;
antonyms such as *tall*/*short* measure on the same scale and differ only in
polarity, so the threshold property of the positive form is derived from the
polarity rather than stored: "at least `d`" on the positive pole, "at most `d`" on
the negative one.

## Main declarations

* `PolarMeasure`: a measure function with the boundedness and polarity of its scale.
* `PolarMeasure.degreeProperty`: the threshold property of the positive form,
  `Comparison.ge.over μ` or `Comparison.le.over μ` by polarity.
* `PolarMeasure.numeral`: the cardinality measure of a numeral on the scale `ℕ`.

## Implementation notes

`boundedness` classifies the *lexicalized* scale and need not agree with the order
structure of the carrier `D`: an open-scale adjective can be measured on a finite
carrier for computation, and licensing (`IsLicensed`, inherited from
`ComparativeScale`) reads the classification. `numeral` is the one constructor whose
carrier is the scale itself, and its classification is faithful to `ℕ`
(`hasMin_numeral_iff`, `hasMax_numeral_iff`).

## References

* [C. Kennedy, *Vagueness and grammar: the semantics of relative and absolute gradable
  adjectives* (2007)][kennedy-2007]
* [C. Kennedy, *A "de-Fregean" semantics (and neo-Gricean pragmatics) for modified and
  unmodified numerals* (2015)][kennedy-2015]
* [D. Lassiter and N. D. Goodman, *Adjectival vagueness in a Bayesian model of
  interpretation* (2017)][lassiter-goodman-2017]
-/

namespace Degree

open Core.Order

/-- A measure function `μ : E → D` with the boundedness and polarity of the scale it
lexicalizes; antonyms share `μ` and differ only in `polarity`. -/
@[ext]
structure PolarMeasure (D : Type*) [Preorder D] (E : Type*) extends ComparativeScale D where
  /-- The measure function. -/
  μ : E → D
  /-- The pole of the scale the predicate names (*tall* positive, *short* negative). -/
  polarity : ScalePolarity := .positive

namespace PolarMeasure

variable {D : Type*} [Preorder D] {E : Type*}

/-- The threshold property of the positive form: the entities measuring at least `d` on
the positive pole, at most `d` on the negative one. -/
def degreeProperty (dm : PolarMeasure D E) : D → Set E :=
  match dm.polarity with
  | .positive => Comparison.ge.over dm.μ
  | .negative => Comparison.le.over dm.μ

/-! ### Numerals -/

/-- The cardinality measure `μ : E → ℕ` of a numeral. The scale `ℕ` of cardinalities has a
least degree and no greatest, so its classification is `lowerBounded`. -/
@[simps]
def numeral (μ : E → ℕ) : PolarMeasure ℕ E := { boundedness := .lowerBounded, μ }

@[simp] theorem isLicensed_numeral (μ : E → ℕ) : (numeral μ).IsLicensed := trivial

@[simp] theorem degreeProperty_numeral (μ : E → ℕ) :
    (numeral μ).degreeProperty = Comparison.ge.over μ := rfl

/-- The classification of `numeral` is faithful to its carrier: `ℕ` has a least degree. -/
theorem hasMin_numeral_iff (μ : E → ℕ) :
    (numeral μ).boundedness.HasMin ↔ ∃ m : ℕ, IsBot m :=
  iff_of_true trivial ⟨0, fun _ => Nat.zero_le _⟩

/-- The classification of `numeral` is faithful to its carrier: `ℕ` has no greatest degree. -/
theorem hasMax_numeral_iff (μ : E → ℕ) :
    (numeral μ).boundedness.HasMax ↔ ∃ m : ℕ, IsTop m :=
  iff_of_false id fun ⟨m, hm⟩ => not_isMax m hm.isMax

end PolarMeasure

end Degree
