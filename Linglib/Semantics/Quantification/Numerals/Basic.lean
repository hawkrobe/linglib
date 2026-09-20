/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Degree.Comparison
import Linglib.Semantics.Exhaustification.Chain

/-!
# Numeral meanings

This file defines the meanings of the numeral forms on counts. A bare numeral and its four
modifications, *more than*, *fewer than*, *at least* and *at most*, are the five comparisons
of `Degree.Comparison` applied to the identity measure: in Kennedy's de-Fregean semantics the
form with relation `REL` and number `m` is true of a degree property whose greatest degree
stands in `REL` to `m`, and on counts that degree is the count itself. The meanings of the
modified forms are common ground. Accounts differ on the bare numeral, which has the
two-sided meaning `bareMeaning` for Kennedy and the lower-bounded meaning `atLeastMeaning` in
the tradition of Horn, each account deriving the other reading. Exhaustifying the
lower-bounded meaning against the scale of higher numerals gives the two-sided one, and
Kennedy's type lowering takes the two-sided meaning to the lower-bounded one
(`Degree.typeLower_eqOver_iff`).

## Main definitions

* `Numerals.ModifierClass`, `Numerals.ModifierKind`: Nouwen's two classes of numeral modifier
  and the constructions modifiers are built on, with `ModifierKind.modifierClass`.
* `Numerals.bareMeaning`, `Numerals.moreThanMeaning`, `Numerals.fewerThanMeaning`,
  `Numerals.atLeastMeaning`, `Numerals.atMostMeaning`: the meanings of the five forms.
* `Numerals.exhNumeral`: the lower-bounded meaning exhaustified against the next numeral.

## Main results

* `Numerals.exhNumeral_iff_bare`: the exhaustified lower-bounded meaning is the two-sided one.
* `Numerals.exhNumeral_eq_exhChain`: exhaustifying against the next numeral is exhaustifying
  against the whole scale.

## References

* [C. Kennedy, *A "de-Fregean" semantics (and neo-Gricean pragmatics) for modified and
  unmodified numerals* (2015)][kennedy-2015]
* [R. Nouwen, *Two kinds of modified numerals* (2010)][nouwen-2010]
* [L. R. Horn, *On the Semantic Properties of Logical Operators in English* (1972)][horn-1972]
* [B. Spector, *Bare numerals and scalar implicatures* (2013)][spector-2013]
* [G. Chierchia, D. Fox and B. Spector, *Scalar Implicature as a Grammatical Phenomenon*
  (2012)][chierchia-fox-spector-2012]
-/

namespace Numerals

open Degree

/-! ### Numeral modifiers -/

/-- The two classes of numeral modifiers of [nouwen-2010]. A Class A modifier relates the
numeral to a definite amount, so *a hexagon has fewer than 11 sides* is a weak truth. A Class B
modifier places a bound on a range of amounts, so *a hexagon has at most 10 sides* is odd and
the modifier conveys that the speaker does not know the amount.

[kennedy-2015] reduces the split to the ordering the modifier expresses, exclusive for Class A
and inclusive for Class B (`Degree.Comparison.boundary_mem`), and derives the ignorance as an
implicature. The categorical pattern is contested: [schwarz-buccola-hamilton-2012] show
*at most* and *up to* dissociate, [cremers-coppock-dotlacil-roelofsen-2022] find the ignorance
contrast graded and dependent on the question under discussion, and [enguehard-2018] derives
the inferences of comparative numerals from granularity. -/
inductive ModifierClass where
  | classA
  | classB
  deriving Repr, DecidableEq

/-- The kinds of numeral modifier in [nouwen-2010]'s survey, by the construction the modifier is
built on. -/
inductive ModifierKind where
  /-- A comparative: *more than*, *fewer than*. -/
  | comparative
  /-- A superlative: *at least*, *at most*. -/
  | superlative
  /-- A locative preposition: *over*, *under*. -/
  | locative
  /-- A directional preposition: *up to*, *from*. -/
  | directional
  /-- An adverb of minimality or maximality: *minimally*, *maximally*. -/
  | adverbial
  deriving Repr, DecidableEq

/-- The class of each kind. The comparatives are [nouwen-2010]'s model of Class A and the
superlatives and the adverbs of Class B, and the prepositional modifiers follow their spatial
use: a locative preposition gives a Class A modifier and a directional one a Class B
modifier. -/
def ModifierKind.modifierClass : ModifierKind → ModifierClass
  | .comparative | .locative => .classA
  | .superlative | .directional | .adverbial => .classB

/-! ### The meanings of the five forms -/

variable (m n : ℕ)

/-- The two-sided meaning of the bare numeral `m` is true of the count `m` alone. -/
def bareMeaning : ℕ → ℕ → Prop := fun m n ↦ n ∈ Comparison.eq.over id m

/-- *More than `m`* is true of the counts that exceed `m`. -/
def moreThanMeaning : ℕ → ℕ → Prop := fun m n ↦ n ∈ Comparison.gt.over id m

/-- *Fewer than `m`* is true of the counts below `m`. -/
def fewerThanMeaning : ℕ → ℕ → Prop := fun m n ↦ n ∈ Comparison.lt.over id m

/-- *At least `m`*, which is also the lower-bounded meaning of the bare numeral, is true of the
counts that reach `m`. -/
def atLeastMeaning : ℕ → ℕ → Prop := fun m n ↦ n ∈ Comparison.ge.over id m

/-- *At most `m`* is true of the counts that do not exceed `m`. -/
def atMostMeaning : ℕ → ℕ → Prop := fun m n ↦ n ∈ Comparison.le.over id m

@[simp] theorem bareMeaning_def : bareMeaning m n ↔ n = m := Iff.rfl
@[simp] theorem moreThanMeaning_def : moreThanMeaning m n ↔ n > m := Iff.rfl
@[simp] theorem fewerThanMeaning_def : fewerThanMeaning m n ↔ n < m := Iff.rfl
@[simp] theorem atLeastMeaning_def : atLeastMeaning m n ↔ n ≥ m := Iff.rfl
@[simp] theorem atMostMeaning_def : atMostMeaning m n ↔ n ≤ m := Iff.rfl

instance : Decidable (bareMeaning m n) := inferInstanceAs (Decidable (n = m))
instance : Decidable (moreThanMeaning m n) := inferInstanceAs (Decidable (n > m))
instance : Decidable (fewerThanMeaning m n) := inferInstanceAs (Decidable (n < m))
instance : Decidable (atLeastMeaning m n) := inferInstanceAs (Decidable (n ≥ m))
instance : Decidable (atMostMeaning m n) := inferInstanceAs (Decidable (n ≤ m))

/-! ### Exhaustification

On the account of [chierchia-fox-spector-2012] that [spector-2013] discusses, the bare numeral
has the lower-bounded meaning and its two-sided reading comes from a covert exhaustivity
operator, which asserts *at least `m`* and denies *at least `m + 1`*. [kennedy-2015] runs the
derivation the other way, lowering the two-sided meaning to the lower-bounded one. -/

/-- The lower-bounded meaning of `m` exhaustified against the next numeral. -/
def exhNumeral : Prop := atLeastMeaning m n ∧ ¬ atLeastMeaning (m + 1) n

instance : Decidable (exhNumeral m n) := inferInstanceAs (Decidable (_ ∧ _))

/-- The exhaustified lower-bounded meaning is the two-sided meaning. -/
theorem exhNumeral_iff_bare : exhNumeral m n ↔ bareMeaning m n := by
  simp only [exhNumeral, atLeastMeaning_def, bareMeaning_def]
  omega

/-- Exhaustifying against the next numeral is exhaustifying against the whole scale of higher
numerals, which is an entailment chain (`Exhaustification.exhChain_iff_succ`). -/
theorem exhNumeral_eq_exhChain :
    exhNumeral m n ↔ Exhaustification.exhChain (fun k ↦ atLeastMeaning (m + k)) 0 n := by
  rw [Exhaustification.exhChain_iff_succ
      (fun j k hjk d hd ↦ by simp only [atLeastMeaning_def, ge_iff_le] at hd ⊢; omega)
      Nat.zero_lt_one fun j hj ↦ hj]
  simp [exhNumeral]

end Numerals
