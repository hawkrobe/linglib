/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Degree.Comparison
import Linglib.Semantics.Exhaustification.Chain

/-!
# Numeral meanings

This file collects what is specific to numerals over the degree comparisons of
`Semantics/Degree/Comparison.lean`. A bare numeral and its four modifications, *more than*,
*fewer than*, *at least* and *at most*, are the five comparisons of `Degree.Comparison`: in
Kennedy's de-Fregean semantics the form with relation `REL` and number `m` is true of a degree
property whose greatest degree stands in `REL` to `m`. On counts the form denotes the interval
`c.interval m`, and on worlds measured by `μ` the set `c.over μ m`, so the forms have no names
of their own here. The meanings of the modified forms are common ground. Accounts differ on the
bare numeral, which has the two-sided meaning `Comparison.eq.interval m` for Kennedy and the
lower-bounded meaning `Comparison.ge.interval m` in the tradition of Horn, each account
deriving the other reading. Exhaustifying the lower-bounded meaning against the scale of
higher numerals gives the two-sided one, and Kennedy's type lowering takes the two-sided
meaning to the lower-bounded one (`Degree.typeLower_eqOver_iff`).

## Main definitions

* `Numerals.ModifierClass`, `Numerals.ModifierKind`: Nouwen's two classes of numeral modifier
  and the constructions modifiers are built on, with `ModifierKind.modifierClass`.
* `Numerals.exhNumeral`: the lower-bounded meaning exhaustified against the next numeral.

## Main results

* `Numerals.exhNumeral_eq`: the exhaustified lower-bounded meaning is the two-sided one.
* `Numerals.mem_exhNumeral_iff_exhChain`: exhaustifying against the next numeral is
  exhaustifying against the whole scale.

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

/-! ### Exhaustification

On the account of [chierchia-fox-spector-2012] that [spector-2013] discusses, the bare numeral
has the lower-bounded meaning and its two-sided reading comes from a covert exhaustivity
operator, which asserts *at least `m`* and denies *at least `m + 1`*. [kennedy-2015] runs the
derivation the other way, lowering the two-sided meaning to the lower-bounded one. -/

variable {m n : ℕ}

/-- The lower-bounded meaning of `m` exhaustified against the next numeral. -/
def exhNumeral (m : ℕ) : Set ℕ := Comparison.ge.interval m \ Comparison.ge.interval (m + 1)

/-- The exhaustified lower-bounded meaning is the two-sided meaning. -/
theorem exhNumeral_eq (m : ℕ) : exhNumeral m = Comparison.eq.interval m := by
  ext n
  simp only [exhNumeral, Comparison.interval_ge, Comparison.interval_eq, Set.mem_sdiff,
    Set.mem_Ici, Set.mem_singleton_iff]
  omega

instance : DecidablePred (· ∈ exhNumeral m) := fun n ↦
  decidable_of_iff (n = m) (by rw [exhNumeral_eq]; rfl)

/-- Exhaustifying against the next numeral is exhaustifying against the whole scale of higher
numerals, which is an entailment chain (`Exhaustification.exhChain_iff_succ`). -/
theorem mem_exhNumeral_iff_exhChain :
    n ∈ exhNumeral m ↔
      Exhaustification.exhChain (fun k ↦ (· ∈ Comparison.ge.interval (m + k))) 0 n := by
  rw [Exhaustification.exhChain_iff_succ (φ := fun k ↦ (· ∈ Comparison.ge.interval (m + k)))
      (fun j k hjk d (hd : m + k ≤ d) ↦ show m + j ≤ d by omega)
      Nat.zero_lt_one fun j hj ↦ hj]
  rfl

end Numerals
