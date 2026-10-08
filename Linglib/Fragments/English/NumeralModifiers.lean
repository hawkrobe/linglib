module

public import Linglib.Semantics.Quantification.Numerals.Basic
public import Mathlib.Order.Interval.Set.Basic

/-!
# English numeral modifiers

This file records the English expressions that combine with a numeral to bound, fix or
approximate the amount it names. The modifiers that set a bound are built on four
constructions in Nouwen's survey: the comparatives *more than* and *fewer than*, the
superlatives *at least* and *at most*, the locative prepositions *over* and *under* and the
directional prepositions *up to* and *from*, beside the adverbs *minimally* and *maximally*.
*Exactly* and *precisely* fix the amount, *about*, *around*, *approximately* and *roughly*
place it near the numeral, and *almost* and *nearly* place it near the numeral and short of it.

Each modifier is a `Numerals.Modifier`, denoting the set of readings the literature makes
available for it. A bound-setting modifier and an exactifier have the one reading of the
comparison they express, so a modifier of one class and its counterpart of the other differ in
whether the interval keeps the number. An approximator has a reading for each value of a
tolerance the context supplies: Égré, Spector, Mortier and Verheyen give *around n* the amounts
within the tolerance of `n` on either side, and on Penka's analysis *almost n* is false of `n` and
true of an amount close below it. Nouwen's two classes of modifier are derived from the kind of
construction, not stored.

## Main definitions

* `English.NumeralModifiers.approximator`, `English.NumeralModifiers.shortOf`: the modifiers
  with a reading for each tolerance, around the number and short of it.
* `English.NumeralModifiers.inventory`: the eighteen modifiers.

## Main results

* `English.NumeralModifiers.self_mem_approximator`: every reading of an approximator is true of
  the number itself, so the approximated numeral is entailed by the exact one.
* `English.NumeralModifiers.self_not_mem_shortOf`: no reading of *almost* or *nearly* is true of
  the number itself.

## Implementation notes

The amounts are natural numbers, as in `Semantics/Quantification/Numerals/Basic.lean`, and
truncated subtraction keeps the lower end of a tolerance interval at zero. *Between … and …*
takes two numerals and is not recorded.

## TODO

Blok argues that *up to n* asserts only a lower bound and implicates its upper bound, which is
why it is odd with the lowest number of a scale and does not license negative polarity items.
A reading here is truth-conditional content, so the reading recorded for *up to* is the upper
bound it shares with *at most*, and the split between asserted and implicated content is left
to the study of that paper.

## References

* [R. Nouwen, *Two kinds of modified numerals* (2010)][nouwen-2010]
* [C. Kennedy, *A "de-Fregean" semantics (and neo-Gricean pragmatics) for modified and
  unmodified numerals* (2015)][kennedy-2015]
* [D. Blok, *The semantics and pragmatics of directional numeral modifiers* (2015)][blok-2015]
* [P. Égré, B. Spector, A. Mortier and S. Verheyen, *On the Optimality of Vagueness: "Around",
  "Between" and the Gricean Maxims* (2023)][egre-etal-2023]
* [D. Penka, *"Almost there": The meaning of almost* (2006)][penka-2006]
-/

@[expose] public section

namespace English.NumeralModifiers

open Degree Numerals Semantics

/-! ### Bounds and exactifiers -/

/-- *more than*, a comparative, excludes the number from below. -/
def moreThan : Modifier := .ofComparison "more than" (some .comparative) .gt
/-- *fewer than*, a comparative, excludes the number from above. -/
def fewerThan : Modifier := .ofComparison "fewer than" (some .comparative) .lt
/-- *over*, a locative preposition, excludes the number from below. -/
def over : Modifier := .ofComparison "over" (some .locative) .gt
/-- *under*, a locative preposition, excludes the number from above. -/
def under : Modifier := .ofComparison "under" (some .locative) .lt
/-- *at least*, a superlative, bounds the amount from below. -/
def atLeast : Modifier := .ofComparison "at least" (some .superlative) .ge
/-- *at most*, a superlative, bounds the amount from above. -/
def atMost : Modifier := .ofComparison "at most" (some .superlative) .le
/-- *minimally*, an adverb, bounds the amount from below. -/
def minimally : Modifier := .ofComparison "minimally" (some .adverbial) .ge
/-- *maximally*, an adverb, bounds the amount from above. -/
def maximally : Modifier := .ofComparison "maximally" (some .adverbial) .le
/-- *up to*, a directional preposition, bounds the amount from above. -/
def upTo : Modifier := .ofComparison "up to" (some .directional) .le
/-- *from*, a directional preposition, bounds the amount from below. -/
def from_ : Modifier := .ofComparison "from" (some .directional) .ge
/-- *exactly* fixes the amount. -/
def exactly : Modifier := .ofComparison "exactly" none .eq
/-- *precisely* fixes the amount. -/
def precisely : Modifier := .ofComparison "precisely" none .eq

/-! ### Approximators -/

/-- An approximator places the amount within a tolerance of the number on either side, one
reading for each tolerance `y` ([egre-etal-2023]). -/
def approximator (form : String) : Modifier :=
  ⟨form, none, Set.range fun y n ↦ Set.Icc (n - y) (n + y)⟩

/-- A modifier like *almost* places the amount within a tolerance below the number and short of
it, one reading for each tolerance `y` ([penka-2006]). -/
def shortOf (form : String) : Modifier := ⟨form, none, Set.range fun y n ↦ Set.Ico (n - y) n⟩

/-- *about*, an approximator. -/
def about : Modifier := approximator "about"
/-- *around*, an approximator. -/
def around : Modifier := approximator "around"
/-- *approximately*, an approximator. -/
def approximately : Modifier := approximator "approximately"
/-- *roughly*, an approximator. -/
def roughly : Modifier := approximator "roughly"
/-- *almost* stops short of the number. -/
def almost : Modifier := shortOf "almost"
/-- *nearly* stops short of the number. -/
def nearly : Modifier := shortOf "nearly"

/-- The English numeral modifiers. -/
def inventory : List Modifier :=
  [moreThan, fewerThan, over, under, atLeast, atMost, minimally, maximally, upTo, from_,
    exactly, precisely, about, around, approximately, roughly, almost, nearly]

variable {form : String} {r : ℕ → Set ℕ}

/-- Every reading of an approximator is true of the number itself, so the exact numeral entails
the approximated one. -/
theorem self_mem_approximator (hr : r ∈ ⟦approximator form⟧) (n : ℕ) : n ∈ r n := by
  obtain ⟨y, rfl⟩ := hr
  exact ⟨Nat.sub_le n y, Nat.le_add_right n y⟩

/-- No reading of *almost* or *nearly* is true of the number itself. -/
theorem self_not_mem_shortOf (hr : r ∈ ⟦shortOf form⟧) (n : ℕ) : n ∉ r n := by
  obtain ⟨y, rfl⟩ := hr
  exact fun h ↦ lt_irrefl n h.2

end English.NumeralModifiers
