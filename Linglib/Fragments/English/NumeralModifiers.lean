import Linglib.Semantics.Denotation
import Linglib.Semantics.Quantification.Numerals.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# English numeral modifiers

This file records the English expressions that combine with a numeral to bound, fix or
approximate the amount it names. The modifiers that set a bound are built on four
constructions in Nouwen's survey: the comparatives *more than* and *fewer than*, the
superlatives *at least* and *at most*, the locative prepositions *over* and *under* and the
directional prepositions *up to* and *from*, beside the adverbs *minimally* and *maximally*.
*Exactly* and *precisely* fix the amount, *about*, *around*, *approximately* and *roughly*
place it near the numeral, and *almost* and *nearly* place it near the numeral and short of it.

A modifier denotes the set of readings the literature makes available for it, each a map from
the number to the set of amounts that verify the modified numeral. A bound-setting modifier
and an exactifier have the one reading of the comparison they express, an interval of
`Degree.Comparison.interval`, so a modifier of one class and its counterpart of the other
differ in whether the interval keeps the number. An approximator has a reading for each value
of a tolerance the context supplies: Égré, Spector, Mortier and Verheyen give *around n* the
amounts within the tolerance of `n` on either side, and on Penka's analysis *almost n* is false
of `n` and true of an amount close below it. Nouwen's two classes of modifier are derived from
the kind of construction, not stored.

## Main definitions

* `English.NumeralModifiers.NumeralModifier`: the carrier of the modifiers, with its lexical
  data `NumeralModifier.form` and `NumeralModifier.kind`.
* `English.NumeralModifiers.NumeralModifier.modifierClass`: the class of a bound-setting
  modifier, read off its kind.
* The `Denotes` instance gives each modifier its available readings.

## Main results

* `English.NumeralModifiers.NumeralModifier.self_mem_of_isApproximator`: every reading of
  *about*, *around*, *approximately* and *roughly* is true of the number itself, so the
  approximated numeral is entailed by the exact one.
* `English.NumeralModifiers.NumeralModifier.self_not_mem_almost`: no reading of *almost* or
  *nearly* is true of the number itself.

## Implementation notes

The amounts are natural numbers, as in `Semantics/Quantification/Numerals/Basic.lean`, and
truncated subtraction keeps the lower end of a tolerance interval at zero. *Between … and …*
takes two numerals and is not in the carrier.

## TODO

Blok argues that *up to n* asserts only a lower bound and implicates its upper bound, which is
why it is odd with the lowest number of a scale and does not license negative polarity items.
The reading recorded here is the upper bound alone, which *up to* shares with *at most*; the
split between asserted and implicated content is not represented.

## References

* [R. Nouwen, *Two kinds of modified numerals* (2010)][nouwen-2010]
* [C. Kennedy, *A "de-Fregean" semantics (and neo-Gricean pragmatics) for modified and
  unmodified numerals* (2015)][kennedy-2015]
* [D. Blok, *The semantics and pragmatics of directional numeral modifiers* (2015)][blok-2015]
* [P. Égré, B. Spector, A. Mortier and S. Verheyen, *On the Optimality of Vagueness: "Around",
  "Between" and the Gricean Maxims* (2023)][egre-etal-2023]
* [D. Penka, *"Almost there": The meaning of almost* (2006)][penka-2006]
-/

namespace English.NumeralModifiers

open Degree Numerals Semantics

/-- The numeral modifiers of English. -/
inductive NumeralModifier where
  | moreThan | fewerThan | over | under
  | atLeast | atMost | minimally | maximally | upTo | from_
  | exactly | precisely
  | about | around | approximately | roughly
  | almost | nearly
  deriving DecidableEq, Repr, Fintype

namespace NumeralModifier

/-- The surface form. -/
def form : NumeralModifier → String
  | .moreThan => "more than"
  | .fewerThan => "fewer than"
  | .over => "over"
  | .under => "under"
  | .atLeast => "at least"
  | .atMost => "at most"
  | .minimally => "minimally"
  | .maximally => "maximally"
  | .upTo => "up to"
  | .from_ => "from"
  | .exactly => "exactly"
  | .precisely => "precisely"
  | .about => "about"
  | .around => "around"
  | .approximately => "approximately"
  | .roughly => "roughly"
  | .almost => "almost"
  | .nearly => "nearly"

/-- The construction a bound-setting modifier is built on, `none` for the exactifiers and the
approximators, which [nouwen-2010]'s survey does not cover. -/
def kind : NumeralModifier → Option ModifierKind
  | .moreThan | .fewerThan => some .comparative
  | .over | .under => some .locative
  | .atLeast | .atMost => some .superlative
  | .minimally | .maximally => some .adverbial
  | .upTo | .from_ => some .directional
  | _ => none

/-- The class of a bound-setting modifier in the sense of [nouwen-2010], read off its kind. -/
def modifierClass (w : NumeralModifier) : Option ModifierClass := w.kind.map (·.modifierClass)

/-- The approximators place the amount within a tolerance of the number. -/
def IsApproximator (w : NumeralModifier) : Prop :=
  w = .about ∨ w = .around ∨ w = .approximately ∨ w = .roughly

instance : DecidablePred IsApproximator := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-! ### The available readings -/

/-- The readings the literature makes available for a modifier, each a map from the number to
the amounts verifying the modified numeral. A bound-setting modifier and an exactifier have the
interval of their comparison. An approximator has the amounts within `y` of the number, one
reading for each tolerance `y` ([egre-etal-2023]), and *almost* and *nearly* the amounts within
`y` below the number and short of it ([penka-2006]). -/
instance : Denotes NumeralModifier (Set (ℕ → Set ℕ)) where
  denote
    | .moreThan | .over => {Comparison.gt.interval}
    | .fewerThan | .under => {Comparison.lt.interval}
    | .atLeast | .minimally | .from_ => {Comparison.ge.interval}
    | .atMost | .maximally | .upTo => {Comparison.le.interval}
    | .exactly | .precisely => {Comparison.eq.interval}
    | .about | .around | .approximately | .roughly =>
        Set.range fun y n ↦ Set.Icc (n - y) (n + y)
    | .almost | .nearly => Set.range fun y n ↦ Set.Ico (n - y) n

variable {w : NumeralModifier} {r : ℕ → Set ℕ}

/-- Every reading of an approximator is true of the number itself, so the exact numeral entails
the approximated one. -/
theorem self_mem_of_isApproximator (hw : w.IsApproximator) (hr : r ∈ ⟦w⟧) (n : ℕ) : n ∈ r n := by
  rcases hw with rfl | rfl | rfl | rfl <;> obtain ⟨y, rfl⟩ := hr <;>
    exact ⟨Nat.sub_le n y, Nat.le_add_right n y⟩

/-- No reading of *almost* or *nearly* is true of the number itself. -/
theorem self_not_mem_almost (hw : w = .almost ∨ w = .nearly) (hr : r ∈ ⟦w⟧) (n : ℕ) :
    n ∉ r n := by
  rcases hw with rfl | rfl <;> obtain ⟨y, rfl⟩ := hr <;> exact fun h ↦ lt_irrefl n h.2

end NumeralModifier

end English.NumeralModifiers
