/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Exhaustification over entailment chains

Scalar alternatives typically form an *entailment chain*: a family `φ : ι → W → Prop` over an
ordered index, antitone in the index, so that a higher index is a stronger alternative.
Exhaustifying a prejacent `φ i` against all stronger alternatives (`exhChain`) then collapses to
negating the single next-stronger alternative when one exists (`exhChain_iff_succ`). On a dense
scale with no next alternative, exhaustification cannot be satisfied at all
(`exhChain_not_of_dense`), the Universal Density of Measurement crash of [fox-hackl-2006]. When
the alternatives are the lower bounds `j ≤ ·` of a partial order, exhaustifying the `i`th pins
the value at `i` (`exhChain_le_iff`): *some* against *all* is *some but not all*, and a
lower-bounded numeral its exact reading.

The two halves of the case split, whether a next-stronger alternative exists, are instantiated
across the numeral literature: `Numerals.exhNumeral`, the exact reading as the step-1 instance on
ℕ ([horn-1972]); granularity-`g` scalar alternatives in both bound directions
(`Studies/Mihoc2019`); the dense crash (`Studies/FoxHackl2006`); and the grain-size-indexed
precisification families of approximative *just* ([thomas-deo-2020]).

## Main definitions

* `exhChain`: assert the prejacent and negate every strictly stronger alternative of the chain.

## Main results

* `exhChain_iff_succ`: on a chain, exhaustification negates the next-stronger alternative.
* `exhChain_not_of_dense`: with no next-stronger alternative, exhaustification is unsatisfiable.
* `exhChain_le_iff`: exhaustifying a lower bound against the stronger ones asserts equality.

## References

* [horn-1972]
* [fox-2007]
* [fox-hackl-2006]
* [chierchia-2013]
* [thomas-deo-2020]
-/

@[expose] public section

namespace Exhaustification

variable {ι W : Type*} [Preorder ι] {φ : ι → W → Prop} {i s : ι} {w : W}

/-- Exhaustifying the prejacent `φ i` against all strictly stronger alternatives of the family
asserts `φ i` and negates `φ j` for every `j > i`. -/
def exhChain (φ : ι → W → Prop) (i : ι) (w : W) : Prop :=
  φ i w ∧ ∀ j, i < j → ¬ φ j w

instance [DecidableEq ι] [Fintype ι] [DecidableLT ι]
    [∀ j, Decidable (φ j w)] : Decidable (exhChain φ i w) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _ → _))

/-- On an entailment chain, where higher alternatives entail lower ones, exhaustifying `φ i`
negates just the next-stronger alternative `φ s`, the one indexed above `i` and below every other
index above `i`. -/
theorem exhChain_iff_succ (hanti : ∀ ⦃j k : ι⦄, j ≤ k → ∀ w, φ k w → φ j w)
    (his : i < s) (hleast : ∀ j, i < j → s ≤ j) :
    exhChain φ i w ↔ φ i w ∧ ¬ φ s w :=
  ⟨fun ⟨hp, hstr⟩ ↦ ⟨hp, hstr s his⟩,
   fun ⟨hp, hs⟩ ↦ ⟨hp, fun j hj hφj ↦ hs (hanti (hleast j hj) w hφj)⟩⟩

/-- Exhaustification is unsatisfiable when every world verifying the prejacent verifies some
strictly stronger alternative, as on a dense scale. -/
theorem exhChain_not_of_dense (hdense : ∀ w, φ i w → ∃ j, i < j ∧ φ j w) :
    ¬ exhChain φ i w := fun ⟨hp, hstr⟩ ↦
  let ⟨j, hij, hφj⟩ := hdense w hp
  hstr j hij hφj

/-- Exhaustifying the lower bound `i ≤ ·` against every stronger lower bound asserts `· = i`. -/
theorem exhChain_le_iff {ι : Type*} [PartialOrder ι] {i w : ι} :
    exhChain (· ≤ ·) i w ↔ w = i :=
  ⟨fun ⟨hi, hs⟩ ↦ (hi.lt_or_eq.resolve_left fun h ↦ hs w h le_rfl).symm,
    fun h ↦ h ▸ ⟨le_rfl, fun _ hj hle ↦ hj.not_ge hle⟩⟩

end Exhaustification
