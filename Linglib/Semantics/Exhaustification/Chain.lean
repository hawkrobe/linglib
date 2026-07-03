/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Exhaustification over entailment chains
[horn-1972] [fox-2007] [fox-hackl-2006] [chierchia-2013]

Scalar alternatives typically form an *entailment chain*: a family
`φ : ι → W → Prop` over an ordered index, antitone in the index (higher
index = stronger alternative). Exhaustifying a prejacent `φ i` against all
stronger alternatives (`exhChain`) then collapses to negating the single
*next-stronger* alternative, when one exists (`exhChain_iff_succ`); on a
dense scale with no next alternative, exhaustification cannot be satisfied
at all (`exhChain_not_of_dense` — [fox-hackl-2006]'s Universal Density of
Measurement crash).

The two lemmas are the two halves of one case split — does a next-stronger
alternative exist? — instantiated across the numeral literature:
`Semantics.Numerals.exhNumeral` (Horn's 'exactly', the step-1 instance on
ℕ), granularity-`g` scalar alternatives in both bound directions
(`Studies/Mihoc2019`), the dense crash (`Studies/FoxHackl2006Numerals`),
and grain-size-indexed precisification families ([thomas-deo-2020]'s
approximative *just*).

## Main definitions

- `exhChain`: assert the prejacent, negate every strictly stronger
  alternative of the chain

## Main results

- `exhChain_iff_succ`: on a chain, exhaustification = negating the
  next-stronger alternative
- `exhChain_not_of_dense`: with no next-stronger alternative,
  exhaustification is unsatisfiable
-/

namespace Exhaustification

variable {ι W : Type*} [Preorder ι] {φ : ι → W → Prop} {i s : ι} {w : W}

/-- Exhaustification of the prejacent `φ i` against all strictly stronger
alternatives of the family: assert `φ i`, negate `φ j` for every `j > i`. -/
def exhChain (φ : ι → W → Prop) (i : ι) (w : W) : Prop :=
  φ i w ∧ ∀ j, i < j → ¬ φ j w

instance [DecidableEq ι] [Fintype ι] [DecidableLT ι]
    [∀ j, Decidable (φ j w)] : Decidable (exhChain φ i w) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _ → _))

/-- On an entailment chain — the family is antitone, so higher alternatives
entail lower ones — exhaustification collapses to negating the
*next-stronger* alternative: if `s` lies above `i` and below every other
index above `i`, then negating `φ s` negates the whole upper set. -/
theorem exhChain_iff_succ (hanti : ∀ ⦃j k : ι⦄, j ≤ k → ∀ w, φ k w → φ j w)
    (his : i < s) (hleast : ∀ j, i < j → s ≤ j) :
    exhChain φ i w ↔ φ i w ∧ ¬ φ s w :=
  ⟨fun ⟨hp, hstr⟩ => ⟨hp, hstr s his⟩,
   fun ⟨hp, hs⟩ => ⟨hp, fun j hj hφj => hs (hanti (hleast j hj) w hφj)⟩⟩

/-- If every world verifying the prejacent verifies some strictly stronger
alternative — as on a dense scale — chain-exhaustification is
unsatisfiable: the [fox-hackl-2006] density crash. -/
theorem exhChain_not_of_dense (hdense : ∀ w, φ i w → ∃ j, i < j ∧ φ j w) :
    ¬ exhChain φ i w := fun ⟨hp, hstr⟩ =>
  let ⟨j, hij, hφj⟩ := hdense w hp
  hstr j hij hφj

end Exhaustification
