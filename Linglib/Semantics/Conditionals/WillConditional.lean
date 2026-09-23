/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Modality.Selectional

/-!
# Selectional *will*-conditionals

This file defines the *will*-conditionals of [cariani-santorio-2018]. An *if*-clause restricts
the modal parameter of the selectional *will* to the antecedent-worlds among its possibilities,
so *if A, will B* is true when `B` holds at the world selected from that restricted parameter.
Because the selected world is single, the conditional validates Conditional Excluded Middle and
commutes with negation whether negation takes narrow or wide scope, where the universal
quantification of a Lewisian conditional validates neither.

## Main definitions

* `WillConditional.willConditional`: the selectional *will*-conditional.
* `WillConditional.universalWillConditional`: the universal foil.
* `WillConditional.subordinatedWillDiscourse`: a modally subordinated *will*-discourse.

## Implementation notes

Section and equation numbers follow the preprint of [cariani-santorio-2018].

## References

* [F. Cariani and P. Santorio, *Will done Better: Selection Semantics, Future Credence, and
  Indeterminacy* (2018)][cariani-santorio-2018]
* [D. Lewis, *Counterfactuals* (1973)][lewis-1973]
-/

@[expose] public section


namespace Conditional.WillConditional

open _root_.Conditional (SelectionFunction)
open Modality.Selectional

variable {W : Type*}

/-- The restriction of the modal parameter `f` to the worlds satisfying the antecedent `A`
([cariani-santorio-2018] §5.3.1, (21)). -/
def restrict (A : W → Prop) (f : Set W) : Set W :=
  f ∩ {w' | A w'}

/-- The selectional *will*-conditional, which evaluates the prejacent `B` at the world selected
from the modal parameter restricted to the antecedent ([cariani-santorio-2018] §5.3.1). -/
def willConditional (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) : Prop :=
  willSem s B (restrict A f) w

@[simp] theorem willConditional_def (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) :
    willConditional s A B f w ↔ B (s.sel w (f ∩ {w' | A w'})) := Iff.rfl

/-- *If A, will B* or *if A, will not B* holds at every point, since the selected world is single
whatever the antecedent restricts the parameter to ([cariani-santorio-2018] §7). -/
theorem compositional_CEM (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) :
    willConditional s A B f w ∨
    willConditional s A (fun w' ↦ ¬ B w') f w :=
  em _

/-- Compositional Conditional Excluded Middle is valid₂. -/
theorem valid2_compositional_CEM (A B : W → Prop) :
    Valid2 (W := W) fun s f w ↦
      willConditional s A B f w ∨
      willConditional s A (fun w' ↦ ¬ B w') f w :=
  fun s f w ↦ compositional_CEM s A B f w

/-- With negation under the *if*-clause, *if A, will not B* is equivalent to the negation of
*if A, will B* ([cariani-santorio-2018] §7). -/
theorem narrow_negation_swap (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) :
    willConditional s A (fun w' ↦ ¬ B w') f w ↔
    ¬ willConditional s A B f w :=
  Iff.rfl

/-- Narrow Negation Swap is valid₂. -/
theorem valid2_narrow_negation_swap (A B : W → Prop) :
    Valid2 (W := W) fun s f w ↦
      willConditional s A (fun w' ↦ ¬ B w') f w ↔
      ¬ willConditional s A B f w :=
  fun s f w ↦ narrow_negation_swap s A B f w

/-- With negation over the whole conditional, the negation of *if A, will B* is equivalent to
*if A, will not B*. In the selectional setting both scopes reduce to the same truth condition
([cariani-santorio-2018] §7). -/
theorem wide_negation_swap (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) :
    ¬ willConditional s A B f w ↔
    willConditional s A (fun w' ↦ ¬ B w') f w :=
  (narrow_negation_swap s A B f w).symm

/-- Wide Negation Swap is valid₂. -/
theorem valid2_wide_negation_swap (A B : W → Prop) :
    Valid2 (W := W) fun s f w ↦
      ¬ willConditional s A B f w ↔
      willConditional s A (fun w' ↦ ¬ B w') f w :=
  fun s f w ↦ wide_negation_swap s A B f w

/-- Compositional Conditional Excluded Middle at a context of utterance. Under a single selection
function the postsemantic and compositional readings coincide, which the supervaluational
generalization of [cariani-santorio-2018] separates. -/
theorem postsemantic_CEM (A B : W → Prop) (sCtx : SelectionFunction W)
    (fCtx : Set W) (wCtx : W) :
    Valid1 (W := W)
      (fun s f w ↦
        willConditional s A B f w ∨
        willConditional s A (fun w' ↦ ¬ B w') f w)
      sCtx fCtx wCtx :=
  valid2_implies_valid1
    (fun s f w ↦ compositional_CEM s A B f w) sCtx fCtx wCtx

/-- When the evaluation world is in the modal parameter and satisfies the antecedent, the
conditional reduces by centering to its consequent at that world. -/
theorem willConditional_collapse (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) (hw_f : w ∈ f) (hw_A : A w) :
    willConditional s A B f w ↔ B w :=
  unembedded_collapse s B (restrict A f) w ⟨hw_f, hw_A⟩

/-- When every world of the modal parameter satisfies the antecedent, the *if*-clause changes
nothing and *if A, will B* is equivalent to *will B*. -/
theorem willConditional_redundant (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) (h_subset : ∀ w' ∈ f, A w') :
    willConditional s A B f w ↔ willSem s B f w := by
  have h_eq : restrict A f = f := by
    ext w'
    exact ⟨fun ⟨hf, _⟩ ↦ hf, fun hf ↦ ⟨hf, h_subset w' hf⟩⟩
  unfold willConditional
  rw [h_eq]

/-! ### The universal foil

The universal reading lifts to conditionals by the same restriction of the modal parameter but
quantifies over the restricted parameter instead of evaluating at the selected world, the
conditional image of `Selectional.universalWill`. It falsifies Compositional Conditional Excluded
Middle when the restricted parameter contains both a `B`-world and a `¬B`-world. -/

/-- The universal foil to the *will*-conditional, which restricts the parameter to the antecedent
and quantifies universally over it. It validates neither Compositional Conditional Excluded
Middle nor Negation Swap. -/
def universalWillConditional (A B : W → Prop) (f : Set W) (w : W) : Prop :=
  universalWill B (restrict A f) w

/-! ### Modal subordination

[cariani-santorio-2018] treat modal subordination in *If A, will B. Will C.* by coindexing the
second *will* with the parameter the *if*-clause restricts, a discourse assumption rather than
something the semantics forces. Both prejacents are then evaluated at the same selected world. -/

/-- The modally subordinated discourse *If A, will B. Will C.*, whose second *will* is coindexed
with the parameter the *if*-clause restricts ([cariani-santorio-2018] §5.3.1). -/
def subordinatedWillDiscourse (s : SelectionFunction W) (A B C : W → Prop)
    (f : Set W) (w : W) : Prop :=
  willConditional s A B f w ∧
  willSem s C (restrict A f) w

/-- A subordinated discourse evaluates both prejacents at the same selected world. -/
theorem subordinatedWillDiscourse_eq_conj (s : SelectionFunction W)
    (A B C : W → Prop) (f : Set W) (w : W) :
    subordinatedWillDiscourse s A B C f w ↔
    (B (s.sel w (f ∩ {w' | A w'})) ∧ C (s.sel w (f ∩ {w' | A w'}))) :=
  Iff.rfl

/-- The subordinated continuation agrees with an unrestricted *will C* when restricting by the
antecedent leaves the selected world fixed. -/
theorem subordinated_eq_unrestricted_of_no_shift (s : SelectionFunction W)
    (A B C : W → Prop) (f : Set W) (w : W)
    (h_no_shift : s.sel w f = s.sel w (restrict A f)) :
    subordinatedWillDiscourse s A B C f w ↔
    (willConditional s A B f w ∧ willSem s C f w) := by
  unfold subordinatedWillDiscourse willConditional willSem
  rw [h_no_shift]

end Conditional.WillConditional
