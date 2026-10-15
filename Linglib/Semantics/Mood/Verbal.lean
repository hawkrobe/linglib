/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Mood.State

/-!
# Verbal mood as component selection

Verbal mood is the contrast between indicative and subjunctive in complement clauses. Portner's
synthesis states it as two principles (p. 235): a clause operated on by the informational modal
is indicative, and a clause operated on by the preference modal is subjunctive. Quantification
over the context set (`boxCs`) is the Truth intuition of Farkas and of Portner's earlier work,
and quantification over the best worlds (`boxLe`) the Comparison intuition of Giorgi and
Pianesi. Here each grammatical mood targets its component and is interpreted as that
component's modal.

Portner leaves question-embedding predicates open (p. 237): Italian *chiedere* takes the
indicative when it means 'ask' and the subjunctive when it means 'wonder'.

## Main definitions

* `Mood.Grammatical.interp`: a grammatical mood interpreted as the modal of its component.

## Main statements

* `Mood.Grammatical.indicative_ne_subjunctive`: the two moods disagree on some state.

## References

* [portner-2018]
* [farkas-1985]
* [portner-1997]
* [giorgi-pianesi-1997]
-/

@[expose] public section

namespace Mood

open DynamicSemantics
open HasTarget (target)

variable {W : Type*}

/-- The indicative targets the informational component and the subjunctive the preferential
one. -/
instance : HasTarget Grammatical where
  target
    | .indicative  => .informational
    | .subjunctive => .preferential

namespace Grammatical

@[simp] theorem target_indicative : target indicative = .informational := rfl

@[simp] theorem target_subjunctive : target subjunctive = .preferential := rfl

/-- A grammatical mood is interpreted as the necessity modal of its target. -/
def interp (m : Grammatical) : State W → (W → Prop) → Prop :=
  (target m).boxOn

@[simp] theorem interp_indicative (c : State W) (p : W → Prop) :
    indicative.interp c p = c.toExpState.boxCs p := rfl

@[simp] theorem interp_subjunctive (c : State W) (p : W → Prop) :
    subjunctive.interp c p = c.toExpState.boxLe p := rfl

/-- Every world is in the context set, and `false`, the one `sepProp`-world, is the one optimal
world. -/
def sepState : State Bool :=
  State.ofExpState ⟨Set.univ, ExpState.crit State.sepProp⟩

/-- The indicative and the subjunctive disagree on some state and proposition. -/
theorem indicative_ne_subjunctive :
    ∃ (c : State Bool) (p : Bool → Prop), subjunctive.interp c p ∧ ¬ indicative.interp c p :=
  ⟨sepState, State.sepProp, fun _ hw ↦ hw.2 (Set.mem_univ false) (fun _ ↦ rfl) rfl,
    fun h ↦ Bool.noConfusion (h true (Set.mem_univ true))⟩

/-- Targeting is injective. Portner states his principles from the modal to the form; the
injectivity here reflects only that two moods go to two components. -/
theorem target_injective : Function.Injective (target : Grammatical → Component) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

end Grammatical

end Mood
