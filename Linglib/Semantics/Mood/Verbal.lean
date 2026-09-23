/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Dynamic.UpdateSemantics.Necessity
public import Linglib.Semantics.Mood.State
public import Linglib.Semantics.Mood.Defs

/-!
# Verbal mood as component selection

This file defines the verbal-mood operators as selectors of a component of the embedding
attitude's state.

Verbal mood is the contrast between indicative and subjunctive in the complement clauses of
attitude verbs. On Portner's account it reduces to which component of the embedding attitude's
state the mood operator quantifies over. The Truth intuition of Farkas and of Portner's earlier
work and the Comparison intuition of Giorgi and Pianesi are both correct, because they target
different components. Universal quantification over the information component underwrites
selection of the Truth kind (`boxCs`), and quantification over the best-ranked subset
underwrites selection of the Comparison kind (`boxLe`). A third operator, for
question-embedding predicates such as *wonder* and *ask*, selects clauses settled by the open
question (`boxAns`). This operator is an addition of this library, since Portner's unification
is restricted to declarative complementation.

## Main declarations

* `VerbalOp`: the three operators, with `HasTarget` sending each to its component.
* `VerbalOp.interp`: interpretation as `boxOn ∘ target`.

## Main statements

* `indicative_ne_subjunctive`, `interrogative_ne_indicative`: the operators are pairwise
  distinguishable.
* `target_injective`: mood selection and component selection are in bijection at this layer.

## References

* [P. Portner, *Mood* (2018)][portner-2018]
* [D. F. Farkas, *Intensional Descriptions and the Romance Subjunctive Mood* (1985)][farkas-1985]
* [P. Portner, *The semantics of mood, complementation, and conversational force*
  (1997)][portner-1997]
* [A. Giorgi and F. Pianesi, *Tense and Aspect: From Semantics to Morphosyntax*
  (1997)][giorgi-pianesi-1997]
* [J. Groenendijk and M. Stokhof, *Studies on the Semantics of Questions and the Pragmatics of
  Answers* (1984)][groenendijk-stokhof-1984]
-/

@[expose] public section

namespace Mood

open UpdateSemantics.Default
open HasTarget (target)

variable {W : Type*}

/-- The three verbal-mood operators are Portner's `.indicative` and `.subjunctive`, together with
`.interrogative`, which this library adds. -/
inductive VerbalOp where
  /-- The indicative quantifies universally over the informational component (the Truth intuition).
  -/
  | indicative
  /-- The subjunctive quantifies over the best-ranked subset of the preferential component (the
  Comparison intuition). -/
  | subjunctive
  /-- The interrogative is answerhood with respect to the inquiry component, and is selected by
  question-embedding predicates. -/
  | interrogative
  deriving DecidableEq, Repr

/-- Each verbal mood targets one component of the state. -/
instance : HasTarget VerbalOp where
  target
    | .indicative    => .informational
    | .subjunctive   => .preferential
    | .interrogative => .inquisitive

@[simp] theorem target_indicative :
    target VerbalOp.indicative = .informational := rfl

@[simp] theorem target_subjunctive :
    target VerbalOp.subjunctive = .preferential := rfl

@[simp] theorem target_interrogative :
    target VerbalOp.interrogative = .inquisitive := rfl

/-- The interpretation of a verbal-mood operator against an embedding state and an embedded
proposition is the necessity modal of the operator's target. -/
def VerbalOp.interp (m : VerbalOp) : State W → (W → Prop) → Prop :=
  (target m).boxOn

/-! ### Definitional equalities -/

@[simp] theorem interp_indicative (c : State W) (p : W → Prop) :
    VerbalOp.indicative.interp c p = c.toExpState.boxCs p := rfl

@[simp] theorem interp_subjunctive (c : State W) (p : W → Prop) :
    VerbalOp.subjunctive.interp c p = c.toExpState.boxLe p := rfl

@[simp] theorem interp_interrogative (c : State W) (p : W → Prop) :
    VerbalOp.interrogative.interp c p = c.boxAns p := rfl

/-! ### Distinctness witnesses -/

/-- Total information over `Bool`, ordered so that `false`, the unique `sepProp`-world, is the
unique optimal world. -/
def sepState : ExpState Bool :=
  ⟨Set.univ, crit State.sepProp⟩

/-- `sepState` with trivial inquiry. -/
def sepStateTriv : State Bool := State.ofExpState sepState

theorem subjunctive_accepts_separation :
    VerbalOp.subjunctive.interp sepStateTriv State.sepProp := by
  intro w hw
  exact hw.2 (Set.mem_univ false) (fun _ ↦ rfl) rfl

theorem indicative_rejects_separation :
    ¬ VerbalOp.indicative.interp sepStateTriv State.sepProp := by
  intro h
  exact Bool.noConfusion (h true (Set.mem_univ true))

/-- The split between Truth and Comparison is genuine, since the two operators disagree on some
state and proposition. -/
theorem indicative_ne_subjunctive :
    ∃ (c : State Bool) (p : Bool → Prop),
      VerbalOp.subjunctive.interp c p ∧
      ¬ VerbalOp.indicative.interp c p :=
  ⟨sepStateTriv, State.sepProp,
    subjunctive_accepts_separation, indicative_rejects_separation⟩

/-- The interrogative operator is not the indicative one
(`State.boxAns_not_reducible_to_boxCs`). -/
theorem interrogative_ne_indicative :
    ∃ (c : State Bool) (p : Bool → Prop),
      VerbalOp.interrogative.interp c p ∧
      ¬ VerbalOp.indicative.interp c p :=
  State.boxAns_not_reducible_to_boxCs

/-- Verbal-mood targeting is injective, so mood selection and component selection are in bijection
at this layer. Portner states his Indicative and Subjunctive principles one way (a clause operated
on by the informational modal is indicative in form), with update-based variants through his
fixpoints, and the bijection here reflects only this three-element enumeration. -/
theorem target_injective :
    Function.Injective (target : VerbalOp → Component) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

end Mood
