/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Dynamic.UpdateSemantics.Necessity
import Linglib.Semantics.Mood.State
import Linglib.Semantics.Mood.Defs

/-!
# Verbal mood as component selection

Verbal mood — the indicative/subjunctive contrast in the complement
clauses of attitude verbs — reduces, on [portner-2018]'s account
(Ch. 2), to which component of the embedding attitude's state the
mood operator quantifies over. His unification: the *Truth* intuition
([farkas-1985], [portner-1997]) and the *Comparison* intuition
([giorgi-pianesi-1997]) are both correct because they target
different components — universal quantification over the information
component underwrites Truth-style selection (`boxCs`), and
quantification over the best-ranked subset underwrites
Comparison-style selection (`boxLe`). A third operator for
question-embedding predicates (*wonder*, *ask*) selects for clauses
settled by the open question (`boxAns`) — this library's extension;
Portner's unification proper is restricted to declarative
complementation.

## Main declarations

* `VerbalOp` — the three operators, with `HasTarget` sending each to
  its component.
* `VerbalOp.interp` — interpretation as `boxOn ∘ target`.
* `Selector.toVerbalOp` — the bridge from predicate-class selection.

## Main statements

* `indicative_ne_subjunctive`, `interrogative_ne_indicative` — the
  operators are pairwise distinguishable.
* `target_injective` — mood selection and component selection are in
  bijection at this layer.
-/

namespace Mood

open Semantics.Dynamic.Default
open HasTarget (target)

variable {W : Type*}

/-- The three verbal-mood operators; `.indicative` and `.subjunctive`
are [portner-2018]'s, `.interrogative` this library's extension. -/
inductive VerbalOp where
  /-- Universal quantification over the informational component — the
      Truth intuition. -/
  | indicative
  /-- Quantification over the preferential component's best-ranked
      subset — the Comparison intuition. -/
  | subjunctive
  /-- Answerhood with respect to the inquiry component
      ([groenendijk-stokhof-1984]); selected by question-embedding
      predicates. -/
  | interrogative
  deriving DecidableEq, Repr

/-- Verbal-mood targets ([portner-2018], Ch. 2). -/
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

/-- Interpretation of a verbal-mood operator against an embedding
state and an embedded proposition: the necessity modal of the
operator's target. -/
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

/-- Total information over `Bool`, ordered so that `false` — the
unique `sepProp`-world — is the unique optimal world. -/
def sepState : ExpState Bool :=
  ⟨Set.univ, Core.Order.Normality.crit State.sepProp⟩

/-- `sepState` with trivial inquiry. -/
def sepStateTriv : State Bool := State.ofExpState sepState

theorem subjunctive_accepts_separation :
    VerbalOp.subjunctive.interp sepStateTriv State.sepProp := by
  intro w hw
  exact hw.2 (Set.mem_univ false) (fun _ => rfl) rfl

theorem indicative_rejects_separation :
    ¬ VerbalOp.indicative.interp sepStateTriv State.sepProp := by
  intro h
  exact Bool.noConfusion (h true (Set.mem_univ true))

/-- The Truth/Comparison split is genuine: the two operators
disagree on some state and proposition. -/
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

/-- Verbal-mood targeting is injective: mood selection and component
selection are in bijection at this layer. [portner-2018] states his
Indicative and Subjunctive principles one-way ("if a clause is
operated on by the informational modal, its form is indicative"),
with update-based variants via his (11) fixpoints; the bijection here
reflects only this three-element enum. -/
theorem target_injective :
    Function.Injective (target : VerbalOp → Component) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-! ### Bridge to `Selector` -/

/-- The verbal-mood operator a predicate class selects, when the class
is committed to a single mood cross-linguistically; variable and
mood-neutral classes project to `none`. `Selector` covers
declarative-complement embedders only, so `.interrogative` is not in
its image. -/
def Selector.toVerbalOp : Selector → Option VerbalOp
  | .indicativeSelecting          => some .indicative
  | .subjunctiveSelecting         => some .subjunctive
  | .crossLinguisticallyVariable  => none
  | .moodNeutral                  => none

end Mood
