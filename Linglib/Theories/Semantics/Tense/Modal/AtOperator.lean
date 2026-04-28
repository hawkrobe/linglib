import Linglib.Theories.Semantics.Tense.Aspect.Core

/-!
# The AT Relation
@cite{condoravdi-2002}

Temporal instantiation of eventuality predicates, dispatching on eventuality
sort. Events require temporal inclusion (τ(e) ⊆ t); states require temporal
overlap (τ(e) ∘ t). This distinction, due to @cite{kamp-rohrer-1983} and
@cite{partee-1984}, is the bridge between eventuality classification and
temporal operators (tense, aspect, modals).

## Key Definitions

- `atEvent` / `atState`: sort-specific instantiation at an interval
- `at'`: unified dispatch on `Dynamicity`
- `atEventForward` / `atStateForward` / `atForward`: instantiation in
  the future of a point — @cite{condoravdi-2002}'s `[t,_)` expansion

## Bridge to Klein's Aspect Operators

- `prfv_iff_atEvent`: PRFV and `atEvent` are definitionally equal
- `impf_implies_atState`: IMPF (proper inclusion) implies `atState` (overlap)
-/

namespace Semantics.Tense.Modal.AtOperator

open Core.Time
open Core.Verbs (Dynamicity)
open Semantics.Tense.Aspect.Core

variable {W Time : Type*} [LinearOrder Time]

/-! ## AT at an Interval -/

/-- Temporal instantiation of an eventive predicate at interval `t`:
    ∃e[P(w)(e) ∧ τ(e) ⊆ t]. Events must be fully contained in the
    reference interval. -/
def atEvent (P : EventPred W Time) (w : W) (t : Interval Time) : Prop :=
  ∃ e : Eventuality Time, P w e ∧ e.runtime.subinterval t

/-- Temporal instantiation of a stative predicate at interval `t`:
    ∃e[P(w)(e) ∧ τ(e) ∘ t]. States need only overlap the reference
    interval. -/
def atState (P : EventPred W Time) (w : W) (t : Interval Time) : Prop :=
  ∃ e : Eventuality Time, P w e ∧ e.runtime.overlaps t

/-- @cite{condoravdi-2002} [19]: unified AT relation dispatching on
    eventuality sort.

    `at' .dynamic P w t = atEvent P w t` (event ⊆ interval)
    `at' .stative P w t = atState P w t` (state ∘ interval) -/
def at' (sort : Dynamicity) (P : EventPred W Time) (w : W)
    (t : Interval Time) : Prop :=
  match sort with
  | .dynamic => atEvent P w t
  | .stative => atState P w t

@[simp] theorem at'_dynamic (P : EventPred W Time) (w : W)
    (t : Interval Time) : at' .dynamic P w t = atEvent P w t := rfl

@[simp] theorem at'_stative (P : EventPred W Time) (w : W)
    (t : Interval Time) : at' .stative P w t = atState P w t := rfl

/-- Eventive instantiation is stronger than stative: if the event is
    contained in the interval, it certainly overlaps it. -/
theorem atState_of_atEvent (P : EventPred W Time) (w : W)
    (t : Interval Time) (h : atEvent P w t) : atState P w t :=
  let ⟨e, hP, hSub⟩ := h
  ⟨e, hP, Interval.subinterval_overlaps hSub⟩

/-! ## AT with Forward Expansion -/

/-! @cite{condoravdi-2002} [22]–[23]: modals expand the evaluation time
    forward to `[t, _)` — the interval from `t` to the end of time.
    Since `Interval` requires finite bounds, we express the constraints
    directly: for events, the event starts at or after `t`; for states,
    the state persists at or past `t`. -/

/-- Event instantiated in the future of `t`: the event starts at or
    after `t`. Corresponds to AT([t,_), w, P) for eventive P. -/
def atEventForward (P : EventPred W Time) (w : W) (t : Time) : Prop :=
  ∃ e : Eventuality Time, P w e ∧ t ≤ e.runtime.start

/-- State instantiated through `t`: the state persists at or past `t`.
    Corresponds to AT([t,_), w, P) for stative P. -/
def atStateForward (P : EventPred W Time) (w : W) (t : Time) : Prop :=
  ∃ e : Eventuality Time, P w e ∧ t ≤ e.runtime.finish

/-- Forward AT, dispatching on sort. -/
def atForward (sort : Dynamicity) (P : EventPred W Time) (w : W)
    (t : Time) : Prop :=
  match sort with
  | .dynamic => atEventForward P w t
  | .stative => atStateForward P w t

@[simp] theorem atForward_dynamic (P : EventPred W Time) (w : W)
    (t : Time) : atForward .dynamic P w t = atEventForward P w t := rfl

@[simp] theorem atForward_stative (P : EventPred W Time) (w : W)
    (t : Time) : atForward .stative P w t = atStateForward P w t := rfl

/-- Forward stative is weaker than forward eventive: if the event starts
    at or after `t`, its finish is also at or after `t`. -/
theorem atStateForward_of_atEventForward (P : EventPred W Time) (w : W)
    (t : Time) (h : atEventForward P w t) : atStateForward P w t :=
  let ⟨e, hP, hStart⟩ := h
  ⟨e, hP, le_trans hStart e.runtime.valid⟩

/-! ## Bridge to Klein's Aspect Operators -/

/-- PRFV and `atEvent` check the same condition (conjunction is
    commuted). -/
theorem prfv_iff_atEvent (P : EventPred W Time) (w : W)
    (t : Interval Time) : PRFV P w t ↔ atEvent P w t :=
  ⟨λ ⟨e, hSub, hP⟩ => ⟨e, hP, hSub⟩, λ ⟨e, hP, hSub⟩ => ⟨e, hSub, hP⟩⟩

/-- IMPF implies `atState`: if the reference interval is properly
    contained in the event runtime (IMPF), then the event runtime
    certainly overlaps the reference interval. -/
theorem impf_implies_atState (P : EventPred W Time) (w : W)
    (t : Interval Time) (h : IMPF P w t) : atState P w t :=
  let ⟨e, hSub, hP⟩ := h
  ⟨e, hP, Interval.subinterval_overlaps (Interval.properSubinterval_implies_subinterval _ _ hSub)
    |> Interval.overlaps_symm⟩

/-! ## Monotonicity -/

/-- `atEvent` is monotone in the reference interval: if a larger interval
    contains the smaller, eventive instantiation at the smaller implies
    instantiation at the larger. -/
theorem atEvent_mono {t₁ t₂ : Interval Time}
    (P : EventPred W Time) (w : W)
    (hSub : t₁.subinterval t₂) (h : atEvent P w t₁) : atEvent P w t₂ :=
  let ⟨e, hP, heSub⟩ := h
  ⟨e, hP, ⟨le_trans hSub.1 heSub.1, le_trans heSub.2 hSub.2⟩⟩

/-- `atEvent` at a point `[t,t]` implies `atEventForward` at `t`:
    if an event is instantiated at time `t`, it starts at or after `t`. -/
theorem atEventForward_of_atEvent_point (P : EventPred W Time) (w : W)
    (t : Time) (h : atEvent P w (Interval.point t)) : atEventForward P w t :=
  let ⟨e, hP, hSub⟩ := h
  ⟨e, hP, hSub.1⟩

/-- `atState` at a point `[t,t]` implies `atStateForward` at `t`:
    if a state overlaps time `t`, it persists at or past `t`. -/
theorem atStateForward_of_atState_point (P : EventPred W Time) (w : W)
    (t : Time) (h : atState P w (Interval.point t)) : atStateForward P w t :=
  let ⟨e, hP, hOv⟩ := h
  ⟨e, hP, hOv.2⟩

end Semantics.Tense.Modal.AtOperator
