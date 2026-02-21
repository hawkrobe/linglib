import Mathlib.Order.Basic
import Linglib.Tactics.OntSort

/-!
# Situation (World × Time)

The most basic composed type in linglib: a world–time pair serving as the
evaluation point for intensional semantics (Kratzer 1989, 2021).

Composes two ontological primitives — worlds (`W : Type*`) and times
(`Time : Type*`) — which are type parameters throughout linglib, not
concrete types.

This file is a root of linglib's import DAG. `Core/Time.lean` imports it
and adds temporal infrastructure (intervals, temporal relations); downstream
modules use `Situation` for tense semantics, event semantics, dynamic
semantics, and situation-dependent attitudes.

## References

- Kratzer, A. (1989). An investigation of the lumps of thought.
- Kratzer, A. (2021). Situations in natural language semantics. SEP.
-/

namespace Core

/--
A situation is a part of a world at a time.

Following Kratzer's situation semantics:
- Situations are "slices" of possible worlds
- They have both spatial and temporal extent
- They can be minimal witnesses for propositions

We model situations as world–time pairs, abstracting from spatial extent.
This is the most basic composition of ontological primitives.
-/
@[ont_sort] structure Situation (W Time : Type*) where
  /-- The world this situation is part of -/
  world : W
  /-- The temporal coordinate of the situation -/
  time : Time
  deriving Repr

namespace Situation

variable {W Time : Type*}

/-- Temporal trace: extract the time of a situation -/
@[simp]
def τ (s : Situation W Time) : Time := s.time

/-- World of a situation -/
@[simp]
def w (s : Situation W Time) : W := s.world

/-- Create a situation from world and time -/
def mk' (world : W) (time : Time) : Situation W Time :=
  { world := world, time := time }

/-- Situations at the same world -/
def sameWorld (s₁ s₂ : Situation W Time) : Prop :=
  s₁.world = s₂.world

/-- Situations at the same time -/
def sameTime (s₁ s₂ : Situation W Time) : Prop :=
  s₁.time = s₂.time

/-- s₁ temporally precedes s₂ -/
def before [LT Time] (s₁ s₂ : Situation W Time) : Prop :=
  s₁.time < s₂.time

/-- s₁ temporally follows s₂ -/
def after [LT Time] (s₁ s₂ : Situation W Time) : Prop :=
  s₁.time > s₂.time

/-- s₁ is contemporaneous with s₂ -/
def contemporaneous (s₁ s₂ : Situation W Time) : Prop :=
  s₁.time = s₂.time

end Situation

end Core
