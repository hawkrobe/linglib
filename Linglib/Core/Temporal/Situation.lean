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

end Core
