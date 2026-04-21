import Mathlib.Tactic.TypeStar
import Linglib.Tactics.OntSort

/-!
# Situations

@cite{kratzer-1989}

A situation is a part of a world at a time — a "slice" of a possible world
with both spatial and temporal extent. We model it as a world-time pair,
abstracting from spatial extent. Situations are the foundational
context-of-evaluation type used throughout intensional, dynamic, modal,
and tense semantics.
-/

namespace Core

/-- A situation is a part of a world at a time.

    Following @cite{kratzer-1989}'s situation semantics: situations are
    "slices" of possible worlds with both spatial and temporal extent,
    and can be minimal witnesses for propositions. We model them as
    world-time pairs, abstracting from spatial extent. -/
@[ont_sort] structure Situation (W Time : Type*) where
  /-- The world this situation is part of -/
  world : W
  /-- The temporal coordinate of the situation -/
  time : Time
  deriving Repr

end Core
