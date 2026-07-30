/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Nat

/-!
# Scan direction

The orientation of a left-to-right vs right-to-left scan, shared by the transducer
machines and the side-determinacy predicates of the subregular function theory, with
the window of positions a direction cuts around a target coordinate. Extracted to its
own leaf so the footprint-predicate file (`Dependence.lean`) does not have to depend on
the transducer machine file just to name a `left`/`right` tag.
-/

namespace Subregular

/-- The orientation of an FST scan: `left` consumes input head-first, `right`
tail-first (via `List.reverse` conjugation). The two scan modes give rise to
distinct function classes — isomorphic under reversal but not equal as
subclasses of the rational functions over un-reversed strings. -/
inductive Direction
  | left
  | right
  deriving DecidableEq, Repr

/-- The input positions not `d`-far from target `i` on side `s`. -/
def Direction.window : Direction → ℕ → ℕ → Set ℕ
  | .left, i, d => Set.Ici (i - d)
  | .right, i, d => Set.Iic (i + d)

@[simp, grind =] theorem Direction.window_left {i d : ℕ} :
    Direction.left.window i d = Set.Ici (i - d) := rfl

@[simp, grind =] theorem Direction.window_right {i d : ℕ} :
    Direction.right.window i d = Set.Iic (i + d) := rfl

end Subregular
