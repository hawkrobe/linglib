/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Direction (Left / Right)

A two-element enumeration for the orientation of a subregular transducer's
scan: `Subsequential.lean` and `ISL.lean` parameterise their classification
predicates over `Direction` (left-to-right vs right-to-left). Kept as its own
file, co-located with those consumers, so the two share one inductive type
rather than duplicating the case names.

The type sits in `namespace Core`, so consumers `open Core` (or qualify) and
use `Direction.left` / `Direction.right` directly. Reused outside the
transducer setting where the same left-vs-right notion is needed (e.g.
`Phonology/Subregular/TierRule.lean` aliases `Side := Direction` for the
context side of a tier rule); the underlying type must be this one.
-/

namespace Core

/-- A left-vs-right enumeration. -/
inductive Direction
  | left
  | right
  deriving DecidableEq, Repr

namespace Direction

/-- Flip a direction: `left ↔ right`. -/
def flip : Direction → Direction
  | .left => .right
  | .right => .left

@[simp] theorem flip_flip : ∀ d : Direction, d.flip.flip = d
  | .left | .right => rfl

@[simp] theorem flip_left : Direction.flip .left = .right := rfl
@[simp] theorem flip_right : Direction.flip .right = .left := rfl

end Direction

end Core
