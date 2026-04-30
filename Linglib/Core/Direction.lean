/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Direction (Left / Right)

A two-element enumeration shared across phonology and computability
substrates that need a notion of left-vs-right (FST scan direction,
context side, harmony spread direction, etc.). Promoted to `Core/` so
that `Theories/Phonology/Process/Alternation.lean::Side` and
`Core/Computability/Subregular/Function/Subsequential.lean::Direction`
do not duplicate the same inductive type with the same case names.

Consumers should `open Core` (or qualify) and use `Direction.left` /
`Direction.right` directly. Phonology-side aliases `Side := Direction`
are acceptable when the `Side` name reads more naturally for the local
context (e.g., "context side" of a tier rule), but the underlying type
must be this one.
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
