/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Nat

/-!
# Scan direction

The orientation of a left-to-right vs right-to-left scan, shared by the transducer
machines and the side-determinacy predicates of the subregular function theory, with
the window of positions a direction cuts around a target coordinate, and the reverse
conjugation `revConj` realizing the flip on string functions. Extracted to its own
leaf so the footprint-predicate file (`Dependence.lean`) does not have to depend on
the transducer machine file just to name a `left`/`right` tag.
-/

/-- The orientation of an FST scan: `left` consumes input head-first, `right`
tail-first (via `List.reverse` conjugation). The two scan modes give rise to
distinct function classes — isomorphic under reversal but not equal as
subclasses of the rational functions over un-reversed strings. -/
inductive ScanDirection
  | left
  | right
  deriving DecidableEq, Repr

/-- The input positions not `d`-far from target `i` on side `s`. -/
def ScanDirection.window : ScanDirection → ℕ → ℕ → Set ℕ
  | .left, i, d => Set.Ici (i - d)
  | .right, i, d => Set.Iic (i + d)

@[simp, grind =] theorem ScanDirection.window_left {i d : ℕ} :
    ScanDirection.left.window i d = Set.Ici (i - d) := rfl

@[simp, grind =] theorem ScanDirection.window_right {i d : ℕ} :
    ScanDirection.right.window i d = Set.Iic (i + d) := rfl

/-! ### Reverse conjugation

The action of flipping scan direction on string functions: right-scan function classes
are the `List.revConj`-images of the left-scan ones, so their theory transports along
the involution rather than being restated. -/

namespace List

variable {α β γ : Type*}

/-- Conjugation by `List.reverse`: compute on the reversed input, reverse the result. -/
def revConj (f : List α → List β) : List α → List β := fun xs => (f xs.reverse).reverse

@[simp] theorem revConj_revConj (f : List α → List β) : revConj (revConj f) = f := by
  funext xs; simp [revConj]

theorem revConj_comp (g : List β → List γ) (f : List α → List β) :
    revConj (g ∘ f) = revConj g ∘ revConj f := by
  funext xs; simp [revConj]

@[simp] theorem revConj_id : revConj (id : List α → List α) = id := by
  funext xs; simp [revConj]

theorem revConj_eq_iff {h : List α → List β} {f : List α → List β} :
    revConj h = f ↔ h = revConj f := by
  constructor <;> rintro rfl <;> simp

end List

