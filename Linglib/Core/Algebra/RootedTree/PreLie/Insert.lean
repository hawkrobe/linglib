/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.PreLie.Path

/-!
# Single-vertex insertion on `RoseTree α`

`insertAt p T₂ T` grafts `T₂` as a new first child of the vertex addressed by the path `p` in
`T`, and leaves `T` unchanged when `p` is out of bounds. `InsertSum.lean` sums it over all
vertices into the Chapoton–Livernet pre-Lie product, and `Graft.lean` generalizes it to
simultaneous grafting at several paths (`multiGraft_singleton`).

## References

* [chapoton-livernet-2001]
* [foissy-typed-decorated-rooted-trees-2018]
-/

@[expose] public section

namespace RoseTree

namespace Pathed

variable {α : Type*}

/-- Insert `T₂` as a new first child at the vertex addressed by path `p`
    in `T`. Returns `T` unchanged if `p` is out of bounds (no-op
    fallback for invalid paths). -/
def insertAt : Path → RoseTree α → RoseTree α → RoseTree α
  | [],        T₂, .node a cs => .node a (T₂ :: cs)
  | i :: rest, T₂, .node a cs =>
      if h : i < cs.length then
        .node a (cs.set i (insertAt rest T₂ (cs[i]'h)))
      else
        .node a cs

@[simp] theorem insertAt_nil (T₂ : RoseTree α) (a : α) (cs : List (RoseTree α)) :
    insertAt [] T₂ (RoseTree.node a cs) = RoseTree.node a (T₂ :: cs) := rfl

@[simp] theorem insertAt_cons_of_lt (i : ℕ) (rest : Path) (T₂ : RoseTree α)
    (a : α) (cs : List (RoseTree α)) (h : i < cs.length) :
    insertAt (i :: rest) T₂ (RoseTree.node a cs) =
      RoseTree.node a (cs.set i (insertAt rest T₂ (cs[i]'h))) := by
  simp [insertAt, h]

theorem insertAt_cons_of_not_lt (i : ℕ) (rest : Path) (T₂ : RoseTree α)
    (a : α) (cs : List (RoseTree α)) (h : ¬ i < cs.length) :
    insertAt (i :: rest) T₂ (RoseTree.node a cs) = RoseTree.node a cs := by
  simp [insertAt, h]

end Pathed

end RoseTree
