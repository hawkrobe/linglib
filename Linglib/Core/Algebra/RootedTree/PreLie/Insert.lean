/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Path
import Linglib.Core.Algebra.RootedTree.PreLie.Vertex

set_option autoImplicit false

/-!
# Path-based single-vertex insertion for `Planar α`
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{chapoton-livernet-2001}

`insertAt p T₂ T` grafts `T₂` as a new first child at the vertex
addressed by path `p` in `T`. Out-of-bounds path: no-op.

Sibling to `Path.lean` (path machinery). Lives under namespace
`RootedTree.Planar.Pathed`. Imports `Vertex.lean` solely for the
`insertAt_eq_oldInsertAt` compatibility bridge that connects the new
path-based `insertAt` to the existing `RootedTree.Planar.insertAt v`
during the migration window.

## Status

`[UPSTREAM]` candidate. Sorry-free, no `noncomputable`.
-/

namespace RootedTree

namespace Planar

namespace Pathed

variable {α : Type*}

/-! ## §1: `insertAt` -/

/-- Insert `T₂` as a new first child at the vertex addressed by path `p`
    in `T`. Returns `T` unchanged if `p` is out of bounds (no-op
    fallback for invalid paths). -/
def insertAt : Path → Planar α → Planar α → Planar α
  | [],        T₂, .node a cs => .node a (T₂ :: cs)
  | i :: rest, T₂, .node a cs =>
      if h : i < cs.length then
        .node a (cs.set i (insertAt rest T₂ (cs[i]'h)))
      else
        .node a cs

@[simp] theorem insertAt_nil (T₂ : Planar α) (a : α) (cs : List (Planar α)) :
    insertAt [] T₂ (Planar.node a cs) = Planar.node a (T₂ :: cs) := rfl

@[simp] theorem insertAt_cons_of_lt (i : ℕ) (rest : Path) (T₂ : Planar α)
    (a : α) (cs : List (Planar α)) (h : i < cs.length) :
    insertAt (i :: rest) T₂ (Planar.node a cs) =
      Planar.node a (cs.set i (insertAt rest T₂ (cs[i]'h))) := by
  simp [insertAt, h]

theorem insertAt_cons_of_not_lt (i : ℕ) (rest : Path) (T₂ : Planar α)
    (a : α) (cs : List (Planar α)) (h : ¬ i < cs.length) :
    insertAt (i :: rest) T₂ (Planar.node a cs) = Planar.node a cs := by
  simp [insertAt, h]

/-! ## §2: Compatibility bridge to the old indexed-inductive `Vertex T`

`toPath v` extracts a path from a vertex of the old indexed-inductive
`Vertex T`. The bridge `insertAt_eq_oldInsertAt` then shows that the new
path-based `insertAt` agrees with the old `RootedTree.Planar.insertAt v`
on `toPath v`. -/

mutual
/-- Extract a path from a (legacy) `RootedTree.Planar.Vertex T`. -/
def toPath : ∀ {T : Planar α}, RootedTree.Planar.Vertex T → Path
  | _, .root _ _        => []
  | _, .inChild _ _ vl  =>
      let p := toPathListPair vl; p.1 :: p.2
/-- Extract an (index, sub-path) pair from a (legacy)
    `RootedTree.Planar.VertexList cs`. The index is the position in
    `cs`; the sub-path continues into `cs[index]`. -/
def toPathListPair : ∀ {cs : List (Planar α)},
    RootedTree.Planar.VertexList cs → ℕ × Path
  | _, .head _ _ v    => (0, toPath v)
  | _, .tail _ _ vl   =>
      let p := toPathListPair vl; (p.1 + 1, p.2)
end

@[simp] theorem toPath_root (a : α) (cs : List (Planar α)) :
    toPath (RootedTree.Planar.Vertex.root a cs) = [] := rfl

@[simp] theorem toPath_inChild (a : α) (cs : List (Planar α))
    (vl : RootedTree.Planar.VertexList cs) :
    toPath (RootedTree.Planar.Vertex.inChild a cs vl) =
      (toPathListPair vl).1 :: (toPathListPair vl).2 := rfl

@[simp] theorem toPathListPair_head (c : Planar α) (cs : List (Planar α))
    (v : RootedTree.Planar.Vertex c) :
    toPathListPair (RootedTree.Planar.VertexList.head c cs v) =
      (0, toPath v) := rfl

@[simp] theorem toPathListPair_tail (c : Planar α) (cs : List (Planar α))
    (vl : RootedTree.Planar.VertexList cs) :
    toPathListPair (RootedTree.Planar.VertexList.tail c cs vl) =
      ((toPathListPair vl).1 + 1, (toPathListPair vl).2) := rfl

/-! ### Bridge theorem

Path-based `insertAt` agrees with the indexed-inductive
`RootedTree.Planar.insertAt v` on `toPath v`. Mutual with an aux on
`RootedTree.Planar.VertexList`. -/

mutual
theorem insertAt_eq_oldInsertAt :
    ∀ {T : Planar α} (v : RootedTree.Planar.Vertex T) (T₂ : Planar α),
    insertAt (toPath v) T₂ T = RootedTree.Planar.insertAt v T₂
  | _, .root a cs, T₂ => rfl
  | _, .inChild a cs vl, T₂ => by
    obtain ⟨hi, hset⟩ := insertAt_eq_oldInsertAtList vl T₂
    show insertAt ((toPathListPair vl).1 :: (toPathListPair vl).2) T₂
           (Planar.node a cs) = .node a (RootedTree.Planar.insertAtList vl T₂)
    rw [insertAt_cons_of_lt _ _ _ _ _ hi]
    exact congrArg (Planar.node a) hset
theorem insertAt_eq_oldInsertAtList :
    ∀ {cs : List (Planar α)} (vl : RootedTree.Planar.VertexList cs) (T₂ : Planar α),
    ∃ (hi : (toPathListPair vl).1 < cs.length),
      cs.set (toPathListPair vl).1
        (insertAt (toPathListPair vl).2 T₂ (cs[(toPathListPair vl).1]'hi)) =
      RootedTree.Planar.insertAtList vl T₂
  | _, .head c cs v, T₂ => by
    refine ⟨by simp, ?_⟩
    show (c :: cs).set 0 (insertAt (toPath v) T₂ c) =
         RootedTree.Planar.insertAt v T₂ :: cs
    rw [List.set_cons_zero]
    exact congrArg (· :: cs) (insertAt_eq_oldInsertAt v T₂)
  | _, .tail c cs vl, T₂ => by
    obtain ⟨hi, hset⟩ := insertAt_eq_oldInsertAtList vl T₂
    have hi' : (toPathListPair vl).1 + 1 < (c :: cs).length := by
      simp [List.length_cons]; omega
    refine ⟨hi', ?_⟩
    show (c :: cs).set ((toPathListPair vl).1 + 1)
         (insertAt (toPathListPair vl).2 T₂
           ((c :: cs)[(toPathListPair vl).1 + 1]'hi')) =
         c :: RootedTree.Planar.insertAtList vl T₂
    rw [List.getElem_cons_succ, List.set_cons_succ, hset]
end

end Pathed

end Planar

end RootedTree
