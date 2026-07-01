/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
import Linglib.Core.Data.Tree.Basic

/-!
# Rose tree indexing by Gorn address

Navigation into an n-ary `Tree` by a **Gorn address**: a `List ℕ` path of child
indices. `subtreeAt` returns the subtree reached by descending along the path,
`get?` its root value, `getD` with a fallback.

Unlike `BinaryTree.get` (indexed by a `PosNum` left/right path) there is no
`indexOf`: that is a binary-search-tree lookup, which has no analogue for a
general (unordered-search) rose tree. The Gorn path replaces the `PosNum` path,
so this file needs no `Num` dependency.
-/

namespace RootedTree.Tree

variable {α : Type*}

/-- The subtree at a **Gorn address** (a path of child indices); `none` if the
path steps outside the tree. -/
def subtreeAt (t : Tree α) : List ℕ → Option (Tree α)
  | [] => some t
  | i :: rest => t.children[i]?.bind fun c => c.subtreeAt rest

@[simp] theorem subtreeAt_nil (t : Tree α) : t.subtreeAt [] = some t := rfl

@[simp] theorem subtreeAt_cons (t : Tree α) (i : ℕ) (rest : List ℕ) :
    t.subtreeAt (i :: rest) = t.children[i]?.bind fun c => c.subtreeAt rest := rfl

/-- Gorn composition: descending along `p ++ q` is descending along `p`, then
along `q` from the result. -/
theorem subtreeAt_append (t : Tree α) (p q : List ℕ) :
    t.subtreeAt (p ++ q) = (t.subtreeAt p).bind (·.subtreeAt q) := by
  induction p generalizing t with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.cons_append, subtreeAt_cons]
    cases t.children[i]? with
    | none => simp
    | some c => simpa using ih c

/-- The root value at a Gorn address; `none` if the path steps outside the tree. -/
def get? (t : Tree α) (path : List ℕ) : Option α :=
  (t.subtreeAt path).map value

/-- The root value at a Gorn address, or `v` if the path is invalid. -/
def getD (t : Tree α) (path : List ℕ) (v : α) : α :=
  (t.get? path).getD v

@[simp] theorem get?_nil (t : Tree α) : t.get? [] = some t.value := rfl

@[simp] theorem getD_nil (t : Tree α) (v : α) : t.getD [] v = t.value := rfl

end RootedTree.Tree
