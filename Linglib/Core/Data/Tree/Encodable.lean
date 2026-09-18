/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Tree.Basic
import Mathlib.Tactic.DeriveEncodable
import Mathlib.Tactic.DeriveCountable

/-!
# Binary trees are encodable

`BinaryTree` is a non-nested inductive type, so mathlib's deriving handlers supply the
`Encodable` and `Countable` instances that `Mathlib.Data.Tree.Basic` omits.

`[UPSTREAM]` candidate: the `deriving` clause of `BinaryTree`.
-/

deriving instance Encodable, Countable for BinaryTree
