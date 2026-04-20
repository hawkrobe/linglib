import Linglib.Core.Inheritance.Basic

/-!
# Default Inheritance — Local Properties + BFS Lookup

@cite{hudson-2010} §2.5, §3.5

A node's value for a relation `r` is determined by:

1. Its **local** value if one is specified (`localProps net node r`).
2. Otherwise, the value of its **nearest ancestor** in the isA chain that
   has a local value for `r` (Best Fit Principle, see `BestFit.lean`).

Like `ancestors`, the BFS recursion is bounded by `nodeUniverse.length`
rather than a magic constant — finite networks always reach a fixpoint.

The override case (where a child specifies a local value that differs from
its parent's) is the empirical heart of WG: passive inherits transitive's
arg-structure but overrides slot 1; the inverted auxiliary inherits the
verb's subject slot but overrides its direction.
-/

set_option autoImplicit false

namespace Core.Inheritance

variable {α R : Type} [DecidableEq α] [DecidableEq R]

/-- Local property values: targets of `.prop` links from `node` with label `r`.
A node may have multiple values for the same relation (e.g., a bird has two
wings). -/
def localProps (net : Network α R) (node : α) (r : R) : List α :=
  (net.links.filter (fun l =>
    l.kind == .prop && l.source == node && l.label == some r)).map Link.target

/-- Bounded BFS for inherited property values. The `bound` parameter is intended
to be ≥ `(nodeUniverse net).length`. Structurally recursive on `Nat`. -/
def inheritedBound (net : Network α R) (node : α) (r : R) : Nat → List α
  | 0 => localProps net node r
  | n + 1 =>
    match localProps net node r with
    | [] =>
      let ps := parents net node
      -- breadth-first: check all direct parents before going deeper
      match ps.findSome? (fun p =>
        match localProps net p r with
        | [] => none
        | vs => some vs) with
      | some vs => vs
      | none =>
        ps.findSome? (fun p =>
          match inheritedBound net p r n with
          | [] => none
          | vs => some vs) |>.getD []
    | vs => vs

/-- Inherited property values for relation `r`, resolved by the Best Fit Principle:
the most specific (nearest ancestor in the isA chain) wins. Recursion bound
derived from network size. -/
def inherited (net : Network α R) (node : α) (r : R) : List α :=
  inheritedBound net node r net.nodeUniverse.length

/-- If a node has local properties for `r`, `inherited` returns them directly
(local overrides inherited). -/
theorem bestFit_local (net : Network α R) (node : α) (r : R)
    (h : localProps net node r ≠ []) :
    inherited net node r = localProps net node r := by
  unfold inherited inheritedBound
  split
  · rfl
  · split
    · contradiction
    · rfl

end Core.Inheritance
