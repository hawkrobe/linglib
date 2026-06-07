import Linglib.Syntax.WordGrammar.Inheritance.Basic

/-!
# Default Inheritance — Local Properties + BFS Lookup + Best Fit Principle

[hudson-2010] §2.5, §3.5, §4.6.4

A node's value for a relation `r` is determined by:

1. Its **local** value if one is specified (`localProps net node r`).
2. Otherwise, the value of its **nearest ancestor** in the isA chain that
   has a local value for `r` — the **Best Fit Principle**:
   "When a default conflicts with a more specific fact, the specific
   fact wins" [hudson-2010] §4.6.4. Hudson attributes the principle
   to Winograd's earlier work on frame-based defaults but generalises it
   from frames to a property of the cognitive network as a whole.

Like `ancestors`, the BFS recursion is bounded by `nodeUniverse.length`
rather than a magic constant — finite networks always reach a fixpoint.

The override case (where a child specifies a local value that differs from
its parent's) is the empirical heart of WG: passive inherits transitive's
arg-structure but overrides slot 1; the inverted auxiliary inherits the
verb's subject slot but overrides its direction.
-/

set_option autoImplicit false

namespace WordGrammar.Inheritance

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

/-- Every value returned by `localProps` is the target of a `prop` link
from `node` labelled `r`. The "kind discipline" — `localProps` only ever
returns the targets of property links, never of isA or or links. -/
theorem localProps_via_prop_link (net : Network α R) (node : α) (r : R)
    (a : α) (h : a ∈ localProps net node r) :
    ∃ l ∈ net.links, l.kind = .prop ∧ l.source = node ∧ l.label = some r ∧
      l.target = a := by
  simp only [localProps, List.mem_map, List.mem_filter] at h
  obtain ⟨l, ⟨hmem, hcond⟩, htgt⟩ := h
  simp only [beq_iff_eq, Bool.and_eq_true] at hcond
  exact ⟨l, hmem, hcond.1.1, hcond.1.2, hcond.2, htgt⟩

/-- The `inherited` BFS is monotone in the link list: adding new property
links for `r` to `node` can only add to (never remove from) `localProps`. This
is a sanity check on the network update semantics. -/
theorem localProps_monotone_in_links (net₁ net₂ : Network α R) (node : α) (r : R)
    (hsub : net₁.links ⊆ net₂.links) (a : α)
    (hmem : a ∈ localProps net₁ node r) :
    a ∈ localProps net₂ node r := by
  simp only [localProps, List.mem_map, List.mem_filter] at hmem ⊢
  obtain ⟨l, ⟨hmem₁, hcond⟩, htgt⟩ := hmem
  exact ⟨l, ⟨hsub hmem₁, hcond⟩, htgt⟩

end WordGrammar.Inheritance
