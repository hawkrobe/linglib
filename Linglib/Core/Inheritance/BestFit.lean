import Linglib.Core.Inheritance.Default

/-!
# Best Fit Principle

@cite{hudson-2010} §4.6.4 (p. 94).

> "When a default conflicts with a more specific fact, the specific fact wins."

Hudson attributes the principle to Winograd's earlier work on frame-based
defaults but generalises it from frames to a property of the cognitive
network as a whole. In WG, the Best Fit Principle is what makes inheritance
work as a model of linguistic competence: a learner does not have to record
every property of every word, because most properties default through the
isA hierarchy.

This module collects theorems characterising when `inherited` returns a
deterministic value, and how it interacts with structural properties of
the network.

## Re-exports

`bestFit_local` (proven in `Default.lean`): when a local value exists, it
shadows any inherited value.
-/

set_option autoImplicit false

namespace Core.Inheritance

variable {α R : Type} [DecidableEq α] [DecidableEq R]

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

end Core.Inheritance
