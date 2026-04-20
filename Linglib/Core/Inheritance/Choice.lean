import Linglib.Core.Inheritance.Basic

/-!
# Choice Sets (OR / Mutual Exclusivity)

@cite{hudson-2010} §3.3

OR-links partition values into mutually exclusive alternatives. The schematic
example: `male --or--> gender`, `female --or--> gender` says that `male` and
`female` are alternative values along the `gender` dimension.

**Future work**: this should be reframed as a `Setoid`/`Partition` quotient
structure (see `project_inheritance_consolidation.md`). The current `LinkKind.or`
case stores choice membership as a relation in the link list; a partition-class
representation would make exhaustivity and disjointness definitional rather than
provable.
-/

set_option autoImplicit false

namespace Core.Inheritance

variable {α R : Type} [DecidableEq α] [DecidableEq R]

/-- OR-alternatives of a node (§3.3): mutually exclusive choices.
E.g., `choiceSet net gender` returns `[male, female]` if the network contains
`male --or--> gender` and `female --or--> gender`. -/
def choiceSet (net : Network α R) (node : α) : List α :=
  (net.links.filter (fun l => l.kind == .or && l.target == node)).map Link.source

/-- Membership in `choiceSet` is exactly being the source of an `or` link
into `node`. -/
theorem mem_choiceSet_iff (net : Network α R) (node a : α) :
    a ∈ choiceSet net node ↔
      ∃ label : Option R, ⟨LinkKind.or, a, node, label⟩ ∈ net.links := by
  unfold choiceSet
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨l, ⟨hmem, hkind⟩, htgt⟩
    refine ⟨l.label, ?_⟩
    obtain ⟨k, s, t, lab⟩ := l
    simp only [beq_iff_eq, Bool.and_eq_true] at hkind
    obtain ⟨hk, ht⟩ := hkind
    cases hk; cases ht; cases htgt; exact hmem
  · rintro ⟨label, hmem⟩
    refine ⟨⟨LinkKind.or, a, node, label⟩, ⟨hmem, ?_⟩, rfl⟩
    simp

end Core.Inheritance
