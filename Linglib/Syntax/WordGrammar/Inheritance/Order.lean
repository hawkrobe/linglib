import Linglib.Syntax.WordGrammar.Inheritance.Basic
import Mathlib.Order.Defs.PartialOrder

/-!
# Inheritance Order — Preorder view of an isA taxonomy

[hudson-2010]'s isA backbone is reflexive and transitive (`IsA.refl`,
`IsA.trans` in `WordGrammar.Inheritance.Basic`), which makes it a `Preorder` on the
node type. Once the instance is in place, every preorder lemma (`le_trans`,
`le_refl`, `Antichain`, `LowerSet`, `UpperSet`, `OrderHom`) is available for
free over the isA backbone of any concrete network.

**Important caveat: structural backbone, not entailment over properties.**
This `Preorder` reflects only the *structural* isA relation. It is **not**
the entailment order on inherited properties: `a ≤ b` does NOT imply
`inherited net a r ⊆ inherited net b r`, because Hudson WG is *default*-
inheritance and children may override parents (see `Default.lean`). The
Best Fit Principle is a procedural tiebreaker over the same backbone, not
a monotone propagation along it. HPSG-style monotonic subsumption requires
an `Acyclic` hypothesis plus appropriateness conditions this substrate
does not impose; do not assume `IsAOrder` reuse on the HPSG side without
those.

The instance is placed on a wrapper type `IsAOrder net` rather than directly
on `α`, because a single node type may participate in multiple unrelated
networks (e.g. `WGNode` in `englishAuxNet`, in a hypothetical `germanAuxNet`,
in test fixtures). The wrapper is the idiomatic mathlib pattern (cf.
`OrderDual`, `Multiplicative`).

## Usage

```
-- A preorder on the nodes of `englishAuxNet`:
example : Preorder (IsAOrder englishAuxNet) := inferInstance

-- `(a : IsAOrder net) ≤ b` means `IsA net a b`:
example (a b : IsAOrder net) : a ≤ b ↔ IsA net (a : α) b := Iff.rfl

-- To compare two `α`-valued nodes via the preorder, route through `mk`:
example (h : IsA net x y) : IsAOrder.mk net x ≤ IsAOrder.mk net y := h
```

A bare type ascription `(x : IsAOrder net) ≤ (y : IsAOrder net)` does not work
because instance synthesis unfolds `IsAOrder net` back to `α` and then fails to
find `LE α`. The `mk` function-call carries the wrapper through elaboration.
-/

set_option autoImplicit false

namespace WordGrammar.Inheritance

variable {α R : Type} [DecidableEq α] [DecidableEq R]

/-- A node type viewed as preordered by the isA closure of a particular
network. Definitionally equal to `α`, but carries the `Preorder` instance. -/
def IsAOrder (_ : Network α R) : Type := α

namespace IsAOrder

/-- Tag a node as inhabiting the preorder view of `net`. Mirrors mathlib's
`OrderDual.toDual`: a function-call wrapper avoids the elaboration pitfall
where `(a : IsAOrder net)` ascription gets unfolded to `α` during instance
search, leaving `LE α` (which doesn't exist) instead of `LE (IsAOrder net)`. -/
def mk (net : Network α R) (a : α) : IsAOrder net := a

/-- Forget the preorder view, returning the underlying node. -/
def val {net : Network α R} (a : IsAOrder net) : α := a

/-- The `Preorder` instance derived from `IsA`'s reflexivity and transitivity. -/
instance preorder (net : Network α R) : Preorder (IsAOrder net) where
  le a b := IsA net a b
  le_refl a := IsA.refl net a
  le_trans _ _ _ := IsA.trans net

/-- The wrapper's `≤` unfolds definitionally to `IsA`. -/
@[simp] theorem le_def (net : Network α R) (a b : IsAOrder net) :
    a ≤ b ↔ IsA net a b := Iff.rfl

/-- `mk` and `val` round-trip definitionally. -/
@[simp] theorem val_mk (net : Network α R) (a : α) : val (mk net a) = a := rfl

end IsAOrder

end WordGrammar.Inheritance
