import Linglib.Core.Inheritance.Basic
import Mathlib.Order.Defs.PartialOrder

/-!
# Inheritance Order — Preorder view of an isA taxonomy

@cite{hudson-2010}'s isA backbone is reflexive and transitive (`IsA.refl`,
`IsA.trans` in `Core.Inheritance.Basic`), which makes it a `Preorder` on the
node type. mathlib's `Preorder` typeclass is the right home for this fact:
once the instance is in place, every preorder lemma (`le_trans`, `le_refl`,
`Antichain`, `LowerSet`, `UpperSet`, `OrderHom`) becomes available for free
to downstream WG / kinship / HPSG hierarchies.

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
```
-/

set_option autoImplicit false

namespace Core.Inheritance

variable {α R : Type} [DecidableEq α] [DecidableEq R]

/-- A node type viewed as preordered by the isA closure of a particular
network. Definitionally equal to `α`, but carries the `Preorder` instance. -/
def IsAOrder (_ : Network α R) : Type := α

namespace IsAOrder

/-- The `Preorder` instance derived from `IsA`'s reflexivity and transitivity. -/
instance preorder (net : Network α R) : Preorder (IsAOrder net) where
  le a b := IsA net a b
  le_refl a := IsA.refl net a
  le_trans _ _ _ := IsA.trans net

/-- The wrapper's `≤` unfolds definitionally to `IsA`. -/
@[simp] theorem le_def (net : Network α R) (a b : IsAOrder net) :
    a ≤ b ↔ IsA net a b := Iff.rfl

end IsAOrder

end Core.Inheritance
