/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Basic
public import Linglib.Core.Data.RoseTree.Licensed

/-!
# Licensed unordered trees

A relation `R` between a value and a multiset of values licenses an unordered tree when every
subtree satisfies it at its root, the daughters' labels read without order. Since `R` reads a
multiset, it licenses every ordered representative of the tree alike
(`RoseTree.licensed_of_perm`), so licensing descends to the quotient.

## Main definitions

* `UnorderedTree.Licensed R u`: every subtree of `u` satisfies `R` at its root.
-/

@[expose] public section

namespace UnorderedTree

variable {α : Type*}

/-- A relation `R` licenses an unordered tree when it licenses its ordered representatives, the
children's values read as a multiset. -/
def Licensed (R : α → Multiset α → Prop) (u : UnorderedTree α) : Prop :=
  Quotient.liftOn u (fun t ↦ t.Licensed fun a ks ↦ R a (ks : Multiset α)) fun _ _ h ↦
    propext (RoseTree.licensed_of_perm (fun _ _ _ hkl ↦ by rw [Multiset.coe_eq_coe.mpr hkl]) h)

@[simp] theorem licensed_mk (R : α → Multiset α → Prop) (t : RoseTree α) :
    (mk t).Licensed R ↔ t.Licensed fun a ks ↦ R a (ks : Multiset α) :=
  Iff.rfl

instance (R : α → Multiset α → Prop) [∀ a ks, Decidable (R a ks)] (u : UnorderedTree α) :
    Decidable (u.Licensed R) :=
  Quotient.recOnSubsingleton u fun t ↦
    inferInstanceAs (Decidable (t.Licensed fun a ks ↦ R a (ks : Multiset α)))

end UnorderedTree
