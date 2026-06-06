import Linglib.Core.Order.Branching

/-!
# Positions of a Tree: the Inherited Order Stack

`Branching.Positions t` — the valid positions of a concrete tree, as a
subtype of `TreePath`. Because `validPaths` is prefix-closed
(`validPaths_prefix_closed`), the subtype inherits the full
rooted-tree order stack from `TreePath`:

| instance            | reading                                      |
|---------------------|----------------------------------------------|
| `OrderBot`          | the root position                            |
| `PredOrder`         | parent (mother-of) stays inside the tree     |
| `SemilatticeInf`    | least common ancestor stays inside the tree  |
| `IsPredArchimedean` | finite ancestor chains                       |

This makes the per-tree position type a rooted tree in mathlib's
order-theoretic sense (`Mathlib.Order.SuccPred.Tree`), with parent,
LCA, and the lattice lemma library available on any `Branching`
carrier's positions.

## The B&P bridge

`TreeOrder.ofPredArchimedean` connects the mathlib stack to
[barker-pullum-1990]'s `TreeOrder`: any bottomed pred-archimedean
partial order satisfies the Connected Ancestor Condition, because two
ancestors of one node are both pred-iterates of it and hence
comparable. B&P's structure is the strictly more general one (it
admits dense dominance orders with no parent function); this is the
general-structure-plus-specialization pattern, connected by
construction rather than stipulation.
-/

namespace Core.Order

namespace Branching

variable {T : Type*} [Branching T]

/-- The valid positions of `t`, as a subtype of `TreePath`. Inherits
the rooted-tree order stack (root, parent, LCA, finite depth) from
`TreePath` via prefix-closure. -/
@[reducible] def Positions (t : T) : Type := {p : TreePath // p ∈ validPaths t}

namespace Positions

variable {t : T}

instance : PartialOrder (Positions t) :=
  Subtype.partialOrder _

@[simp] theorem mk_le_mk {p q : TreePath} {hp hq} :
    (⟨p, hp⟩ : Positions t) ≤ ⟨q, hq⟩ ↔ p ≤ q := Iff.rfl

/-- The root position. -/
instance : OrderBot (Positions t) where
  bot := ⟨⊥, bot_mem_validPaths t⟩
  bot_le p := bot_le (a := p.val)

@[simp] theorem bot_val : ((⊥ : Positions t) : TreePath) = ⊥ := rfl

/-- Least common ancestor: the LCA of two valid positions is valid
(it is an ancestor of either). -/
instance : SemilatticeInf (Positions t) where
  inf p q := ⟨p.val ⊓ q.val, validPaths_prefix_closed p.2 inf_le_left⟩
  inf_le_left _ _ := inf_le_left (α := TreePath)
  inf_le_right _ _ := inf_le_right (α := TreePath)
  le_inf _ _ _ h₁ h₂ := le_inf (α := TreePath) h₁ h₂

@[simp] theorem inf_val (p q : Positions t) :
    ((p ⊓ q : Positions t) : TreePath) = p.val ⊓ q.val := rfl

/-- Parent: the parent of a valid position is valid. -/
instance : PredOrder (Positions t) where
  pred p := ⟨p.val.parent, validPaths_prefix_closed p.2 (TreePath.parent_le _)⟩
  pred_le p := TreePath.parent_le p.val
  min_of_le_pred {p} h := fun b hb =>
    show p ≤ b from
      PredOrder.min_of_le_pred (α := TreePath)
        (show p.val ≤ Order.pred p.val from h)
        (show b.val ≤ p.val from hb)
  le_pred_of_lt {p q} h :=
    TreePath.le_parent_of_lt (Subtype.coe_lt_coe.mpr h)

@[simp] theorem pred_val (p : Positions t) :
    ((Order.pred p : Positions t) : TreePath) = p.val.parent := rfl

private theorem pred_iterate_val (p : Positions t) (n : Nat) :
    ((Order.pred)^[n] p : Positions t).val = (Order.pred)^[n] p.val := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

/-- Finite ancestor chains, inherited from `TreePath`. -/
instance : IsPredArchimedean (Positions t) where
  exists_pred_iterate_of_le {p q} h := by
    obtain ⟨n, hn⟩ :=
      IsPredArchimedean.exists_pred_iterate_of_le (α := TreePath) h
    exact ⟨n, Subtype.ext (by rw [pred_iterate_val]; exact hn)⟩

end Positions

end Branching

/-! ### The B&P bridge -/

/-- **The mathlib-stack ⟹ B&P bridge**: any bottomed pred-archimedean
partial order is a [barker-pullum-1990] `TreeOrder` on its whole
carrier. The Connected Ancestor Condition holds because two ancestors
of `z` are both pred-iterates of `z` (`exists_pred_iterate_of_le`) and
iterates are comparable (`le_total_of_directed`). B&P's structure is
strictly more general (dense dominance orders have no `PredOrder`);
this bridge realizes the general-plus-specialization pattern by
construction. -/
def TreeOrder.ofPredArchimedean (α : Type*) [PartialOrder α]
    [PredOrder α] [IsPredArchimedean α] [OrderBot α] : TreeOrder α where
  nodes := Set.univ
  root := ⊥
  root_in_nodes := Set.mem_univ _
  root_le_all _ _ := bot_le
  ancestor_connected x y z hx hy := le_total_of_directed hy hx

end Core.Order
