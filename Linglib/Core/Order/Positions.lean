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
carrier's positions; covering in it is covering in `TreePath`
(`Positions.covBy_iff`), so the daughters of a position are its valid
daughters.
-/

namespace Core.Order

namespace Branching

variable {T : Type*} [Branching T]

/-- The valid positions of `t`, as a subtype of `TreePath`. Inherits
the rooted-tree order stack (root, parent, LCA, finite depth) from
`TreePath` via prefix-closure. -/
abbrev Positions (t : T) : Type := {p : TreePath // p ∈ validPaths t}

namespace Positions

variable {t : T}

instance : PartialOrder (Positions t) :=
  Subtype.partialOrder _

@[simp] theorem mk_le_mk {p q : TreePath} {hp hq} :
    (⟨p, hp⟩ : Positions t) ≤ ⟨q, hq⟩ ↔ p ≤ q := Iff.rfl

@[simp] theorem mk_lt_mk {p q : TreePath} {hp hq} :
    (⟨p, hp⟩ : Positions t) < ⟨q, hq⟩ ↔ p < q := Iff.rfl

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
  le_pred_of_lt {_ _} h :=
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

/-- Covering in the positions of `t` is covering in `TreePath`: the daughters of a position
are its valid daughters. -/
theorem covBy_iff {p q : Positions t} : p ⋖ q ↔ p.val ⋖ q.val := by
  constructor
  · intro h
    have hpred : q.val.parent = p.val := congrArg Subtype.val (Order.pred_eq_of_covBy h)
    have hc : Order.pred q.val ⋖ q.val :=
      Order.pred_covBy_of_not_isMin (not_isMin_of_lt (Subtype.coe_lt_coe.mpr h.lt))
    rwa [TreePath.pred_eq_parent, hpred] at hc
  · intro h
    have hpred : Order.pred q = p := Subtype.ext (by rw [pred_val]; exact Order.pred_eq_of_covBy h)
    have hpq : p < q := Subtype.coe_lt_coe.mp h.lt
    have hc : Order.pred q ⋖ q := Order.pred_covBy_of_not_isMin (not_isMin_of_lt hpq)
    rwa [hpred] at hc

end Positions

/-- The positions of `t` as a mathlib `RootedTree`
(`Mathlib.Order.SuccPred.Tree`): the inherited stack, bundled. -/
def Positions.rootedTree (t : T) : RootedTree := ⟨Positions t⟩

end Branching

end Core.Order
