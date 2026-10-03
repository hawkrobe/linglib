module

public import Linglib.Core.Order.Branching

/-!
# Positions of a tree

The valid positions of a tree `t` of a `Branching` carrier form `Branching.Positions t`, a subtype
of `TreePath`. Since `validPaths t` is prefix-closed, the positions inherit the order structure of
`TreePath`: the root is the least position, the parent of a position and the meet of two positions
are again positions, and strict dominance is well founded, so `Positions t` is a rooted tree in the
sense of `Mathlib/Order/SuccPred/Tree.lean`. Covering in `Positions t` is covering in `TreePath`
(`Positions.covBy_iff`), so the daughters of a position are its valid daughters.
-/

@[expose] public section

namespace Core.Order

namespace Branching

variable {T : Type*} [Branching T]

/-- The valid positions of `t`, as a subtype of `TreePath`, form a rooted tree under the prefix
order. -/
abbrev Positions (t : T) : Type := {p : TreePath // p ∈ validPaths t}

namespace Positions

variable {t : T}

/-- The root is the least position. -/
instance : OrderBot (Positions t) where
  bot := ⟨⊥, bot_mem_validPaths t⟩
  bot_le p := bot_le (a := p.val)

@[simp] theorem bot_val : ((⊥ : Positions t) : TreePath) = ⊥ := rfl

/-- The meet of two positions, their longest common prefix, is a position, since it dominates
either. -/
instance : SemilatticeInf (Positions t) :=
  Subtype.semilatticeInf fun _ _ hp _ ↦ validPaths_prefix_closed hp inf_le_left

@[simp] theorem inf_val (p q : Positions t) :
    ((p ⊓ q : Positions t) : TreePath) = p.val ⊓ q.val := rfl

/-- The parent of a position is a position. -/
instance : PredOrder (Positions t) where
  pred p := ⟨p.val.parent, validPaths_prefix_closed p.2 (TreePath.parent_le _)⟩
  pred_le p := TreePath.parent_le p.val
  min_of_le_pred {p} h := fun b hb ↦
    show p ≤ b from
      PredOrder.min_of_le_pred (α := TreePath)
        (show p.val ≤ Order.pred p.val from h)
        (show b.val ≤ p.val from hb)
  le_pred_of_lt {_ _} h :=
    TreePath.le_parent_of_lt (Subtype.coe_lt_coe.mpr h)

@[simp] theorem pred_val (p : Positions t) :
    ((Order.pred p : Positions t) : TreePath) = p.val.parent := rfl

/-- Covering in the positions of `t` is covering in `TreePath`, so the daughters of a position
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

end Branching

end Core.Order
