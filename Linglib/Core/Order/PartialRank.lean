import Mathlib.Order.Basic

/-!
# Partial-Rank Orders

The partial order induced by a partial rank function `r : α → Option β`:
ranked elements compare by strict rank comparison, unranked elements are
**isolated** — comparable only to themselves.

This is the order-theoretic gadget behind linguistic hierarchies that are
deliberately silent on part of the inventory: Caha's case-containment
order (`Syntax/Case/Order.lean`) ranks NOM < ACC < GEN < DAT < LOC and
says nothing about ERG or ABS, and the silence is theoretical content.

No pullback produces this. `Preorder.lift` through `r` (the
`PullbackPreorder` construction) would make all unranked elements
mutually equivalent — `r a = r b = none` gives `a ≤ b ≤ a` — losing
antisymmetry and the isolation. Hence the direct construction: `RankLE`
is the reflexive closure of the strict comparison `RankLT`, which is
asymmetric and transitive whenever `<` on `β` is, so the closure is a
genuine partial order.

## Main declarations

* `Core.Order.RankLT` — strict comparison through a partial rank
* `Core.Order.RankLE` — its reflexive closure
* `Core.Order.partialOrderOfRank` — the bundled `PartialOrder`, with
  `<` definitionally `RankLT`
-/

namespace Core.Order

variable {α β : Type*}

/-- Strict comparison through a partial rank: both elements are ranked
    and the ranks compare strictly. Unranked elements relate to
    nothing. -/
def RankLT (r : α → Option β) [LT β] (a b : α) : Prop :=
  match r a, r b with
  | some x, some y => x < y
  | _, _ => False

/-- Non-strict comparison through a partial rank: the reflexive closure
    of `RankLT`. Unranked elements are isolated — `≤`-related only to
    themselves. -/
def RankLE (r : α → Option β) [LT β] (a b : α) : Prop :=
  a = b ∨ RankLT r a b

section LT

variable (r : α → Option β) [LT β]

instance [DecidableRel ((· < ·) : β → β → Prop)] :
    DecidableRel (RankLT r) := fun a b => by
  unfold RankLT; split <;> infer_instance

instance [DecidableEq α] [DecidableRel ((· < ·) : β → β → Prop)] :
    DecidableRel (RankLE r) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

variable {r} {a b : α}

theorem rankLT_iff :
    RankLT r a b ↔ ∃ x y, r a = some x ∧ r b = some y ∧ x < y := by
  unfold RankLT
  split <;> simp_all

theorem RankLT.rankLE (h : RankLT r a b) : RankLE r a b := Or.inr h

theorem rankLE_refl (a : α) : RankLE r a a := Or.inl rfl

/-- An unranked element is `≤`-related only to itself (left). -/
theorem rankLE_iff_eq_left (h : r a = none) : RankLE r a b ↔ a = b := by
  refine ⟨fun hab => hab.resolve_right fun hlt => ?_, Or.inl⟩
  obtain ⟨x, _, hx, _, _⟩ := rankLT_iff.mp hlt
  rw [h] at hx
  exact Option.some_ne_none _ hx.symm

/-- An unranked element is `≤`-related only to itself (right). -/
theorem rankLE_iff_eq_right (h : r b = none) : RankLE r a b ↔ a = b := by
  refine ⟨fun hab => hab.resolve_right fun hlt => ?_, Or.inl⟩
  obtain ⟨_, y, _, hy, _⟩ := rankLT_iff.mp hlt
  rw [h] at hy
  exact Option.some_ne_none _ hy.symm

end LT

section Preorder

variable {r : α → Option β} [Preorder β] {a b c : α}

theorem RankLT.trans (hab : RankLT r a b) (hbc : RankLT r b c) :
    RankLT r a c := by
  obtain ⟨x, y, hx, hy, hxy⟩ := rankLT_iff.mp hab
  obtain ⟨y', z, hy', hz, hyz⟩ := rankLT_iff.mp hbc
  obtain rfl := Option.some.inj (hy.symm.trans hy')
  exact rankLT_iff.mpr ⟨x, z, hx, hz, lt_trans hxy hyz⟩

theorem rankLT_irrefl (a : α) : ¬RankLT r a a := fun h => by
  obtain ⟨x, y, hx, hy, hxy⟩ := rankLT_iff.mp h
  obtain rfl := Option.some.inj (hx.symm.trans hy)
  exact lt_irrefl x hxy

theorem RankLT.asymm (hab : RankLT r a b) : ¬RankLT r b a := fun hba =>
  rankLT_irrefl a (hab.trans hba)

theorem rankLE_trans (hab : RankLE r a b) (hbc : RankLE r b c) :
    RankLE r a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  · exact Or.inr (hab.trans hbc)

theorem rankLE_antisymm (hab : RankLE r a b) (hba : RankLE r b a) :
    a = b := by
  rcases hab with rfl | hab
  · rfl
  rcases hba with rfl | hba
  · rfl
  · exact absurd hba hab.asymm

/-- The partial order induced by a partial rank. `≤` is `RankLE r`; `<`
    is definitionally `RankLT r`. Intended for `scoped instance`s: a
    theoretical hierarchy is borne by a feature type as an opt-in
    commitment, never as a global instance. -/
@[reducible] def partialOrderOfRank (r : α → Option β) [Preorder β] :
    PartialOrder α where
  le := RankLE r
  lt := RankLT r
  le_refl := rankLE_refl
  le_trans _ _ _ := rankLE_trans
  le_antisymm _ _ := rankLE_antisymm
  lt_iff_le_not_ge a _ :=
    ⟨fun h => ⟨h.rankLE, fun hba => hba.elim (fun he => rankLT_irrefl a (he ▸ h)) h.asymm⟩,
     fun ⟨hab, hba⟩ => hab.resolve_left fun he => hba (Or.inl he.symm)⟩

end Preorder

end Core.Order
