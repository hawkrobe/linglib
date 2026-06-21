import Mathlib.Order.RelClasses
import Mathlib.Order.Interval.Finset.Basic

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
antisymmetry and the isolation.

The order structure itself is mathlib's: `RankLT` is a strict order
(`IsStrictOrder` instance below), so `partialOrderOfRank` is
`partialOrderOfSO (RankLT r)` and `RankLE` (`a = b ∨ RankLT r a b`) is
exactly the reflexive-closure shape `partialOrderOfSO` uses for `≤`.
This file's value-add is `RankLT` itself, its decidability, and the
isolation lemmas. There is no total variant: isolation precludes
totality whenever any element is unranked.

## Main declarations

* `Core.Order.RankLT` — strict comparison through a partial rank
* `Core.Order.RankLE` — its reflexive closure
* `Core.Order.rankLE_iff_eq_left`/`rankLE_iff_eq_right` — isolation:
  an unranked element is `≤`-related only to itself
* `Core.Order.partialOrderOfRank` — `partialOrderOfSO` at `RankLT r`;
  `<` is definitionally `RankLT` and `≤` is `RankLE`
* `Core.Order.rankShells` — the canonical down-set decomposition `Iic ∘ r`,
  and `rankLT_iff_rankShells`: the rank order *is* the shadow of inclusion
  between the down-sets (the structural fact behind nanosyntactic "feature
  stack" decompositions, replacing per-instance stipulate-a-table-and-`decide`)
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

/-- `RankLT` is a strict order — the bridge to mathlib's order
    constructors. -/
instance (r : α → Option β) [Preorder β] : IsStrictOrder α (RankLT r) where
  irrefl := rankLT_irrefl
  trans _ _ _ := RankLT.trans

/-- The partial order induced by a partial rank: `partialOrderOfSO` at
    `RankLT r`, so `<` is definitionally `RankLT r` and `≤` is
    `RankLE r`. Intended for `scoped instance`s: a theoretical hierarchy
    is borne by a feature type as an opt-in commitment, never as a
    global instance.

    See note [reducible non-instances]. -/
abbrev partialOrderOfRank (r : α → Option β) [Preorder β] :
    PartialOrder α :=
  partialOrderOfSO (RankLT r)

end Preorder

section Shells

variable {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]

/-- The canonical **down-set decomposition** of a partial rank: an element's
    content is the initial segment `Finset.Iic` of its rank (its "shell stack";
    cf. the order-theoretic primitive `LowerSet.Iic`). For a rank into a chain an
    element *is* this down-set, and the rank order is the shadow of inclusion
    between the down-sets (`rankLT_iff_rankShells`). The structure behind
    nanosyntactic feature-stack decompositions (`Syntax/Case/Order.lean`). -/
def rankShells (r : α → Option ι) (a : α) : Option (Finset ι) :=
  (r a).map Finset.Iic

/-- **The rank order is the shadow of its down-set decomposition.** Strict-rank
    comparison through `r` coincides with strict inclusion of the shell stacks
    `rankShells r` — `Finset.Iic` being strictly monotone
    (`Finset.Iic_ssubset_Iic`). Generic over any rank into a locally-finite-below
    preorder, replacing per-instance "stipulate a shells table + `decide` it
    agrees with the rank". -/
theorem rankLT_iff_rankShells (r : α → Option ι) (a b : α) :
    RankLT r a b ↔ RankLT (rankShells r) a b := by
  rw [rankLT_iff, rankLT_iff]
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact ⟨Finset.Iic x, Finset.Iic y, by rw [rankShells, hx]; rfl,
      by rw [rankShells, hy]; rfl, Finset.Iic_ssubset_Iic.mpr hxy⟩
  · rintro ⟨X, Y, hX, hY, hXY⟩
    simp only [rankShells, Option.map_eq_some_iff] at hX hY
    obtain ⟨x, hx, rfl⟩ := hX
    obtain ⟨y, hy, rfl⟩ := hY
    exact ⟨x, y, hx, hy, Finset.Iic_ssubset_Iic.mp hXY⟩

end Shells

end Core.Order
