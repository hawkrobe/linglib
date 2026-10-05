module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Order.Preorder.Finite

/-!
# Left-linear orders

A partial order is **left-linear** when the predecessors of every element are linearly
ordered: `a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a`. Equivalently, every principal down-set `Iic m`
is a chain. This is the order-theoretic notion of a tree: the order may branch upward but
never downward.

Linear orders are left-linear, and so is every rooted tree in the sense of
`Mathlib/Order/SuccPred/Tree.lean`: a `PredOrder` with archimedean predecessor is left-linear by
mathlib's `le_total_of_directed`. Left-linearity also pulls back along any order embedding
(`OrderEmbedding.isLeftLinear`), so a suborder of a tree is left-linear. Branching-time frames,
which need not have predecessors, assume left-linearity directly.

The flags of a left-linear order, mathlib's maximal chains, behave like the branches of a tree:
a flag through an element contains its entire past (`Flag.Iic_subset`), the down-set of a maximal
element is a flag (`Flag.ofIsMax`), and on a finite order every flag arises this way
(`Flag.exists_isMax_eq_ofIsMax`), which turns quantification over flags into quantification over
maximal elements (`Flag.forall_mem_iff`) and so makes it decidable.

## Main definitions

* `IsLeftLinear M`: the predecessors of every element are linearly ordered.
* `Flag.ofIsMax`: the down-set of a maximal element, as a flag.

## Main results

* `IsLeftLinear.isChain_Iic`, `IsLeftLinear.isChain_Iio`: every principal down-set is a chain.
* `Flag.exists_mem_gt_of_lt`: a flag cannot stop at an element with a strict successor; this
  holds in any order.
* `Flag.exists_isMax_eq_ofIsMax`, `Flag.forall_mem_iff`: on a finite left-linear order the
  flags are the down-sets of the maximal elements.
-/

@[expose] public section

/-- A partial order is **left-linear** when the predecessors of every element are linearly
ordered, so that it never branches backward. -/
class IsLeftLinear (M : Type*) [PartialOrder M] : Prop where
  /-- The predecessors of any element are pairwise comparable. -/
  comparable_of_le_common : ∀ ⦃a b c : M⦄, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a

/-- A linear order is left-linear. -/
instance (priority := 100) {M : Type*} [LinearOrder M] : IsLeftLinear M :=
  ⟨fun a b _ _ _ ↦ le_total a b⟩

/-- A `PredOrder` with archimedean predecessor, such as a rooted tree, is left-linear. -/
instance (priority := 100) {M : Type*} [PartialOrder M] [PredOrder M] [IsPredArchimedean M] :
    IsLeftLinear M :=
  ⟨fun _ _ _ ha hb ↦ (le_total_of_directed ha hb).symm⟩

/-- Left-linearity pulls back along an order embedding. -/
theorem OrderEmbedding.isLeftLinear {M N : Type*} [PartialOrder M] [PartialOrder N]
    [IsLeftLinear N] (f : M ↪o N) : IsLeftLinear M :=
  ⟨fun _ _ _ ha hb ↦ (IsLeftLinear.comparable_of_le_common (f.monotone ha)
    (f.monotone hb)).imp f.le_iff_le.1 f.le_iff_le.1⟩

namespace IsLeftLinear

variable {M : Type*} [PartialOrder M] [IsLeftLinear M]

/-- In a left-linear order the principal down-set `Iic m` is a chain. -/
theorem isChain_Iic (m : M) : IsChain (· ≤ ·) (Set.Iic m) := by
  intro a ha b hb _
  exact comparable_of_le_common (Set.mem_Iic.mp ha) (Set.mem_Iic.mp hb)

/-- In a left-linear order the strict down-set `Iio m` is a chain. -/
theorem isChain_Iio (m : M) : IsChain (· ≤ ·) (Set.Iio m) := by
  intro a ha b hb _
  exact comparable_of_le_common (le_of_lt (Set.mem_Iio.mp ha)) (le_of_lt (Set.mem_Iio.mp hb))

end IsLeftLinear

/-! ### Flags

In a left-linear order a flag, mathlib's maximal chain, is a branch: it contains the whole
past of each of its elements, and when the order is finite it is the down-set of a maximal
element. -/

/-- Maximality is decidable on a finite type. -/
instance {M : Type*} [PartialOrder M] [Fintype M] [DecidableLE M] (x : M) :
    Decidable (IsMax x) :=
  decidable_of_iff (∀ b, x ≤ b → b ≤ x) Iff.rfl

namespace Flag

variable {M : Type*} [PartialOrder M] {m x y : M} {h : Flag M}

/-- A flag through a non-maximal element contains a strictly larger one; otherwise inserting
the successor would extend the chain. -/
theorem exists_mem_gt_of_lt (hm : m ∈ h) (hx : m < x) : ∃ y ∈ h, m < y := by
  by_contra! hcon
  have hxh : x ∈ h := mem_iff_forall_le_or_ge.2 fun b hb ↦ .inr <|
    (h.le_or_le hb hm).elim (fun hbm ↦ hbm.trans hx.le) fun hmb ↦
      (hmb.lt_or_eq.resolve_left (hcon b hb)) ▸ hx.le
  exact hcon x hxh hx

variable [IsLeftLinear M]

/-- In a left-linear order a flag contains the entire past of each of its elements. -/
theorem Iic_subset (hm : m ∈ h) : Set.Iic m ⊆ (h : Set M) := fun _ hx ↦
  mem_iff_forall_le_or_ge.2 fun _ hb ↦ (h.le_or_le hb hm).elim
    (fun hbm ↦ IsLeftLinear.comparable_of_le_common hx hbm) fun hmb ↦ .inl (hx.trans hmb)

/-- The down-set of a maximal element of a left-linear order, as a flag. -/
def ofIsMax (hx : IsMax x) : Flag M where
  carrier := Set.Iic x
  Chain' := IsLeftLinear.isChain_Iic x
  max_chain' := fun _ hc hsub ↦ hsub.antisymm fun _ hy ↦
    (hc.total (hsub (Set.mem_Iic.2 le_rfl)) hy).elim (fun h ↦ hx h) id

@[simp] theorem mem_ofIsMax {hx : IsMax x} : y ∈ ofIsMax hx ↔ y ≤ x := Iff.rfl

/-- A flag through a maximal element is its down-set. -/
theorem eq_ofIsMax_of_mem (hx : IsMax x) (hxh : x ∈ h) : h = ofIsMax hx :=
  Flag.ext (Set.ext fun _ ↦ ⟨fun hy ↦ (h.le_or_le hy hxh).elim id fun hxy ↦ hx hxy,
    fun hy ↦ Iic_subset hxh hy⟩)

variable [Finite M]

/-- On a finite left-linear order every flag is the down-set of a maximal element, since the
flag has a greatest element, which a strict successor would contradict. -/
theorem exists_isMax_eq_ofIsMax [Nonempty M] (h : Flag M) :
    ∃ x, ∃ hx : IsMax x, h = ofIsMax hx := by
  obtain ⟨x, hx, hmax⟩ :=
    WellFounded.has_min (wellFounded_gt (α := M)) (h : Set M) (h.maxChain.nonempty_iff.1 ‹_›)
  refine ⟨x, fun y hxy ↦ ?_, eq_ofIsMax_of_mem _ hx⟩
  by_contra hyx
  obtain ⟨z, hz, hxz⟩ := exists_mem_gt_of_lt hx (lt_of_le_not_ge hxy hyx)
  exact hmax z hz hxz

/-- On a finite left-linear order, quantifying over the flags through an element is
quantifying over the maximal elements above it. -/
theorem forall_mem_iff [Nonempty M] {P : Flag M → Prop} :
    (∀ h : Flag M, m ∈ h → P h) ↔ ∀ x, ∀ hx : IsMax x, m ≤ x → P (ofIsMax hx) :=
  ⟨fun H x hx hmx ↦ H _ hmx, fun H h hm ↦ by
    obtain ⟨x, hx, rfl⟩ := exists_isMax_eq_ofIsMax h
    exact H x hx hm⟩

end Flag
