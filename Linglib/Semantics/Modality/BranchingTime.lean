import Linglib.Core.Order.LeftLinear
import Linglib.Semantics.Tense.Defs
import Mathlib.Order.Zorn
import Mathlib.Order.Directed
import Mathlib.Order.Preorder.Finite

/-!
# Branching time

This file defines the branching-time model of [prior-1967] and Thomason: an order-theoretic
tree of moments whose maximal chains are the histories, and the two classic postsemantics
over it. A branching-time structure is a left-linear (`Core.Order.IsLeftLinear`, no backward
branching) and downward-directed (`IsCodirectedOrder`, historically connected) partial order,
and its histories are mathlib `Flag`s. Peircean truth is at a moment, and future truth
requires settledness; Ockhamist truth is at a moment–history pair, and future truth is
history-relative, with settledness the quantifier over the histories through the moment. The
Ockhamist history parameter is not fixed by a context of utterance, since there is no actual
future; only the moment is, which is why settledness carries the felicity facts.

## Main definitions

* `IsBranchingTime`, `IsBranchingMeetTree` — the frame, and its form with branching points
  as meets.
* `Hist` — the histories through a moment; `flagOfMax` — the history below a maximal moment.
* `pPast`, `oAtom`, `oPast`, `oFut`, `oSettled`, `oSupervaluation` — the Peircean and
  Ockhamist operators.
* `IsInevitable` — settled future truth, the Peircean future.

## Main results

* `Iic_subset_of_mem` — the past sits inside every history through a moment, the payoff of
  left-linearity; `exists_mem_gt_of_lt` — a history cannot stop at a moment with a future.
* `oSettled_oAtom` — atomic propositions are settled.
* `isInevitable_iff_oSupervaluation_oFut` — the Peircean future is the Ockhamist settled future.
* `exists_isMax_eq_flagOfMax`, `forall_hist_iff`, `isInevitable_iff` — on a finite frame every
  history is the down-set of a maximal moment, so settledness is decidable.

## References

* [prior-1967]
* [rumberg-lauer-2023]
-/

namespace BranchingTime

variable {M : Type*}

/-! ### The frame -/

/-- A branching-time structure: a left-linear, downward-directed partial order. Left-linearity
is no backward branching; downward-directedness is historical connectedness. -/
class IsBranchingTime (M : Type*) [PartialOrder M] : Prop
    extends IsLeftLinear M, IsCodirectedOrder M

/-- The meet-tree form: branching points exist as meets, `m₁ ⊓ m₂` being the moment where the
histories of `m₁` and `m₂` diverge. -/
class IsBranchingMeetTree (M : Type*) [SemilatticeInf M] : Prop
    extends IsLeftLinear M

/-! ### Histories -/

/-- The histories through a moment: the maximal chains containing it. -/
def Hist [PartialOrder M] (m : M) : Set (Flag M) := {h | m ∈ h}

/-- Every moment lies on a history. -/
theorem hist_nonempty [PartialOrder M] (m : M) : (Hist m).Nonempty :=
  let ⟨s, hs⟩ := Flag.exists_mem m; ⟨s, hs⟩

/-- The past of a moment sits inside every history through it: `Iic m` is a chain by
left-linearity, so it extends the maximal chain `h` and is therefore contained in it. -/
theorem Iic_subset_of_mem [PartialOrder M] [IsLeftLinear M] {m : M} {h : Flag M}
    (hm : m ∈ h) : Set.Iic m ⊆ (h : Set M) := by
  have hchain : IsChain (· ≤ ·) ((h : Set M) ∪ Set.Iic m) := by
    rintro a (ha | ha) b (hb | hb) _
    · exact h.le_or_le ha hb
    · rcases h.le_or_le ha hm with hab | hma
      · exact IsLeftLinear.comparable_of_le_common hab (Set.mem_Iic.mp hb)
      · exact Or.inr (le_trans (Set.mem_Iic.mp hb) hma)
    · rcases h.le_or_le hm hb with hmb | hbm
      · exact Or.inl (le_trans (Set.mem_Iic.mp ha) hmb)
      · exact IsLeftLinear.comparable_of_le_common (Set.mem_Iic.mp ha) hbm
    · exact IsLeftLinear.comparable_of_le_common (Set.mem_Iic.mp ha) (Set.mem_Iic.mp hb)
  have heq : (h : Set M) = (h : Set M) ∪ Set.Iic m := h.max_chain' hchain Set.subset_union_left
  intro x hx
  have hmem : x ∈ (h : Set M) ∪ Set.Iic m := Or.inr hx
  rwa [← heq] at hmem

/-- A history through a non-maximal moment contains a later moment: otherwise inserting a
successor would give a strictly larger chain. -/
theorem exists_mem_gt_of_lt [PartialOrder M] {m x : M} {h : Flag M}
    (hm : m ∈ h) (hx : m < x) : ∃ y ∈ h, m < y := by
  by_contra hcon
  push Not at hcon
  have hbx : ∀ b ∈ (h : Set M), b ≤ x := by
    intro b hb
    rcases h.le_or_le hb hm with hbm | hmb
    · exact le_of_lt (lt_of_le_of_lt hbm hx)
    · have hbeq : m = b := (hmb.lt_or_eq).resolve_left (hcon b hb)
      exact le_of_lt (hbeq ▸ hx)
  have hchain : IsChain (· ≤ ·) (insert x (h : Set M)) := by
    rintro a ha b hb _
    simp only [Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact Or.inl le_rfl
    · exact Or.inr (hbx b hb)
    · exact Or.inl (hbx a ha)
    · exact h.le_or_le ha hb
  have heq : (h : Set M) = insert x (h : Set M) := h.max_chain' hchain (Set.subset_insert x _)
  have hxh : x ∈ (h : Set M) := by rw [heq]; exact Set.mem_insert x _
  exact hcon x hxh hx

/-! ### Postsemantics

`MProp` is truth at a moment (Peircean); `OProp` is truth at a moment–history pair
(Ockhamist, intended `m ∈ h`). Atomic propositions depend only on the moment. -/

/-- A Peircean proposition: truth at a moment. -/
abbrev MProp (M : Type*) := M → Prop

/-- An Ockhamist proposition: truth at a moment–history pair. -/
abbrev OProp (M : Type*) [PartialOrder M] := M → Flag M → Prop

/-- Peircean past: `φ` held at some earlier moment. -/
def pPast [PartialOrder M] (φ : MProp M) : MProp M := λ m => ∃ m' < m, φ m'

/-- Lift a moment-proposition to an Ockhamist one, ignoring the history. -/
def oAtom [PartialOrder M] (φ : MProp M) : OProp M := λ m _h => φ m

/-- Ockhamist past: `φ` held at some earlier moment, along the same history. -/
def oPast [PartialOrder M] (φ : OProp M) : OProp M := λ m h => ∃ m' < m, φ m' h

/-- Ockhamist future: `φ` holds at some later moment on the fixed history. -/
def oFut [PartialOrder M] (φ : OProp M) : OProp M :=
  λ m h => ∃ m' ∈ h, m < m' ∧ φ m' h

/-- Ockhamist settledness: `φ` holds at `m` on every history through `m`. The history argument
is ignored, since settledness quantifies the unfixed history parameter away. -/
def oSettled [PartialOrder M] (φ : OProp M) : OProp M :=
  λ m _h => ∀ h' ∈ Hist m, φ m h'

/-- Supervaluationist truth at a moment: settledness read off the moment. -/
def oSupervaluation [PartialOrder M] (φ : OProp M) : MProp M :=
  λ m => ∀ h ∈ Hist m, φ m h

/-- A future-directed claim `φ` is inevitable at `m`: on every history through `m`, `φ`
eventually holds. This is the Peircean future. -/
def IsInevitable [PartialOrder M] (φ : MProp M) (m : M) : Prop :=
  ∀ h ∈ Hist m, ∃ m' ∈ h, m < m' ∧ φ m'

/-! ### Theorems -/

/-- Atomic propositions are settled: the valuation depends only on the moment. -/
@[simp] theorem oSettled_oAtom [PartialOrder M] (φ : MProp M) (m : M) (h : Flag M) :
    oSettled (oAtom φ) m h ↔ φ m := by
  unfold oSettled oAtom
  refine ⟨λ hall => ?_, λ hφ _ _ => hφ⟩
  obtain ⟨h', hh'⟩ := hist_nonempty m
  exact hall h' hh'

/-- The Peircean future is the Ockhamist settled future read off the moment. -/
theorem isInevitable_iff_oSupervaluation_oFut [PartialOrder M] (φ : MProp M) (m : M) :
    IsInevitable φ m ↔ oSupervaluation (oFut (oAtom φ)) m := Iff.rfl

/-! ### Grounding in the library's tense cells

The Ockhamist past and future operators land in the same comparison cells as the rest of the
library's tense (`Tense.past`, `Tense.future`): `oPast`'s witness compares into `Tense.past`
against the evaluation moment and `oFut`'s into `Tense.future`. These are the linear-frame
reductions; on a genuinely branching frame the comparison lives on each history's chain order
(`oFut_oAtom_holds_on_hist`). -/

@[simp] theorem oPast_oAtom_iff_holds {M : Type*} [LinearOrder M]
    (φ : MProp M) (m : M) (h : Flag M) :
    oPast (oAtom φ) m h ↔ ∃ m', compare m' m ∈ Tense.past ∧ φ m' := by
  simp only [oPast, oAtom, Tense.compare_mem_past]

@[simp] theorem oFut_oAtom_iff_holds {M : Type*} [LinearOrder M]
    (φ : MProp M) (m : M) (h : Flag M) :
    oFut (oAtom φ) m h ↔ ∃ m' ∈ h, compare m' m ∈ Tense.future ∧ φ m' := by
  simp only [oFut, oAtom, Tense.compare_mem_future]

/-- The Ockhamist future along a history is the tense-cell future over the history's own chain
order, mathlib's `LinearOrder ↥h` for a maximal chain. -/
theorem oFut_oAtom_holds_on_hist {M : Type*} [PartialOrder M]
    [DecidableEq M] [DecidableRel (· ≤ · : M → M → Prop)] [DecidableLT M]
    (φ : MProp M) {m : M} {h : Flag M} (hm : m ∈ h) :
    oFut (oAtom φ) m h ↔ ∃ x : ↥h, compare x ⟨m, hm⟩ ∈ Tense.future ∧ φ (x : M) := by
  simp only [oFut, oAtom, Tense.compare_mem_future]
  constructor
  · rintro ⟨m', hm', hlt, hφ⟩
    exact ⟨⟨m', hm'⟩, hlt, hφ⟩
  · rintro ⟨x, hlt, hφ⟩
    exact ⟨x, x.2, hlt, hφ⟩

/-! ### Finite frames

On a finite frame every history is the down-set of a maximal moment, so quantifying over the
histories through a moment is quantifying over the maximal moments above it, and settledness
is decidable. -/

section Finite

variable [PartialOrder M] [IsLeftLinear M]

/-- The history below a maximal moment: its down-set, a chain by left-linearity, which no
chain properly extends. -/
def flagOfMax (x : M) (hx : IsMax x) : Flag M where
  carrier := Set.Iic x
  Chain' := IsLeftLinear.isChain_Iic x
  max_chain' := λ _ hc hsub => hsub.antisymm λ _ hy =>
    (hc.total (hsub (Set.mem_Iic.2 le_rfl)) hy).elim (λ h => hx h) id

@[simp] theorem mem_flagOfMax {x y : M} (hx : IsMax x) : y ∈ flagOfMax x hx ↔ y ≤ x := Iff.rfl

variable [Finite M] [Nonempty M]

/-- On a finite frame every history is the down-set of its greatest moment, which is maximal:
a finite chain has a greatest element, the past of that element lies in the history, and a
successor of it would extend the history. -/
theorem exists_isMax_eq_flagOfMax (h : Flag M) : ∃ x, ∃ hx : IsMax x, h = flagOfMax x hx := by
  obtain ⟨x, hx, hmax⟩ :=
    WellFounded.has_min (wellFounded_gt (α := M)) (h : Set M) (h.maxChain.nonempty_iff.1 ‹_›)
  have hx' : IsMax x := λ y hxy => by
    by_contra hyx
    obtain ⟨z, hz, hxz⟩ := exists_mem_gt_of_lt hx (lt_of_le_not_ge hxy hyx)
    exact hmax z hz hxz
  refine ⟨x, hx', Flag.ext (Set.ext λ y => ⟨λ hy => ?_, λ hy => Iic_subset_of_mem hx hy⟩)⟩
  exact (h.le_or_le hy hx).elim id λ hxy => hx' hxy

/-- Quantifying over the histories through `m` is quantifying over the maximal moments
above `m`. -/
theorem forall_hist_iff {m : M} {P : Flag M → Prop} :
    (∀ h ∈ Hist m, P h) ↔ ∀ x, ∀ hx : IsMax x, m ≤ x → P (flagOfMax x hx) :=
  ⟨λ H x hx hmx => H _ hmx, λ H h hm => by
    obtain ⟨x, hx, rfl⟩ := exists_isMax_eq_flagOfMax h
    exact H x hx hm⟩

/-- Inevitability on a finite frame: below every maximal moment above `m` there is a later
`φ`-moment. -/
theorem isInevitable_iff (φ : MProp M) (m : M) :
    IsInevitable φ m ↔ ∀ x, IsMax x → m ≤ x → ∃ m', m < m' ∧ m' ≤ x ∧ φ m' := by
  rw [IsInevitable, forall_hist_iff]
  exact forall_congr' λ x => forall_congr' λ _ => imp_congr_right λ _ =>
    ⟨λ ⟨m', hm', hlt, hφ⟩ => ⟨m', hlt, hm', hφ⟩, λ ⟨m', hlt, hm', hφ⟩ => ⟨m', hm', hlt, hφ⟩⟩

end Finite

/-- Maximality is decidable on a finite frame. -/
instance [PartialOrder M] [Fintype M] [DecidableRel (· ≤ · : M → M → Prop)] (x : M) :
    Decidable (IsMax x) :=
  decidable_of_iff (∀ b, x ≤ b → b ≤ x) Iff.rfl

instance [PartialOrder M] [IsLeftLinear M] [Fintype M] [DecidableEq M]
    [DecidableRel (· ≤ · : M → M → Prop)] [DecidableLT M] (φ : MProp M) [DecidablePred φ]
    (m : M) : Decidable (IsInevitable φ m) :=
  haveI : Nonempty M := ⟨m⟩
  decidable_of_iff _ (isInevitable_iff φ m).symm

end BranchingTime
