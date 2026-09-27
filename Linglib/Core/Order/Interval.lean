module

public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Interval.Basic

/-!
# Relations between intervals

This file defines the relations between two nonempty intervals of an ordered type that mathlib's
`NonemptyInterval` API leaves implicit, and their counterparts on `Interval`, the intervals with
a null element. Two intervals overlap when neither lies strictly beyond the other, `i₁` precedes
`i₂` when it ends strictly before `i₂` starts, and the weak forms `isBefore` and `isAfter` let the
endpoints touch. `during`, `finalSubinterval` and `initialOverlap` refine containment, and
`IsPoint` singles out the intervals with a single element. In a linear order two intervals occupy
exactly one of three positions, precedence either way or overlap, and `position` records which as
an `Ordering`, so that on point intervals it is `compare`; the finer classification into Allen's
thirteen relations is in `Core/Order/AllenRelation.lean`.

Containment, the subinterval order and point intervals are mathlib's own: `t ∈ i` (`mem_def`),
`i₁ ≤ i₂` (`le_def`), `i₁ < i₂` (`lt_def`) and `pure t`. On `Interval α`, where `≤` is inclusion
and `⊓` intersection, `Interval.Precedes` is Allen's *before* stated pointwise, a left endpoint is
`IsLeast` of the coerced set, `NonemptyInterval.withTop` embeds a bounded interval into
`WithTop α`, and `Interval.Ici a` is the ray `[a, ⊤]`.

## Main definitions

* `NonemptyInterval.overlaps`, `NonemptyInterval.precedes`, `NonemptyInterval.isBefore`,
  `NonemptyInterval.isAfter`: the order of two intervals.
* `NonemptyInterval.during`, `NonemptyInterval.finalSubinterval`,
  `NonemptyInterval.initialOverlap`: refinements of containment.
* `NonemptyInterval.position`: the position of two intervals in a linear order as an `Ordering`.
* `Interval.Precedes`, `Interval.Ici`: pointwise precedence and rays on intervals with a null
  element.

## References

* [allen-1983]
-/

@[expose] public section

namespace NonemptyInterval

/-! ### Relations between intervals -/

section LE

variable {α : Type*} [LE α] {i₁ i₂ : NonemptyInterval α}

/-- Two intervals overlap when neither lies strictly beyond the other. -/
def overlaps (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁.fst ≤ i₂.snd ∧ i₂.fst ≤ i₁.snd

/-- An interval is a point when its endpoints coincide. -/
def IsPoint (i : NonemptyInterval α) : Prop :=
  i.fst = i.snd

/-- `i₁` is after `i₂` when `i₁` starts at or after `i₂` ends. -/
def isAfter (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₂.snd ≤ i₁.fst

/-- `i₁` is before `i₂` when `i₁` ends at or before `i₂` starts. -/
def isBefore (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁.snd ≤ i₂.fst

/-- `i₁` is a final subinterval of `i₂` when it lies within `i₂` and shares its right endpoint. -/
def finalSubinterval (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁ ≤ i₂ ∧ i₁.snd = i₂.snd

theorem isAfter_iff_isBefore (i₁ i₂ : NonemptyInterval α) : i₁.isAfter i₂ ↔ i₂.isBefore i₁ :=
  Iff.rfl

section Decidability

variable [DecidableLE α] [DecidableEq α]

instance : Decidable (i₁.overlaps i₂) := inferInstanceAs (Decidable (_ ∧ _))
instance {i : NonemptyInterval α} : Decidable i.IsPoint := inferInstanceAs (Decidable (_ = _))
instance : Decidable (i₁.isAfter i₂) := inferInstanceAs (Decidable (_ ≤ _))
instance : Decidable (i₁.isBefore i₂) := inferInstanceAs (Decidable (_ ≤ _))
instance : Decidable (i₁.finalSubinterval i₂) := inferInstanceAs (Decidable (_ ∧ _))

end Decidability

@[simp] theorem overlaps_refl (i : NonemptyInterval α) : i.overlaps i :=
  ⟨i.fst_le_snd, i.fst_le_snd⟩

theorem overlaps_symm (h : i₁.overlaps i₂) : i₂.overlaps i₁ :=
  ⟨h.2, h.1⟩

theorem overlaps_comm (i₁ i₂ : NonemptyInterval α) : i₁.overlaps i₂ ↔ i₂.overlaps i₁ :=
  ⟨overlaps_symm, overlaps_symm⟩

end LE

section Preorder

variable {α : Type*} [Preorder α] {i₁ i₂ : NonemptyInterval α}

instance {a : α} {s : NonemptyInterval α} [DecidableLE α] : Decidable (a ∈ s) :=
  decidable_of_iff' _ mem_def

instance {s t : NonemptyInterval α} [DecidableLE α] : Decidable (s < t) :=
  decidable_of_iff' _ lt_iff_le_not_ge

/-- `i₁` precedes `i₂` when `i₁` ends strictly before `i₂` starts. -/
def precedes (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁.snd < i₂.fst

/-- `i₁` initially overlaps `i₂` when the two overlap and `i₂` starts within `i₁`. -/
def initialOverlap (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁.overlaps i₂ ∧ i₂.fst ∈ i₁

/-- `i₁` lies during `i₂` when it is strictly inside `i₂` on both sides. -/
def during (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₂.fst < i₁.fst ∧ i₁.snd < i₂.snd

instance [DecidableLE α] : Decidable (i₁.initialOverlap i₂) := inferInstanceAs (Decidable (_ ∧ _))

instance [DecidableLE α] : Decidable (i₁.precedes i₂) :=
  decidable_of_iff' _ lt_iff_le_not_ge

instance [DecidableLE α] : Decidable (i₁.during i₂) :=
  @instDecidableAnd _ _ (decidable_of_iff' _ lt_iff_le_not_ge)
    (decidable_of_iff' _ lt_iff_le_not_ge)

theorem during_irrefl (i : NonemptyInterval α) : ¬ i.during i := fun h ↦ lt_irrefl _ h.1

theorem during_asymm (h : i₁.during i₂) : ¬ i₂.during i₁ := fun h' ↦ lt_asymm h.1 h'.1

theorem during_trans {i₃ : NonemptyInterval α} (h₁ : i₁.during i₂) (h₂ : i₂.during i₃) :
    i₁.during i₃ :=
  ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

/-- An interval during another neither precedes nor follows it. -/
theorem not_precedes_of_during (h : i₁.during i₂) : ¬ i₁.precedes i₂ ∧ ¬ i₂.precedes i₁ :=
  ⟨fun h' ↦ lt_irrefl _ ((h.1.trans_le i₁.fst_le_snd).trans h'),
   fun h' ↦ lt_irrefl _ ((i₁.fst_le_snd.trans_lt h.2).trans h')⟩

@[simp] theorem finalSubinterval_refl (i : NonemptyInterval α) : i.finalSubinterval i :=
  ⟨le_refl i, rfl⟩

/-- Subintervals overlap their containing intervals. -/
theorem overlaps_of_le (h : i₁ ≤ i₂) : i₁.overlaps i₂ :=
  ⟨i₁.fst_le_snd.trans (le_def.1 h).2, (le_def.1 h).1.trans i₁.fst_le_snd⟩

theorem precedes_irrefl (i : NonemptyInterval α) : ¬ i.precedes i :=
  fun h ↦ absurd i.fst_le_snd (not_le_of_gt h)

theorem precedes_asymm (h : i₁.precedes i₂) : ¬ i₂.precedes i₁ :=
  fun h' ↦ absurd (i₂.fst_le_snd.trans (h'.le.trans i₁.fst_le_snd)) (not_le_of_gt h)

theorem precedes_trans {i₃ : NonemptyInterval α} (h₁₂ : i₁.precedes i₂) (h₂₃ : i₂.precedes i₃) :
    i₁.precedes i₃ :=
  (h₁₂.trans_le i₂.fst_le_snd).trans h₂₃

/-- Precedence and overlap are mutually exclusive. -/
theorem precedes_not_overlaps (h : i₁.precedes i₂) : ¬ i₁.overlaps i₂ :=
  fun ⟨_, h₂⟩ ↦ lt_irrefl _ (h.trans_le h₂)

end Preorder

section LinearOrder

variable {α : Type*} [LinearOrder α] {i₁ i₂ : NonemptyInterval α}

/-- Strict containment unfolded to endpoints, `i₁ ≤ i₂` with a strictly interior endpoint. -/
theorem lt_def : i₁ < i₂ ↔ i₁ ≤ i₂ ∧ (i₂.fst < i₁.fst ∨ i₁.snd < i₂.snd) := by
  rw [lt_iff_le_not_ge]
  exact and_congr_right' (by rw [le_def, not_and_or, not_le, not_le])

/-- An interval containing an overlapping interval overlaps. -/
theorem overlaps.mono_left {i₁' : NonemptyInterval α} (h : i₁.overlaps i₂) (hle : i₁ ≤ i₁') :
    i₁'.overlaps i₂ :=
  ⟨(le_def.1 hle).1.trans h.1, h.2.trans (le_def.1 hle).2⟩

/-- In a linear order two intervals overlap exactly when neither precedes the other. -/
theorem overlaps_iff_not_precedes : i₁.overlaps i₂ ↔ ¬ i₁.precedes i₂ ∧ ¬ i₂.precedes i₁ := by
  simp only [overlaps, precedes, not_lt, and_comm]

/-! ### Relative position

In a linear order two intervals stand in exactly one of three positions: the first precedes the
second, the second precedes the first, or they overlap. `position` records which as an
`Ordering`, so that a set of admissible positions is a `Finset Ordering`, as a set of admissible
comparisons of points is; on point intervals it is `compare`. -/

/-- The position of `i₁` relative to `i₂` is `lt` when `i₁` precedes `i₂`, `gt` when `i₂`
precedes `i₁`, and `eq` when the two overlap. -/
def position (i₁ i₂ : NonemptyInterval α) : Ordering :=
  if i₁.precedes i₂ then .lt else if i₂.precedes i₁ then .gt else .eq

@[simp] theorem position_eq_lt : i₁.position i₂ = .lt ↔ i₁.precedes i₂ := by
  unfold position; split_ifs <;> simp [*]

@[simp] theorem position_eq_gt : i₁.position i₂ = .gt ↔ i₂.precedes i₁ := by
  unfold position
  split_ifs with h h'
  · simp [precedes_asymm h]
  · simp [h']
  · simp [h']

@[simp] theorem position_eq_eq : i₁.position i₂ = .eq ↔ i₁.overlaps i₂ := by
  rw [overlaps_iff_not_precedes]; unfold position; split_ifs <;> simp [*]

@[simp] theorem position_self (i : NonemptyInterval α) : i.position i = .eq :=
  position_eq_eq.2 (overlaps_refl i)

theorem swap_position (i₁ i₂ : NonemptyInterval α) : (i₁.position i₂).swap = i₂.position i₁ := by
  rcases h : i₂.position i₁ with _ | _ | _
  · rw [Ordering.swap_eq_lt, position_eq_gt, ← position_eq_lt, h]
  · rw [Ordering.swap_eq_eq, position_eq_eq, overlaps_comm, ← position_eq_eq, h]
  · rw [Ordering.swap_eq_gt, position_eq_lt, ← position_eq_gt, h]

/-- On point intervals the position is the comparison of the points. -/
@[simp] theorem position_pure (a b : α) : (pure a).position (pure b) = compare a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [position_eq_lt.2 (by exact h), compare_lt_iff_lt.2 h]
  · rw [position_self, compare_eq_iff_eq.2 rfl]
  · rw [position_eq_gt.2 (by exact h), compare_gt_iff_gt.2 h]

/-- An interval containing one that overlaps `i₂` overlaps `i₂`. -/
theorem position_eq_eq_of_le {i₁' : NonemptyInterval α} (h : i₁.position i₂ = .eq)
    (hle : i₁ ≤ i₁') : i₁'.position i₂ = .eq :=
  position_eq_eq.2 ((position_eq_eq.1 h).mono_left hle)

end LinearOrder

/-! ### Embedding into `WithTop` -/

section WithTop

variable {α : Type*} [Preorder α]

/-- An interval of `α` as an interval of `WithTop α`. -/
def withTop (i : NonemptyInterval α) : NonemptyInterval (WithTop α) :=
  i.map WithTop.coeOrderHom.toOrderHom

@[simp] theorem fst_withTop (i : NonemptyInterval α) : i.withTop.fst = ↑i.fst := rfl

@[simp] theorem snd_withTop (i : NonemptyInterval α) : i.withTop.snd = ↑i.snd := rfl

@[simp] theorem mem_withTop {i : NonemptyInterval α} {x : WithTop α} :
    x ∈ i.withTop ↔ ↑i.fst ≤ x ∧ x ≤ ↑i.snd :=
  Iff.rfl

/-- The embedding preserves and reflects containment. -/
@[simp] theorem withTop_le_withTop {i j : NonemptyInterval α} : i.withTop ≤ j.withTop ↔ i ≤ j := by
  simp [le_def]

end WithTop

end NonemptyInterval

/-! ### Intervals with a null element -/

namespace Interval

section PartialOrder

variable {α : Type*} [PartialOrder α] {s t : Interval α} {i j : NonemptyInterval α} {a b x : α}

/-- `s` precedes `t` when every element of `s` is below every element of `t`, Allen's *before*
stated pointwise, vacuously so at the null interval. -/
def Precedes (s t : Interval α) : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ t → x < y

@[simp] theorem notMem_bot : x ∉ (⊥ : Interval α) := by
  simp [← SetLike.mem_coe]

/-- A nonempty interval lies within `s` exactly when its endpoints do. -/
theorem coe_le_iff : (↑i : Interval α) ≤ s ↔ i.fst ∈ s ∧ i.snd ∈ s := by
  induction s using recBotCoe with
  | bot =>
    exact iff_of_false (fun h ↦ WithBot.coe_ne_bot (le_bot_iff.1 h)) (fun h ↦ notMem_bot h.1)
  | coe j =>
    refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ WithBot.coe_le_coe.2 (NonemptyInterval.le_def.2
      ⟨(NonemptyInterval.mem_def.1 h₁).1, (NonemptyInterval.mem_def.1 h₂).2⟩)⟩
    obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 (WithBot.coe_le_coe.1 h)
    exact ⟨NonemptyInterval.mem_def.2 ⟨h₁, i.fst_le_snd.trans h₂⟩,
      NonemptyInterval.mem_def.2 ⟨h₁.trans i.fst_le_snd, h₂⟩⟩

@[simp] theorem pure_le_iff : pure a ≤ s ↔ a ∈ s := by
  simp [← coe_subset_coe]

/-- The left endpoint is the least element. -/
theorem isLeast_coe_fst : IsLeast (↑(↑i : Interval α) : Set α) i.fst :=
  ⟨NonemptyInterval.mem_def.2 ⟨le_rfl, i.fst_le_snd⟩,
    fun _ hx ↦ (NonemptyInterval.mem_def.1 hx).1⟩

theorem isLeast_pure : IsLeast (↑(pure a : Interval α) : Set α) a := isLeast_coe_fst

/-- Nonempty intervals precede exactly when the one ends before the other starts, the
endpoint form of the relation. -/
theorem precedes_coe_coe : (↑i : Interval α).Precedes ↑j ↔ i.precedes j :=
  ⟨fun h ↦ h (NonemptyInterval.mem_def.2 ⟨i.fst_le_snd, le_rfl⟩)
      (NonemptyInterval.mem_def.2 ⟨le_rfl, j.fst_le_snd⟩),
    fun h _ hx _ hy ↦ (NonemptyInterval.mem_def.1 hx).2.trans_lt
      (h.trans_le (NonemptyInterval.mem_def.1 hy).1)⟩

@[simp] theorem precedes_pure_pure : (pure a).Precedes (pure b) ↔ a < b := precedes_coe_coe

end PartialOrder

section Lattice

variable {α : Type*} [Lattice α] {s t : Interval α} {x : α}

theorem not_disjoint_iff : ¬ Disjoint s t ↔ ∃ x, x ∈ s ∧ x ∈ t := by
  simp only [← disjoint_coe, Set.not_disjoint_iff, SetLike.mem_coe]

/-- Nonempty intervals meet exactly when they overlap, the endpoint form of the relation. -/
theorem not_disjoint_coe_coe {i j : NonemptyInterval α} :
    ¬ Disjoint (↑i : Interval α) ↑j ↔ i.overlaps j := by
  rw [not_disjoint_iff]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨(NonemptyInterval.mem_def.1 hx).1.trans (NonemptyInterval.mem_def.1 hy).2,
      (NonemptyInterval.mem_def.1 hy).1.trans (NonemptyInterval.mem_def.1 hx).2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨i.fst ⊔ j.fst, NonemptyInterval.mem_def.2 ⟨le_sup_left, sup_le i.fst_le_snd h₂⟩,
      NonemptyInterval.mem_def.2 ⟨le_sup_right, sup_le h₁ j.fst_le_snd⟩⟩

variable [DecidableLE α]

@[simp] theorem mem_inf : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := by
  simp [← SetLike.mem_coe]

end Lattice

/-! ### Rays -/

section WithTop

variable {α : Type*} [PartialOrder α] {i : NonemptyInterval α} {a b : α} {x : WithTop α}

/-- The ray `[a, ⊤]` as an interval of `WithTop α`. -/
def Ici (a : α) : Interval (WithTop α) := ↑(⟨(↑a, ⊤), le_top⟩ : NonemptyInterval (WithTop α))

@[simp] theorem mem_Ici : x ∈ Ici a ↔ ↑a ≤ x := by
  simp [Ici, NonemptyInterval.mem_def]

@[simp] theorem Ici_le_Ici : Ici a ≤ Ici b ↔ b ≤ a := by
  simp [Ici, NonemptyInterval.le_def]

theorem antitone_Ici : Antitone (Ici : α → Interval (WithTop α)) := fun _ _ h ↦ Ici_le_Ici.2 h

theorem isLeast_Ici : IsLeast (↑(Ici a) : Set (WithTop α)) ↑a := isLeast_coe_fst

@[simp] theorem pure_le_Ici : pure (↑b : WithTop α) ≤ Ici a ↔ a ≤ b := by
  simp

/-- An interval lies within the ray from `a` exactly when all its elements are at or above `a`. -/
theorem le_Ici_iff {s : Interval (WithTop α)} : s ≤ Ici a ↔ ∀ x ∈ s, ↑a ≤ x := by
  simp [← coe_subset_coe, Set.subset_def]

/-- A bounded interval lies within the ray from `a` exactly when it starts at or above `a`. -/
theorem withTop_le_Ici : (↑i.withTop : Interval (WithTop α)) ≤ Ici a ↔ a ≤ i.fst := by
  simp only [coe_le_iff, NonemptyInterval.fst_withTop, NonemptyInterval.snd_withTop, mem_Ici,
    WithTop.coe_le_coe]
  exact ⟨And.left, fun h ↦ ⟨h, h.trans i.fst_le_snd⟩⟩

/-- A bounded interval precedes the ray from `a` exactly when it ends below `a`. -/
theorem precedes_withTop_Ici :
    (↑i.withTop : Interval (WithTop α)).Precedes (Ici a) ↔ i.snd < a := by
  rw [Ici, precedes_coe_coe]; simp [NonemptyInterval.precedes]

/-- A bounded interval precedes the point `a` exactly when it ends below `a`. -/
theorem precedes_withTop_pure :
    (↑i.withTop : Interval (WithTop α)).Precedes (pure ↑a) ↔ i.snd < a := by
  rw [pure, precedes_coe_coe]; simp [NonemptyInterval.precedes]

end WithTop

section WithTopLattice

variable {α : Type*} [Lattice α] {i : NonemptyInterval α} {a : α}

/-- A bounded interval meets the ray from `a` exactly when it ends at or above `a`. -/
theorem not_disjoint_withTop_Ici :
    ¬ Disjoint (↑i.withTop : Interval (WithTop α)) (Ici a) ↔ a ≤ i.snd := by
  rw [Ici, not_disjoint_coe_coe]; simp [NonemptyInterval.overlaps]

end WithTopLattice

end Interval
