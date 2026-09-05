import Mathlib.Order.Hom.WithTopBot
import Mathlib.Order.Interval.Basic

/-!
# Relational vocabulary for intervals

[allen-1983] [kamp-reyle-1993] [klein-1994]
[pancheva-2003] [sagey-1986] [smith-1997]

Extends mathlib's `NonemptyInterval` with the relational algebra
linguistic semantics consumes: overlap, precedence, meets, plus the
nuclear cluster needed by aspectual semantics (final subinterval,
initial overlap, isAfter/isBefore). Consumed as the time axis by tense,
aspect, and event semantics, and as the timing tier by autosegmental
phonology ([sagey-1986]).

Containment, the subinterval order, and point intervals are mathlib's
own API: `t ∈ i` (`mem_def`), `i₁ ≤ i₂` (`le_def`), `i₁ < i₂`
(strict containment, see `lt_def`), `pure t`.

The same vocabulary on mathlib's `Interval α`, the closed intervals with
the null interval `⊥`, where `≤` is inclusion and `⊓` intersection:
`Interval.Precedes` is [allen-1983]'s *before*, a left endpoint is
`IsLeast` of the coerced set, `NonemptyInterval.withTop` embeds a bounded
interval into `WithTop α`, and `Interval.Ici a` is the ray from `a` to the
end of time.
-/

namespace NonemptyInterval

/-! ### Relational vocabulary -/

section LE

variable {α : Type*} [LE α]

/-- Intervals overlap: neither lies strictly beyond the other. -/
def overlaps (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁.fst ≤ i₂.snd ∧ i₂.fst ≤ i₁.snd

/-- i₁ meets i₂ (i₁ ends exactly when i₂ starts). -/
def meets (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁.snd = i₂.fst

/-- An interval is a *point* iff its endpoints coincide.
    The atomic case in the time dimension — used by Bennett-Partee 1972
    strict subinterval property and Zhao 2025 ATOM-DIST_t at the atomic
    granularity. -/
def IsPoint (i : NonemptyInterval α) : Prop :=
  i.fst = i.snd

/-- i₁ is entirely after i₂ (i₁ starts at or after i₂ finishes). -/
def isAfter (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₂.snd ≤ i₁.fst

/-- i₁ is entirely before i₂. -/
def isBefore (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁.snd ≤ i₂.fst

/-- Final subinterval: i₁ ⊆ i₂ and they share the same right endpoint.
    [pancheva-2003]: PTS(i', i) iff i is a final subinterval of i'. -/
def finalSubinterval (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁ ≤ i₂ ∧ i₁.snd = i₂.snd

theorem isAfter_iff_isBefore (i₁ i₂ : NonemptyInterval α) :
    i₁.isAfter i₂ ↔ i₂.isBefore i₁ :=
  Iff.rfl

section Decidability

variable [DecidableLE α] [DecidableEq α] {i₁ i₂ : NonemptyInterval α}

instance : Decidable (i₁.overlaps i₂) := by unfold overlaps; infer_instance
instance : Decidable (i₁.meets i₂) := by unfold meets; infer_instance
instance {i : NonemptyInterval α} : Decidable i.IsPoint := by unfold IsPoint; infer_instance
instance : Decidable (i₁.isAfter i₂) := by unfold isAfter; infer_instance
instance : Decidable (i₁.isBefore i₂) := by unfold isBefore; infer_instance
instance : Decidable (i₁.finalSubinterval i₂) := by unfold finalSubinterval; infer_instance

end Decidability

/-- Final subintervals are subintervals. -/
theorem le_of_finalSubinterval {i₁ i₂ : NonemptyInterval α}
    (h : i₁.finalSubinterval i₂) : i₁ ≤ i₂ :=
  h.1

/-- Overlap is reflexive: every interval overlaps itself. -/
@[simp] theorem overlaps_refl (i : NonemptyInterval α) : i.overlaps i :=
  ⟨i.fst_le_snd, i.fst_le_snd⟩

/-- Overlap is symmetric. -/
theorem overlaps_symm {i₁ i₂ : NonemptyInterval α} (h : i₁.overlaps i₂) :
    i₂.overlaps i₁ :=
  ⟨h.2, h.1⟩

/-- Overlap is symmetric (iff version). -/
theorem overlaps_comm (i₁ i₂ : NonemptyInterval α) :
    i₁.overlaps i₂ ↔ i₂.overlaps i₁ :=
  ⟨overlaps_symm, overlaps_symm⟩

end LE

section Preorder

variable {α : Type*} [Preorder α]

/-- Membership in a nonempty interval is decidable when `≤` is. -/
instance {a : α} {s : NonemptyInterval α} [DecidableLE α] : Decidable (a ∈ s) :=
  decidable_of_iff' _ mem_def

/-- Strict containment is decidable when `≤` is. -/
instance {s t : NonemptyInterval α} [DecidableLE α] : Decidable (s < t) :=
  decidable_of_iff' _ lt_iff_le_not_ge

/-- i₁ precedes i₂ (no overlap, i₁ entirely before i₂). -/
def precedes (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁.snd < i₂.fst

/-- Initial overlap (∂): i₁ and i₂ overlap, and the start of i₂ is in i₁.
    [pancheva-2003]: i ∂τ(e) — the beginning of the eventuality is included
    in the reference interval but the end may not be.
    [smith-1997]: the neutral viewpoint uses the same interval relation. -/
def initialOverlap (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁.overlaps i₂ ∧ i₂.fst ∈ i₁

instance [DecidableLE α] {i₁ i₂ : NonemptyInterval α} : Decidable (i₁.initialOverlap i₂) := by
  unfold initialOverlap; infer_instance

instance [DecidableLE α] {i₁ i₂ : NonemptyInterval α} : Decidable (i₁.precedes i₂) := by
  unfold precedes
  exact decidable_of_iff' _ lt_iff_le_not_ge

/-- Every interval is a final subinterval of itself. -/
theorem finalSubinterval_refl (i : NonemptyInterval α) : i.finalSubinterval i :=
  ⟨le_refl i, rfl⟩

/-- Subintervals overlap their containing intervals. -/
theorem overlaps_of_le {i₁ i₂ : NonemptyInterval α}
    (h : i₁ ≤ i₂) : i₁.overlaps i₂ :=
  ⟨le_trans i₁.fst_le_snd (le_def.mp h).2, le_trans (le_def.mp h).1 i₁.fst_le_snd⟩

/-- Precedence is irreflexive: no interval precedes itself. -/
theorem precedes_irrefl (i : NonemptyInterval α) : ¬ i.precedes i :=
  fun h => absurd i.fst_le_snd (not_le_of_gt h)

/-- Precedence is asymmetric. -/
theorem precedes_asymm {i₁ i₂ : NonemptyInterval α}
    (h : i₁.precedes i₂) : ¬ i₂.precedes i₁ :=
  fun h' => absurd (le_trans i₂.fst_le_snd (le_trans (le_of_lt h') i₁.fst_le_snd))
    (not_le_of_gt h)

/-- Precedence is transitive. -/
theorem precedes_trans {i₁ i₂ i₃ : NonemptyInterval α}
    (h₁₂ : i₁.precedes i₂) (h₂₃ : i₂.precedes i₃) : i₁.precedes i₃ :=
  lt_trans (lt_of_lt_of_le h₁₂ i₂.fst_le_snd) h₂₃

/-- Precedence and overlap are mutually exclusive. -/
theorem precedes_not_overlaps {i₁ i₂ : NonemptyInterval α}
    (h : i₁.precedes i₂) : ¬ i₁.overlaps i₂ :=
  fun ⟨_, h₂⟩ => absurd (lt_of_lt_of_le h h₂) (lt_irrefl _)

end Preorder

section LinearOrder

variable {α : Type*} [LinearOrder α]

/-- Strict containment unfolded to endpoints: `i₁ < i₂` iff `i₁ ≤ i₂`
    with at least one strictly interior endpoint. The shape the IMPF
    semantics consumes (reference time PROPERLY inside event runtime). -/
theorem lt_def {i₁ i₂ : NonemptyInterval α} :
    i₁ < i₂ ↔ i₁ ≤ i₂ ∧ (i₂.fst < i₁.fst ∨ i₁.snd < i₂.snd) := by
  rw [lt_iff_le_not_ge]
  exact and_congr_right' (by rw [le_def, not_and_or, not_le, not_le])

/-- Overlap is NOT transitive: [0,1] overlaps [1,2] and [1,2] overlaps [2,3],
    but [0,1] does not overlap [2,3].

    This is the cornerstone property that distinguishes overlap from
    simultaneity (identity) and makes the No-Crossing Constraint derivable
    from temporal precedence alone ([sagey-1986] §5.2.3, fn. 6). -/
theorem overlaps_not_transitive :
    ¬ ∀ (i₁ i₂ i₃ : NonemptyInterval ℤ),
      i₁.overlaps i₂ → i₂.overlaps i₃ → i₁.overlaps i₃ := by
  intro h
  have := h ⟨⟨0, 1⟩, by omega⟩ ⟨⟨1, 2⟩, by omega⟩ ⟨⟨2, 3⟩, by omega⟩
    (by simp only [overlaps]; omega) (by simp only [overlaps]; omega)
  simp only [overlaps] at this
  omega

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

/-- `s` precedes `t`: every element of `s` is below every element of `t` ([allen-1983]'s
*before*), vacuously so at the null interval. -/
def Precedes (s t : Interval α) : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ t → x < y

@[simp] theorem notMem_bot : x ∉ (⊥ : Interval α) := by
  simp [← SetLike.mem_coe]

/-- A nonempty interval lies within `s` exactly when its endpoints do. -/
theorem coe_le_iff : (↑i : Interval α) ≤ s ↔ i.fst ∈ s ∧ i.snd ∈ s := by
  induction s using recBotCoe with
  | bot => exact iff_of_false (λ h => WithBot.coe_ne_bot (le_bot_iff.1 h)) (λ h => notMem_bot h.1)
  | coe j =>
    refine ⟨λ h => ?_, λ ⟨h₁, h₂⟩ => WithBot.coe_le_coe.2 (NonemptyInterval.le_def.2
      ⟨(NonemptyInterval.mem_def.1 h₁).1, (NonemptyInterval.mem_def.1 h₂).2⟩)⟩
    obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 (WithBot.coe_le_coe.1 h)
    exact ⟨NonemptyInterval.mem_def.2 ⟨h₁, le_trans i.fst_le_snd h₂⟩,
      NonemptyInterval.mem_def.2 ⟨le_trans h₁ i.fst_le_snd, h₂⟩⟩

@[simp] theorem pure_le_iff : pure a ≤ s ↔ a ∈ s := by
  simp [← coe_subset_coe]

/-- The left endpoint is the least element. -/
theorem isLeast_coe_fst : IsLeast (↑(↑i : Interval α) : Set α) i.fst :=
  ⟨NonemptyInterval.mem_def.2 ⟨le_rfl, i.fst_le_snd⟩, λ _ hx => (NonemptyInterval.mem_def.1 hx).1⟩

theorem isLeast_pure : IsLeast (↑(pure a : Interval α) : Set α) a := isLeast_coe_fst

/-- Nonempty intervals precede exactly when the one ends before the other starts, the
endpoint form of the relation. -/
theorem precedes_coe_coe : (↑i : Interval α).Precedes ↑j ↔ i.precedes j :=
  ⟨λ h => h (NonemptyInterval.mem_def.2 ⟨i.fst_le_snd, le_rfl⟩)
      (NonemptyInterval.mem_def.2 ⟨le_rfl, j.fst_le_snd⟩),
    λ h _ hx _ hy => lt_of_le_of_lt (NonemptyInterval.mem_def.1 hx).2
      (lt_of_lt_of_le h (NonemptyInterval.mem_def.1 hy).1)⟩

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
    exact ⟨le_trans (NonemptyInterval.mem_def.1 hx).1 (NonemptyInterval.mem_def.1 hy).2,
      le_trans (NonemptyInterval.mem_def.1 hy).1 (NonemptyInterval.mem_def.1 hx).2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨i.fst ⊔ j.fst, NonemptyInterval.mem_def.2 ⟨le_sup_left, sup_le i.fst_le_snd h₂⟩,
      NonemptyInterval.mem_def.2 ⟨le_sup_right, sup_le h₁ j.fst_le_snd⟩⟩

variable [DecidableLE α]

@[simp] theorem mem_inf : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := by
  simp [← SetLike.mem_coe]

end Lattice

/-! ### Rays to the end of time -/

section WithTop

variable {α : Type*} [PartialOrder α] {i : NonemptyInterval α} {a b : α} {x : WithTop α}

/-- The interval from `a` to the end of time, `[a, ⊤]`. -/
def Ici (a : α) : Interval (WithTop α) := ↑(⟨(↑a, ⊤), le_top⟩ : NonemptyInterval (WithTop α))

@[simp] theorem mem_Ici : x ∈ Ici a ↔ ↑a ≤ x := by
  simp [Ici, NonemptyInterval.mem_def]

@[simp] theorem Ici_le_Ici : Ici a ≤ Ici b ↔ b ≤ a := by
  simp [Ici, NonemptyInterval.le_def]

theorem antitone_Ici : Antitone (Ici : α → Interval (WithTop α)) := λ _ _ h => Ici_le_Ici.2 h

theorem isLeast_Ici : IsLeast (↑(Ici a) : Set (WithTop α)) ↑a := isLeast_coe_fst

@[simp] theorem pure_le_Ici : pure (↑b : WithTop α) ≤ Ici a ↔ a ≤ b := by
  simp

/-- An interval lies within the ray from `a` exactly when all its times are at or after `a`. -/
theorem le_Ici_iff {s : Interval (WithTop α)} : s ≤ Ici a ↔ ∀ x ∈ s, ↑a ≤ x := by
  simp [← coe_subset_coe, Set.subset_def]

/-- A bounded interval lies within the ray from `a` exactly when it starts at or after `a`. -/
theorem withTop_le_Ici : (↑i.withTop : Interval (WithTop α)) ≤ Ici a ↔ a ≤ i.fst := by
  simp only [coe_le_iff, NonemptyInterval.fst_withTop, NonemptyInterval.snd_withTop, mem_Ici,
    WithTop.coe_le_coe]
  exact ⟨And.left, λ h => ⟨h, le_trans h i.fst_le_snd⟩⟩

/-- A bounded interval precedes the ray from `a` exactly when it ends before `a`. -/
theorem precedes_withTop_Ici :
    (↑i.withTop : Interval (WithTop α)).Precedes (Ici a) ↔ i.snd < a := by
  rw [Ici, precedes_coe_coe]; simp [NonemptyInterval.precedes]

/-- A bounded interval precedes the point `a` exactly when it ends before `a`. -/
theorem precedes_withTop_pure :
    (↑i.withTop : Interval (WithTop α)).Precedes (pure ↑a) ↔ i.snd < a := by
  rw [pure, precedes_coe_coe]; simp [NonemptyInterval.precedes]

end WithTop

section WithTopLattice

variable {α : Type*} [Lattice α] {i : NonemptyInterval α} {a : α}

/-- A bounded interval meets the ray from `a` exactly when it ends at or after `a`. -/
theorem not_disjoint_withTop_Ici :
    ¬ Disjoint (↑i.withTop : Interval (WithTop α)) (Ici a) ↔ a ≤ i.snd := by
  rw [Ici, not_disjoint_coe_coe]; simp [NonemptyInterval.overlaps]

end WithTopLattice

end Interval
