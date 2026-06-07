import Mathlib.Order.Interval.Basic

/-!
# Relational vocabulary for nonempty intervals

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

Generalized intervals with open/closed boundaries ([rouillard-2026])
live with their consuming study in `Studies/Rouillard2026.lean`.
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

/-! ### Boundary type (open/closed endpoints) -/

/-- Whether an interval's boundary is included (closed) or excluded (open).
    [rouillard-2026] §2.2.4: the distinction between closed and open
    times is central to deriving the polarity sensitivity of G-TIAs.
    Event runtimes are closed; PTSs are open intervals.

    Consumed by `GInterval` (in `Studies/Rouillard2026.lean`). -/
inductive BoundaryType where
  | closed  -- boundary moment included in the interval
  | open_   -- boundary moment excluded from the interval
  deriving DecidableEq, Repr

end NonemptyInterval
