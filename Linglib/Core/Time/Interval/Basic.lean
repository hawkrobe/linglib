import Mathlib.Data.Int.Order.Basic
import Linglib.Core.Scales.Scale

/-!
# Temporal intervals

@cite{allen-1983} @cite{kamp-reyle-1993} @cite{klein-1994}
@cite{pancheva-2003} @cite{rouillard-2026} @cite{sagey-1986}
@cite{smith-1997}

The basic interval type and its relational algebra: containment,
subinterval, overlap, precedence, meets, plus the nuclear cluster
needed by aspectual semantics (proper subinterval, final subinterval,
initial overlap, isAfter/isBefore).

Open/closed boundary distinctions and generalized intervals
(@cite{rouillard-2026}) live in `Generalized.lean`.
-/

namespace Core.Time

/-- Temporal interval: a pair of times [start, finish] with start ≤ finish.
    Following standard interval semantics. -/
@[ont_sort] structure Interval (Time : Type*) [LinearOrder Time] where
  start : Time
  finish : Time
  valid : start ≤ finish

namespace Interval

variable {Time : Type*} [LinearOrder Time]

/-- Point interval: start = finish -/
def point (t : Time) : Interval Time where
  start := t
  finish := t
  valid := le_refl t

/-- Does time t fall within interval i? -/
def contains (i : Interval Time) (t : Time) : Prop :=
  i.start ≤ t ∧ t ≤ i.finish

/-- Interval i₁ is contained in i₂ -/
def subinterval (i₁ i₂ : Interval Time) : Prop :=
  i₂.start ≤ i₁.start ∧ i₁.finish ≤ i₂.finish

/-- Intervals overlap -/
def overlaps (i₁ i₂ : Interval Time) : Prop :=
  i₁.start ≤ i₂.finish ∧ i₂.start ≤ i₁.finish

/-- i₁ precedes i₂ (no overlap, i₁ entirely before i₂) -/
def precedes (i₁ i₂ : Interval Time) : Prop :=
  i₁.finish < i₂.start

/-- i₁ meets i₂ (i₁ ends exactly when i₂ starts) -/
def meets (i₁ i₂ : Interval Time) : Prop :=
  i₁.finish = i₂.start

/-- Proper subinterval: i₁ ⊆ i₂ with at least one strict boundary.
    Required for IMPF: reference time PROPERLY inside event runtime. -/
def properSubinterval (i₁ i₂ : Interval Time) : Prop :=
  i₁.subinterval i₂ ∧ (i₂.start < i₁.start ∨ i₁.finish < i₂.finish)

/-- i₁ is entirely after i₂ (i₁ starts at or after i₂ finishes). -/
def isAfter (i₁ i₂ : Interval Time) : Prop :=
  i₂.finish ≤ i₁.start

/-- i₁ is entirely before i₂. -/
def isBefore (i₁ i₂ : Interval Time) : Prop :=
  i₁.finish ≤ i₂.start

theorem properSubinterval_implies_subinterval (i₁ i₂ : Interval Time)
    (h : i₁.properSubinterval i₂) : i₁.subinterval i₂ :=
  h.1

@[simp] theorem subinterval_refl (i : Interval Time) : i.subinterval i :=
  ⟨le_refl _, le_refl _⟩

/-- No interval is properly contained in itself. -/
theorem properSubinterval_irrefl (i : Interval Time) :
    ¬ i.properSubinterval i := by
  intro ⟨_, h⟩
  cases h with
  | inl h => exact lt_irrefl _ h
  | inr h => exact lt_irrefl _ h

theorem isAfter_iff_isBefore (i₁ i₂ : Interval Time) :
    i₁.isAfter i₂ ↔ i₂.isBefore i₁ :=
  Iff.rfl

/-- Final subinterval: i₁ ⊆ i₂ and they share the same right endpoint.
    @cite{pancheva-2003}: PTS(i', i) iff i is a final subinterval of i'. -/
def finalSubinterval (i₁ i₂ : Interval Time) : Prop :=
  i₁.subinterval i₂ ∧ i₁.finish = i₂.finish

/-- Initial overlap (∂): i₁ and i₂ overlap, and the start of i₂ is in i₁.
    @cite{pancheva-2003}: i ∂τ(e) — the beginning of the eventuality is included
    in the reference interval but the end may not be.
    @cite{smith-1997}: the neutral viewpoint uses the same interval relation. -/
def initialOverlap (i₁ i₂ : Interval Time) : Prop :=
  i₁.overlaps i₂ ∧ i₁.contains i₂.start

/-- Final subinterval implies subinterval. -/
theorem finalSubinterval_implies_subinterval (i₁ i₂ : Interval Time)
    (h : i₁.finalSubinterval i₂) : i₁.subinterval i₂ :=
  h.1

/-- Every interval is a final subinterval of itself. -/
theorem finalSubinterval_refl (i : Interval Time) : i.finalSubinterval i :=
  ⟨subinterval_refl i, rfl⟩

-- ════════════════════════════════════════════════════
-- § Interval Relation Algebra
-- ════════════════════════════════════════════════════

/-- Overlap is reflexive: every interval overlaps itself. -/
@[simp] theorem overlaps_refl (i : Interval Time) : i.overlaps i :=
  ⟨i.valid, i.valid⟩

/-- Overlap is symmetric. -/
theorem overlaps_symm {i₁ i₂ : Interval Time} (h : i₁.overlaps i₂) :
    i₂.overlaps i₁ :=
  ⟨h.2, h.1⟩

/-- Overlap is symmetric (iff version). -/
theorem overlaps_comm (i₁ i₂ : Interval Time) :
    i₁.overlaps i₂ ↔ i₂.overlaps i₁ :=
  ⟨overlaps_symm, overlaps_symm⟩

/-- Overlap is NOT transitive: [0,1] overlaps [1,2] and [1,2] overlaps [2,3],
    but [0,1] does not overlap [2,3].

    This is the cornerstone property that distinguishes overlap from
    simultaneity (identity) and makes the No-Crossing Constraint derivable
    from temporal precedence alone (@cite{sagey-1986} §5.2.3, fn. 6). -/
theorem overlaps_not_transitive :
    ¬ ∀ (i₁ i₂ i₃ : Interval ℤ),
      i₁.overlaps i₂ → i₂.overlaps i₃ → i₁.overlaps i₃ := by
  intro h
  have := h ⟨0, 1, by omega⟩ ⟨1, 2, by omega⟩ ⟨2, 3, by omega⟩
    (by simp only [overlaps]; omega) (by simp only [overlaps]; omega)
  simp only [overlaps] at this
  omega

/-- Subintervals overlap their containing intervals. -/
theorem subinterval_overlaps {i₁ i₂ : Interval Time}
    (h : i₁.subinterval i₂) : i₁.overlaps i₂ :=
  ⟨le_trans i₁.valid h.2, le_trans h.1 i₁.valid⟩

/-- Precedence is irreflexive: no interval precedes itself. -/
theorem precedes_irrefl (i : Interval Time) : ¬ i.precedes i :=
  not_lt.mpr i.valid

/-- Precedence is asymmetric. -/
theorem precedes_asymm {i₁ i₂ : Interval Time}
    (h : i₁.precedes i₂) : ¬ i₂.precedes i₁ :=
  not_lt.mpr (le_trans i₁.valid (le_trans (le_of_lt h) i₂.valid))

/-- Precedence is transitive. -/
theorem precedes_trans {i₁ i₂ i₃ : Interval Time}
    (h₁₂ : i₁.precedes i₂) (h₂₃ : i₂.precedes i₃) : i₁.precedes i₃ :=
  lt_trans (lt_of_lt_of_le h₁₂ i₂.valid) h₂₃

/-- Precedence and overlap are mutually exclusive. -/
theorem precedes_not_overlaps {i₁ i₂ : Interval Time}
    (h : i₁.precedes i₂) : ¬ i₁.overlaps i₂ :=
  fun ⟨_, h₂⟩ => absurd (lt_of_lt_of_le h h₂) (lt_irrefl _)

-- ════════════════════════════════════════════════════
-- § Boundary Type (open/closed endpoints)
-- ════════════════════════════════════════════════════

/-- Whether an interval's boundary is included (closed) or excluded (open).
    @cite{rouillard-2026} §2.2.4: the distinction between closed and open
    times is central to deriving the polarity sensitivity of G-TIAs.
    Event runtimes are closed; PTSs are open intervals.

    Consumed by `GInterval` (in `Generalized.lean`). -/
inductive BoundaryType where
  | closed  -- boundary moment included in the interval
  | open_   -- boundary moment excluded from the interval
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § BoundaryType → Boundedness Bridge
-- ════════════════════════════════════════════════════

/-- Interval boundary type maps to scale boundedness.
    @cite{rouillard-2026}: closed runtimes correspond to closed scales
    (licensed); open PTSs correspond to open scales (blocked/information
    collapse). This is the "interval generalization":
    `Interval.BoundaryType.closed`/`.open_` is isomorphic to
    `Core.Scale.Boundedness.closed`/`.open_`. -/
def BoundaryType.toBoundedness : BoundaryType → Core.Scale.Boundedness
  | .closed => .closed
  | .open_ => .open_

theorem closedBoundary_licensed :
    (BoundaryType.toBoundedness .closed).isLicensed = true := rfl

theorem openBoundary_blocked :
    (BoundaryType.toBoundedness .open_).isLicensed = false := rfl

instance : Core.Scale.LicensingPipeline BoundaryType where
  toBoundedness := BoundaryType.toBoundedness

end Interval

end Core.Time
