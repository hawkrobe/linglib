/-
# Temporal Semantics Infrastructure

Foundational types for tense, aspect, and temporal reference.

## Key Concepts

1. **Times** as primitives (intervals or instants)
2. **Situations** as world-time pairs (Kratzer 1989, 2021)
3. **Temporal relations** (precedence, overlap, containment)
4. **Historical modal base** (Thomason 1984) for future branching

## Reichenbach (1947) / Klein (1994) Framework

Three distinguished times:
- **S** (Speech time): When the utterance occurs
- **R** (Reference/Topic time): The time being talked about
- **E** (Event time): When the event occurs

Tense relates R to S; Aspect relates E to R.

## References

- Reichenbach, H. (1947). Elements of Symbolic Logic.
- Partee, B. (1973). Some structural analogies between tenses and pronouns.
- Klein, W. (1994). Time in Language.
- Kratzer, A. (1998). More structural analogies between pronouns and tenses.
- Kratzer, A. (2021). Situations in natural language semantics.
- Thomason, R. (1984). Combinations of tense and modality.
-/

import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic

namespace TruthConditional.Core.Time


/--
Abstract time type.

We keep this polymorphic to allow:
- Discrete times (ℕ, ℤ)
- Dense times (ℚ, ℝ)
- Abstract/opaque times

The key requirement is a linear order for temporal relations.
-/
class TimeStructure (Time : Type*) extends LinearOrder Time

/--
Temporal interval: a pair of times [start, end].

Following standard interval semantics (Allen 1983, Kamp & Reyle 1993).
-/
structure Interval (Time : Type*) [LE Time] where
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

/-- Decidable containment for computational use -/
def containsB [DecidableRel (α := Time) (· ≤ ·)] (i : Interval Time) (t : Time) : Bool :=
  i.start ≤ t && t ≤ i.finish

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

-- ════════════════════════════════════════════════════
-- § Open/Closed Interval Distinction (Rouillard 2026)
-- ════════════════════════════════════════════════════

/-- Whether an interval's boundary is included (closed) or excluded (open).
    Rouillard (2026) §2.2.4: the distinction between closed and open times
    is central to deriving the polarity sensitivity of G-TIAs.
    Event runtimes are closed; PTSs are open intervals. -/
inductive BoundaryType where
  | closed  -- boundary moment included in the interval
  | open_   -- boundary moment excluded from the interval
  deriving DecidableEq, Repr, BEq

/-- A generalized interval with specified boundary types.
    Extends the basic `Interval` with open/closed annotations on each end.
    Rouillard (2026) eq. (14a–b), (99a–b). -/
structure GInterval (Time : Type*) [LE Time] where
  /-- Left endpoint -/
  left : Time
  /-- Right endpoint -/
  right : Time
  /-- Left boundary type: closed [m or open ]m -/
  leftType : BoundaryType
  /-- Right boundary type: closed m] or open m[ -/
  rightType : BoundaryType
  /-- The endpoints are ordered -/
  valid : left ≤ right

namespace GInterval

variable {Time : Type*} [LinearOrder Time]

/-- A closed interval [m₁, m₂]: both endpoints included.
    Rouillard (2026) eq. (14a): C := {t | min(t) ⊑ᵢ t ∧ max(t) ⊑ᵢ t}. -/
def closed (i : Interval Time) : GInterval Time where
  left := i.start
  right := i.finish
  leftType := .closed
  rightType := .closed
  valid := i.valid

/-- An open interval ]m₁, m₂[: both endpoints excluded.
    Rouillard (2026) eq. (14b): O := {t | min(t) ⊄ᵢ t ∨ max(t) ⊄ᵢ t}. -/
def open_ (i : Interval Time) : GInterval Time where
  left := i.start
  right := i.finish
  leftType := .open_
  rightType := .open_
  valid := i.valid

/-- The o(t) operation: open counterpart of a time.
    Rouillard (2026) eq. (99a): if t is open, o(t) = t; if t is closed,
    o(t) is the open interval with the same endpoints.  -/
def toOpen (gi : GInterval Time) : GInterval Time :=
  { gi with leftType := .open_, rightType := .open_ }

/-- The c(t) operation: closed counterpart of a time.
    Rouillard (2026) eq. (99b): if t is closed, c(t) = t; if t is open,
    c(t) adds the endpoints. -/
def toClosed (gi : GInterval Time) : GInterval Time :=
  { gi with leftType := .closed, rightType := .closed }

/-- Is this interval closed (both boundaries included)? -/
def isClosed (gi : GInterval Time) : Prop :=
  gi.leftType = .closed ∧ gi.rightType = .closed

/-- Is this interval open (both boundaries excluded)? -/
def isOpen (gi : GInterval Time) : Prop :=
  gi.leftType = .open_ ∧ gi.rightType = .open_

/-- Containment for generalized intervals: m is in gi.
    For closed endpoints, ≤ is used; for open endpoints, <. -/
def gcontains (gi : GInterval Time) (m : Time) : Prop :=
  (match gi.leftType with
   | .closed => gi.left ≤ m
   | .open_ => gi.left < m) ∧
  (match gi.rightType with
   | .closed => m ≤ gi.right
   | .open_ => m < gi.right)

/-- Generalized subinterval: gi₁ ⊆ gi₂ (every moment in gi₁ is in gi₂). -/
def gsubinterval (gi₁ gi₂ : GInterval Time) : Prop :=
  ∀ m : Time, gi₁.gcontains m → gi₂.gcontains m

/-- Convert a closed GInterval back to the basic Interval type. -/
def toInterval (gi : GInterval Time) : Interval Time where
  start := gi.left
  finish := gi.right
  valid := gi.valid

/-- The closed counterpart of an open interval is always closed. -/
theorem toClosed_isClosed (gi : GInterval Time) : gi.toClosed.isClosed :=
  ⟨rfl, rfl⟩

/-- The open counterpart is always open. -/
theorem toOpen_isOpen (gi : GInterval Time) : gi.toOpen.isOpen :=
  ⟨rfl, rfl⟩

/-- toClosed is idempotent. -/
theorem toClosed_idempotent (gi : GInterval Time) :
    gi.toClosed.toClosed = gi.toClosed := rfl

/-- toOpen is idempotent. -/
theorem toOpen_idempotent (gi : GInterval Time) :
    gi.toOpen.toOpen = gi.toOpen := rfl

end GInterval

end Interval

-- ════════════════════════════════════════════════════
-- § Dense Time (Fox & Hackl 2006, Rouillard 2026)
-- ════════════════════════════════════════════════════

/-- Dense time is captured by Mathlib's `DenselyOrdered` typeclass:
    ∀ m₁ m₂, m₁ < m₂ → ∃ m₃, m₁ < m₃ ∧ m₃ < m₂.

    This is Rouillard (2026) eq. (8) and an instance of Fox & Hackl (2006)
    Universal Density of Measurement (UDM). Instead of a custom class, we
    use Mathlib's `DenselyOrdered` directly — ℚ and ℝ already have instances.

    Crucial for G-TIA polarity sensitivity: ensures that no open interval
    can be the smallest interval including a closed time. -/
abbrev DenseTime (Time : Type*) [LinearOrder Time] := DenselyOrdered Time


/--
A situation is a part of a world at a time.

Following Kratzer's situation semantics:
- Situations are "slices" of possible worlds
- They have both spatial and temporal extent
- They can be minimal witnesses for propositions

We model situations as world-time pairs, abstracting from spatial extent.
-/
structure Situation (W Time : Type*) where
  /-- The world this situation is part of -/
  world : W
  /-- The temporal coordinate of the situation -/
  time : Time
  deriving Repr

namespace Situation

variable {W Time : Type*}

/-- Temporal trace: extract the time of a situation -/
@[simp]
def τ (s : Situation W Time) : Time := s.time

/-- World of a situation -/
@[simp]
def w (s : Situation W Time) : W := s.world

/-- Create a situation from world and time -/
def mk' (world : W) (time : Time) : Situation W Time :=
  { world := world, time := time }

/-- Situations at the same world -/
def sameWorld (s₁ s₂ : Situation W Time) : Prop :=
  s₁.world = s₂.world

/-- Situations at the same time -/
def sameTime (s₁ s₂ : Situation W Time) : Prop :=
  s₁.time = s₂.time

/-- s₁ temporally precedes s₂ -/
def before [LT Time] (s₁ s₂ : Situation W Time) : Prop :=
  s₁.time < s₂.time

/-- s₁ temporally follows s₂ -/
def after [LT Time] (s₁ s₂ : Situation W Time) : Prop :=
  s₁.time > s₂.time

/-- s₁ is contemporaneous with s₂ -/
def contemporaneous (s₁ s₂ : Situation W Time) : Prop :=
  s₁.time = s₂.time

end Situation


/--
Reichenbach's temporal parameters for tense/aspect analysis.

- `speechTime`: When the utterance is made (S)
- `referenceTime`: The time being talked about (R, Klein's "topic time")
- `eventTime`: When the described event occurs (E)
-/
structure ReichenbachFrame (Time : Type*) where
  /-- Speech time (S): when the utterance occurs -/
  speechTime : Time
  /-- Reference time (R): the time under discussion -/
  referenceTime : Time
  /-- Event time (E): when the event takes place -/
  eventTime : Time

namespace ReichenbachFrame

variable {Time : Type*} [LinearOrder Time]

/-- PAST: R < S (reference time precedes speech time) -/
def isPast (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime < f.speechTime

/-- PRESENT: R = S (reference time equals speech time) -/
def isPresent (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime = f.speechTime

/-- FUTURE: S < R (speech time precedes reference time) -/
def isFuture (f : ReichenbachFrame Time) : Prop :=
  f.speechTime < f.referenceTime

/-- Perfective: E ⊆ R (event contained in reference) -/
def isPerfective (f : ReichenbachFrame Time) : Prop :=
  f.eventTime = f.referenceTime  -- Simplified: E = R

/-- Imperfective: R ⊆ E (reference contained in event) -/
def isImperfective (f : ReichenbachFrame Time) : Prop :=
  f.eventTime = f.referenceTime  -- Simplified: needs intervals for proper treatment

/-- Perfect: E < R (event precedes reference) -/
def isPerfect (f : ReichenbachFrame Time) : Prop :=
  f.eventTime < f.referenceTime

/-- Prospective: R < E (reference precedes event) -/
def isProspective (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime < f.eventTime

end ReichenbachFrame


/--
World history function: given a world and time, returns worlds that
agree with that world up to that time.

This is the basis for the "historical" or "open future" modal base
used in future-oriented modality.

Intuition: At time t in world w, multiple futures are possible.
The historical alternatives are all worlds that share the same
past with w up to t.
-/
def WorldHistory (W Time : Type*) := W → Time → Set W

/--
Historical modal base: situations whose worlds agree with s up to τ(s),
and whose times are at or after τ(s).

Following Thomason (1984) and Condoravdi (2002):
- Past is fixed (determined)
- Future branches (open)

hist(s) = {s' : w_{s'} ∈ H(wₛ, τ(s)) ∧ τ(s') ≥ τ(s)}
-/
def historicalBase {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (s : Situation W Time) : Set (Situation W Time) :=
  { s' | s'.world ∈ history s.world s.time ∧ s'.time ≥ s.time }

/--
A world history is reflexive if every world agrees with itself.
-/
def WorldHistory.reflexive {W Time : Type*} (h : WorldHistory W Time) : Prop :=
  ∀ w t, w ∈ h w t

/--
A world history is backwards-closed: if w' agrees with w up to t,
and t' ≤ t, then w' agrees with w up to t'.

"If two worlds agree up to time t, they also agree up to any earlier time."
-/
def WorldHistory.backwardsClosed {W Time : Type*} [LE Time]
    (h : WorldHistory W Time) : Prop :=
  ∀ w w' t t', t' ≤ t → w' ∈ h w t → w' ∈ h w t'

/--
Standard historical modal base properties.
-/
structure HistoricalProperties {W Time : Type*} [LE Time]
    (h : WorldHistory W Time) : Prop where
  /-- Every world agrees with itself -/
  refl : h.reflexive
  /-- Agreement is preserved for earlier times -/
  backwards : h.backwardsClosed


/--
A temporal proposition: true or false at each situation.

This is the situation-semantic analog of Prop' W.
-/
abbrev TProp (W Time : Type*) := Situation W Time → Prop

/--
Decidable temporal proposition (for computation).
-/
abbrev TBProp (W Time : Type*) := Situation W Time → Bool

/--
Lift a world proposition to a temporal proposition.

The lifted proposition is true at situation s iff the original
proposition is true at s.world.
-/
def liftProp {W Time : Type*} (p : W → Prop) : TProp W Time :=
  λ s => p s.world

/--
A proposition holds at time t in world w.
-/
def holdsAt {W Time : Type*} (p : TProp W Time) (w : W) (t : Time) : Prop :=
  p ⟨w, t⟩


/--
Temporal relation type for tense operators.

These relate two times (typically event time and reference/speech time).
-/
inductive TemporalRelation where
  | before      -- t₁ < t₂
  | after       -- t₁ > t₂
  | overlapping -- t₁ ◦ t₂ (simplified to equality for points)
  | notAfter    -- t₁ ≤ t₂
  | notBefore   -- t₁ ≥ t₂
  deriving DecidableEq, Repr, BEq

namespace TemporalRelation

/-- Evaluate a temporal relation on two times -/
def eval {Time : Type*} [LinearOrder Time] :
    TemporalRelation → Time → Time → Prop
  | .before, t₁, t₂ => t₁ < t₂
  | .after, t₁, t₂ => t₁ > t₂
  | .overlapping, t₁, t₂ => t₁ = t₂
  | .notAfter, t₁, t₂ => t₁ ≤ t₂
  | .notBefore, t₁, t₂ => t₁ ≥ t₂

/-- Decidable evaluation -/
def evalB {Time : Type*} [LinearOrder Time] [DecidableEq Time]
    [DecidableRel (α := Time) (· < ·)] [DecidableRel (α := Time) (· ≤ ·)] :
    TemporalRelation → Time → Time → Bool
  | .before, t₁, t₂ => t₁ < t₂
  | .after, t₁, t₂ => t₁ > t₂
  | .overlapping, t₁, t₂ => t₁ == t₂
  | .notAfter, t₁, t₂ => t₁ ≤ t₂
  | .notBefore, t₁, t₂ => t₁ ≥ t₂

end TemporalRelation


/--
Integer times for concrete examples.

Using ℤ allows both past (negative) and future (positive) times
relative to a speech time of 0.
-/
instance : TimeStructure ℤ where

/-- Speech time at 0 by convention -/
def speechTimeZ : ℤ := 0

/-- Example: yesterday (t = -1) -/
def yesterdayZ : ℤ := -1

/-- Example: today (t = 0) -/
def todayZ : ℤ := 0

/-- Example: tomorrow (t = 1) -/
def tomorrowZ : ℤ := 1

end TruthConditional.Core.Time
