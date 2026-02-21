import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Linglib.Core.Scale
import Linglib.Core.Situation
import Linglib.Tactics.OntSort

export Core (Situation)

/-!
# Theory-Neutral Temporal Infrastructure

Framework-agnostic types for temporal reasoning: intervals, temporal relations,
situations (world–time pairs), and concrete time instances.

These definitions are used across truth-conditional semantics, event semantics,
dynamic semantics, and intensional semantics. The theory-specific layer
(branching time, temporal propositions) remains in
`Theories/Semantics.Montague/Core/Time`.

## Key Concepts

1. **Times** as primitives (intervals or instants)
2. **Situations** as world-time pairs (Kratzer 1989, 2021)
3. **Temporal relations** (precedence, overlap, containment)
4. **Atomic distributivity** (subinterval property, Zhao 2026)

## References

- Allen, J. (1983). Maintaining knowledge about temporal intervals.
- Kamp, H. & Reyle, U. (1993). From Discourse to Logic.
- Klein, W. (1994). Time in Language.
- Kratzer, A. (2021). Situations in natural language semantics.
- Rouillard, V. (2026). Generalized temporal interval semantics.
- Fox, D. & Hackl, M. (2006). The Universal Density of Measurement.
- Zhao, Z. (2026). Cross-Linguistic and Cross-Domain Parallels in the
  Semantics of Degree and Time. MIT dissertation.
- Champollion, L. (2015). The interaction of compositional semantics and
  event semantics. *Linguistics and Philosophy* 38(1):31–66.
-/

namespace Core.Time


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
@[ont_sort] structure Interval (Time : Type*) [LE Time] where
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


-- Situation is now defined in Core/Ontology.lean (Core.Situation).
-- Re-exported via `export Core (Situation)` above.


-- ════════════════════════════════════════════════════
-- § Aspectual Boundedness
-- ════════════════════════════════════════════════════

/-- Aspectual boundedness of a situation (Smith 1991, Depraetere 1995).

    Whether a situation is conceptualized as having inherent boundaries:
    - **bounded**: telic / perfective / closed (achievements, accomplishments)
    - **unbounded**: atelic / imperfective / open (activities, states)

    Cross-cuts Vendler classes and aspectual viewpoint. Used by event semantics
    (telicity), aspect theory (perfective/imperfective), and temporal discourse
    interpretation (sequential vs. simultaneous default readings). -/
inductive SituationBoundedness where
  | bounded    -- telic / perfective / closed
  | unbounded  -- atelic / imperfective / open
  deriving DecidableEq, Repr, BEq

instance : Core.Scale.LicensingPipeline SituationBoundedness where
  toBoundedness
    | .bounded   => .closed
    | .unbounded => .open_

theorem bounded_licensed :
    Core.Scale.LicensingPipeline.isLicensed SituationBoundedness.bounded = true := rfl

theorem unbounded_blocked :
    Core.Scale.LicensingPipeline.isLicensed SituationBoundedness.unbounded = false := rfl

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

-- ════════════════════════════════════════════════════
-- § BoundaryType → Boundedness Bridge (Interval Generalization)
-- ════════════════════════════════════════════════════

/-- Interval boundary type maps to scale boundedness.
    Rouillard (2026): closed runtimes correspond to closed scales (licensed);
    open PTSs correspond to open scales (blocked/information collapse).
    This is the "interval generalization": `BoundaryType.closed`/`.open_`
    in `Core/Time` is isomorphic to `Boundedness.closed`/`.open_` in
    `Core/MeasurementScale`. -/
def Interval.BoundaryType.toBoundedness : Interval.BoundaryType → Core.Scale.Boundedness
  | .closed => .closed
  | .open_ => .open_

theorem closedBoundary_licensed :
    (Interval.BoundaryType.toBoundedness .closed).isLicensed = true := rfl

theorem openBoundary_blocked :
    (Interval.BoundaryType.toBoundedness .open_).isLicensed = false := rfl

instance : Core.Scale.LicensingPipeline Interval.BoundaryType where
  toBoundedness := Interval.BoundaryType.toBoundedness

-- ════════════════════════════════════════════════════
-- § Atomic Distributivity (Zhao 2026, Champollion 2015)
-- ════════════════════════════════════════════════════

/-- An event quantifier (Champollion 2015): a predicate on event predicates.
    V(P) holds iff "there is an event satisfying P" according to V's
    quantificational force. -/
abbrev EvQuant (Event : Type*) := (Event → Prop) → Prop

/-- ATOM-DIST_α (Zhao 2026, Def. 5.3): an event quantifier V satisfies
    ATOM-DIST with respect to trace function τ iff for every event predicate P
    and subinterval i' of τ(e), V also holds for the restriction of P to
    events whose trace is i'.

    Formally: V(P) → ∀ e, P(e) → ∀ i', subinterval(i', τ(e)) →
              V(λ e'. P(e') ∧ τ(e') = i')

    This captures the subinterval property parameterized over any
    linearly ordered dimension α. -/
def AtomDist {Event : Type*} {α : Type*} [LinearOrder α]
    (τ : Event → Interval α) (V : EvQuant Event) : Prop :=
  ∀ (P : Event → Prop), V P →
    ∀ (e : Event), P e →
      ∀ (i' : Interval α), i'.subinterval (τ e) →
        V (λ e' => P e' ∧ τ e' = i')

/-- ATOM-DIST_t: temporal atomic distributivity.
    Abbreviation for ATOM-DIST with respect to a temporal trace. -/
abbrev AtomDist_t {Event : Type*} {Time : Type*} [LinearOrder Time]
    (τ_t : Event → Interval Time) (V : EvQuant Event) : Prop :=
  AtomDist τ_t V

/-- ATOM-DIST_d: degree atomic distributivity.
    Abbreviation for ATOM-DIST with respect to a degree trace. -/
abbrev AtomDist_d {Event : Type*} {Deg : Type*} [LinearOrder Deg]
    (τ_d : Event → Interval Deg) (V : EvQuant Event) : Prop :=
  AtomDist τ_d V

/-- NOT-ATOM-DIST_α licensing condition (Zhao 2026, Ch. 6):
    A particle is licensed by an event quantifier V (w.r.t. trace τ) iff
    V does NOT satisfy ATOM-DIST_α. This is the presupposition of
    Mandarin le and mei-you. -/
def antiAtomDistLicensed {Event : Type*} {α : Type*} [LinearOrder α]
    (τ : Event → Interval α) (V : EvQuant Event) : Prop :=
  ¬ AtomDist τ V

end Core.Time
