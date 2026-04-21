import Linglib.Core.Time.Interval.Basic

/-!
# Generalized intervals with open/closed boundaries

@cite{rouillard-2026}

`GInterval` extends the basic `Interval` with explicit open/closed
annotations on each endpoint, plus the `closed`/`open_` constructors,
the `toOpen`/`toClosed` operations (eq. 99a–b), and generalized
containment/subinterval relations.

Used by Rouillard 2026's account of G-TIA polarity sensitivity, where
event runtimes are closed and PTSs are open.
-/

namespace Core.Time.Interval

/-- A generalized interval with specified boundary types.
    Extends the basic `Interval` with open/closed annotations on each end.
    @cite{rouillard-2026} eq. (14a–b), (99a–b). -/
structure GInterval (Time : Type*) [LinearOrder Time] where
  /-- Left endpoint -/
  left : Time
  /-- Right endpoint -/
  right : Time
  /-- Left boundary type: closed [m or open]m -/
  leftType : BoundaryType
  /-- Right boundary type: closed m] or open m[ -/
  rightType : BoundaryType
  /-- The endpoints are ordered -/
  valid : left ≤ right

namespace GInterval

variable {Time : Type*} [LinearOrder Time]

/-- A closed interval [m₁, m₂]: both endpoints included.
    @cite{rouillard-2026} eq. (14a): C := {t | min(t) ⊑ᵢ t ∧ max(t) ⊑ᵢ t}. -/
def closed (i : Interval Time) : GInterval Time where
  left := i.start
  right := i.finish
  leftType := .closed
  rightType := .closed
  valid := i.valid

/-- An open interval]m₁, m₂[: both endpoints excluded.
    @cite{rouillard-2026} eq. (14b): O := {t | min(t) ⊄ᵢ t ∨ max(t) ⊄ᵢ t}. -/
def open_ (i : Interval Time) : GInterval Time where
  left := i.start
  right := i.finish
  leftType := .open_
  rightType := .open_
  valid := i.valid

/-- The o(t) operation: open counterpart of a time.
    @cite{rouillard-2026} eq. (99a): if t is open, o(t) = t; if t is closed,
    o(t) is the open interval with the same endpoints. -/
def toOpen (gi : GInterval Time) : GInterval Time :=
  { gi with leftType := .open_, rightType := .open_ }

/-- The c(t) operation: closed counterpart of a time.
    @cite{rouillard-2026} eq. (99b): if t is closed, c(t) = t; if t is open,
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
@[simp] theorem toClosed_isClosed (gi : GInterval Time) : gi.toClosed.isClosed :=
  ⟨rfl, rfl⟩

/-- The open counterpart is always open. -/
@[simp] theorem toOpen_isOpen (gi : GInterval Time) : gi.toOpen.isOpen :=
  ⟨rfl, rfl⟩

/-- toClosed is idempotent. -/
@[simp] theorem toClosed_idempotent (gi : GInterval Time) :
    gi.toClosed.toClosed = gi.toClosed := rfl

/-- toOpen is idempotent. -/
@[simp] theorem toOpen_idempotent (gi : GInterval Time) :
    gi.toOpen.toOpen = gi.toOpen := rfl

end GInterval

end Core.Time.Interval
