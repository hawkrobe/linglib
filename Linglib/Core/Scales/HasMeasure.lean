import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.NormNum

/-!
# Core/Scales/HasMeasure.lean — measurement typeclass + finite degree types

`HasMeasure E α` is the formal-semantics "measure function" `μ : E → α`,
parameterized over both the entity type and the codomain.

Renames the legacy `HasDegree` typeclass — `HasDegree` is preserved as a
deprecation alias for one version, then removed in a later refactor.

`Degree max` and `Threshold max` are discretized scale types for gradable
adjective RSA computations; they participate in the `DirectedMeasure`
infrastructure via their `LinearOrder`/`BoundedOrder` instances.

This file is part of the Phase A decomposition of the legacy
`Core/Scales/Scale.lean` dumping ground (master plan v4).

## Multi-dim measurement

No `outParam` on `δ` — multi-dim same-carrier (e.g. `Entity` measured by
both height and weight) is supported via distinct `(α, δ)` instance
signatures or newtype wrappers (mathlib `Additive`/`Multiplicative`
precedent). This is a deliberate design choice per master plan v4.
-/

namespace Core.Scale

-- ════════════════════════════════════════════════════
-- § 11. Discrete Bounded Scales
-- ════════════════════════════════════════════════════

/-! ### Degree and Threshold types for finite scales

`Degree max` wraps `Fin (max + 1)` with `LinearOrder`, `BoundedOrder`, `Fintype`.
`Threshold max` wraps `Fin max` with coercion to `Degree max`. -/

/-- A degree on a scale from 0 to max. Represents discretized continuous
    values like height, temperature, etc. -/
structure Degree (max : Nat) where
  value : Fin (max + 1)
  deriving Repr, DecidableEq

instance {n : Nat} : Inhabited (Degree n) := ⟨⟨0, Nat.zero_lt_succ n⟩⟩

/-- `Degree max` inherits a linear order from `Fin (max + 1)`. -/
instance {max : Nat} : LinearOrder (Degree max) :=
  LinearOrder.lift' Degree.value (fun a b h => by cases a; cases b; simp_all)

/-- `Degree max` is bounded: 0 is the minimum, `max` is the maximum. -/
instance {max : Nat} : BoundedOrder (Degree max) where
  top := ⟨Fin.last max⟩
  le_top d := Fin.le_last d.value
  bot := ⟨0, Nat.zero_lt_succ max⟩
  bot_le d := Fin.zero_le d.value

/-- All degrees from 0 to max -/
def allDegrees (max : Nat) : List (Degree max) :=
  List.finRange (max + 1) |>.map (⟨·⟩)

/-- Degree from Nat (clamped) -/
def Degree.ofNat (max : Nat) (n : Nat) : Degree max :=
  ⟨⟨min n max, by omega⟩⟩

/-- Get numeric value -/
def Degree.toNat {max : Nat} (d : Degree max) : Nat := d.value.val

/-- A threshold for a gradable adjective. x is "tall" iff degree(x) > threshold. -/
structure Threshold (max : Nat) where
  value : Fin max
  deriving Repr, DecidableEq

instance {n : Nat} (h : 0 < n := by omega) : Inhabited (Threshold n) := ⟨⟨0, h⟩⟩

/-- `Threshold max` inherits a linear order from `Fin max`. -/
instance {max : Nat} : LinearOrder (Threshold max) :=
  LinearOrder.lift' Threshold.value (fun a b h => by cases a; cases b; simp_all)

/-- All thresholds from 0 to max-1 -/
def allThresholds (max : Nat) (_ : 0 < max := by omega) : List (Threshold max) :=
  List.finRange max |>.map (⟨·⟩)

/-- Get numeric value -/
def Threshold.toNat {max : Nat} (t : Threshold max) : Nat := t.value.val

instance {max : Nat} : Fintype (Degree max) :=
  Fintype.ofEquiv (Fin (max + 1)) ⟨Degree.mk, Degree.value, fun _ => rfl, fun ⟨_⟩ => rfl⟩

instance {max : Nat} [NeZero max] : Fintype (Threshold max) :=
  Fintype.ofEquiv (Fin max) ⟨Threshold.mk, Threshold.value, fun _ => rfl, fun ⟨_⟩ => rfl⟩

/-- Coercion: Threshold embeds into Degree via Fin.castSucc -/
instance {max : Nat} : Coe (Threshold max) (Degree max) where
  coe t := ⟨t.value.castSucc⟩

theorem coe_threshold_toNat {max : Nat} (t : Threshold max) :
    (t : Degree max).toNat = t.toNat := rfl

/-- Construct a degree by literal: `deg 5 : Degree 10`. -/
abbrev deg (n : Nat) {max : Nat} (h : n ≤ max := by omega) : Degree max :=
  ⟨⟨n, by omega⟩⟩

/-- Construct a threshold by literal: `thr 5 : Threshold 10`. -/
abbrev thr (n : Nat) {max : Nat} (h : n < max := by omega) : Threshold max :=
  ⟨⟨n, h⟩⟩

-- ════════════════════════════════════════════════════
-- § 12. HasMeasure typeclass (renames HasDegree)
-- ════════════════════════════════════════════════════

/-- Typeclass for entities that have a measurement on some scale.
    The formal semantics "measure function" μ : Entity → α.

    The codomain `α` is polymorphic — heights might use ℚ (cm, exact),
    physical heights ℝ, durations ℕ (ticks), prices ℚ (USD), etc.

    **No `outParam` on α**: master plan v4 deliberately drops `outParam`
    to support multi-dim same-carrier (e.g., `Entity` measured by BOTH
    height and weight). When an `Entity` has multiple measures, consumers
    disambiguate via explicit `(α := ...)` or named instances; mathlib
    `Additive`/`Multiplicative` newtype-wrapping is the canonical pattern
    for type-level disambiguation.

    Renamed from `HasDegree` (legacy name) per master plan v4 Phase A.7.
    Field name kept as `degree` for one-version migration compatibility;
    `HasMeasure.measure` is provided as the v4-canonical alias. -/
class HasMeasure (E : Type) (α : Type) where
  degree : E → α

/-- v4-canonical name for the measurement function. Aliased to the
    legacy field name `degree` for one-version migration. -/
abbrev HasMeasure.measure {E α : Type} [HasMeasure E α] : E → α :=
  HasMeasure.degree

/-- Deprecation alias: `HasDegree` is the legacy name for `HasMeasure`.
    One-version migration alias; will be removed in a follow-up refactor. -/
abbrev HasDegree (E : Type) (α : Type) := HasMeasure E α

/-- Explicit alias for the legacy field projection `HasDegree.degree`.
    Needed because Lean does not auto-derive projection names through abbrevs. -/
abbrev HasDegree.degree {E α : Type} [HasDegree E α] : E → α :=
  HasMeasure.degree

end Core.Scale
