import Mathlib.Order.BoundedOrder.Basic
import Linglib.Core.Order.Comparison
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.NormNum

/-!
# Discrete degree carriers

The finite, `Fin`-backed scale carriers used by RSA fragments and
computational Studies [kennedy-2007] [heim-2001] [kennedy-mcnally-2005]:
`Bounded max` / `Threshold max` with their order/`Fintype` instances, and
the threshold-comparison predicates (*tall* / *short* / *not tall*).
The abstract theory works with plain measure functions `μ : E → D` into
a preorder (`Comparative.lean`, `Extent.lean`); this module is its
decidable discretization.

## Main definitions

* `Bounded max`, `Threshold max` — discrete bounded scale types.
* `deg`, `thr` — literal constructors.
* `positiveMeaning`, `negativeMeaning`, `notPositiveMeaning` — the three
  opposition relations as decidable threshold comparisons.
-/

namespace Degree

/-! ### Discrete bounded scales -/

/-- A degree on a scale from 0 to `max` — a discretized continuous value
    (height, temperature, …). -/
structure Bounded (max : Nat) where
  value : Fin (max + 1)
  deriving Repr, DecidableEq

instance {n : Nat} : Inhabited (Bounded n) := ⟨⟨0, Nat.zero_lt_succ n⟩⟩

/-- `Bounded max` inherits a linear order from `Fin (max + 1)`. -/
instance {max : Nat} : LinearOrder (Bounded max) :=
  LinearOrder.lift' Bounded.value (fun a b h => by cases a; cases b; simp_all)

/-- `Bounded max` is bounded: 0 is the minimum, `max` the maximum. -/
instance {max : Nat} : BoundedOrder (Bounded max) where
  top := ⟨Fin.last max⟩
  le_top d := Fin.le_last d.value
  bot := ⟨0, Nat.zero_lt_succ max⟩
  bot_le d := Fin.zero_le d.value

/-- All degrees from 0 to `max`. -/
def allDegrees (max : Nat) : List (Bounded max) :=
  List.finRange (max + 1) |>.map (⟨·⟩)

/-- Bounded from `Nat` (clamped to `max`). -/
def Bounded.ofNat (max : Nat) (n : Nat) : Bounded max :=
  ⟨⟨min n max, by omega⟩⟩

/-- The numeric value of a degree. -/
def Bounded.toNat {max : Nat} (d : Bounded max) : Nat := d.value.val

/-- A threshold for a gradable adjective: `x` is "tall" iff `degree x > threshold`. -/
structure Threshold (max : Nat) where
  value : Fin max
  deriving Repr, DecidableEq

instance {n : Nat} [NeZero n] : Inhabited (Threshold n) :=
  ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩

/-- `Threshold max` inherits a linear order from `Fin max`. -/
instance {max : Nat} : LinearOrder (Threshold max) :=
  LinearOrder.lift' Threshold.value (fun a b h => by cases a; cases b; simp_all)

/-- All thresholds from 0 to `max - 1`. -/
def allThresholds (max : Nat) (_ : 0 < max := by omega) : List (Threshold max) :=
  List.finRange max |>.map (⟨·⟩)

/-- The numeric value of a threshold. -/
def Threshold.toNat {max : Nat} (t : Threshold max) : Nat := t.value.val

instance {max : Nat} : Fintype (Bounded max) :=
  Fintype.ofEquiv (Fin (max + 1)) ⟨Bounded.mk, Bounded.value, fun _ => rfl, fun ⟨_⟩ => rfl⟩

instance {max : Nat} [NeZero max] : Fintype (Threshold max) :=
  Fintype.ofEquiv (Fin max) ⟨Threshold.mk, Threshold.value, fun _ => rfl, fun ⟨_⟩ => rfl⟩

/-- Coercion: a `Threshold` embeds into `Bounded` via `Fin.castSucc`. -/
instance {max : Nat} : Coe (Threshold max) (Bounded max) where
  coe t := ⟨t.value.castSucc⟩

theorem coe_threshold_toNat {max : Nat} (t : Threshold max) :
    (t : Bounded max).toNat = t.toNat := rfl

/-- Construct a degree by literal: `deg 5 : Bounded 10`. -/
abbrev deg (n : Nat) {max : Nat} (h : n ≤ max := by omega) : Bounded max :=
  ⟨⟨n, by omega⟩⟩

/-- Construct a threshold by literal: `thr 5 : Threshold 10`. -/
abbrev thr (n : Nat) {max : Nat} (h : n < max := by omega) : Threshold max :=
  ⟨⟨n, h⟩⟩

/-! ### Threshold-comparison meanings

General degree operations on the discrete carriers, not
adjective-specific; decidability is inherited from the underlying
`Fin` order. -/

section Concrete

variable {max : Nat}

/-- Positive form (*tall*): `t < d` — the strict threshold face of
`Core.Order.Comparison.gt.over` on the discrete carrier. -/
def positiveMeaning (d : Bounded max) (t : Threshold max) : Prop :=
  d ∈ Core.Order.Comparison.gt.over id (t : Bounded max)

/-- Polar antonym (*short*): `d < t`, evaluated against the antonym's own
threshold (which may sit below the positive's — see `Gradability.ThresholdPair`). -/
def negativeMeaning (d : Bounded max) (t : Threshold max) : Prop :=
  d ∈ Core.Order.Comparison.lt.over id (t : Bounded max)

/-- Contradictory negation (*not tall*): `d ≤ t`, the complement of
`positiveMeaning`. Not the polar antonym — that is `negativeMeaning`. -/
def notPositiveMeaning (d : Bounded max) (t : Threshold max) : Prop :=
  d ∈ Core.Order.Comparison.le.over id (t : Bounded max)

instance (d : Bounded max) (t : Threshold max) : Decidable (positiveMeaning d t) :=
  inferInstanceAs (Decidable ((t : Bounded max) < d))

instance (d : Bounded max) (t : Threshold max) : Decidable (negativeMeaning d t) :=
  inferInstanceAs (Decidable (d < (t : Bounded max)))

instance (d : Bounded max) (t : Threshold max) : Decidable (notPositiveMeaning d t) :=
  inferInstanceAs (Decidable (d ≤ (t : Bounded max)))

end Concrete

end Degree
