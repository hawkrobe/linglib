import Mathlib.Order.Basic
import Mathlib.Order.WithBot
import Mathlib.Order.Nat
import Mathlib.Order.Max
import Mathlib.Order.BoundedOrder.Basic

/-!
# Scale boundedness

The four-way endpoint classification of scales — open, lower closed, upper closed, closed —
of [kennedy-mcnally-2005] (22) and [kennedy-2007] (59), found independently by
[rotstein-winter-2004]. `Boundedness` is the lexical tag a fragment entry stores (a record
field cannot hold an `OrderTop` instance); `degreeShape` is an order carrier of that shape,
with a greatest element exactly when the scale `HasMax`. `dual` is the antonym's scale, the
same degrees with the ends exchanged, and `ScalePolarity` says which member of an antonym
pair an adjective is.

## Main declarations

* `Boundedness`, `Boundedness.HasMax`, `Boundedness.HasMin`, `Boundedness.dual`,
  `Boundedness.ofPolarity`
* `Boundedness.degreeShape`, `Boundedness.hasGreatest_degreeShape_iff`
* `ScalePolarity`
-/

namespace Degree

/-! ### Scale boundedness -/

/-- Which endpoints a scale has ([kennedy-mcnally-2005] (22), [kennedy-2007] (59)). Open
scales may further approach a value without reaching it or be unbounded ([kennedy-2007]
fn. 28); the tag does not record that. -/
inductive Boundedness where
  | open_        -- neither endpoint: *tall*
  | lowerBounded -- a minimum, no maximum: *wet*
  | upperBounded -- a maximum, no minimum: *dry*
  | closed       -- both: *full*
  deriving DecidableEq, Repr

namespace Boundedness

/-- The scale has a maximum. -/
def HasMax : Boundedness → Prop
  | .upperBounded | .closed => True
  | .open_ | .lowerBounded => False

instance : DecidablePred HasMax
  | .open_ => isFalse id
  | .lowerBounded => isFalse id
  | .upperBounded => isTrue trivial
  | .closed => isTrue trivial

/-- The scale has a minimum. -/
def HasMin : Boundedness → Prop
  | .lowerBounded | .closed => True
  | .open_ | .upperBounded => False

instance : DecidablePred HasMin
  | .open_ => isFalse id
  | .lowerBounded => isTrue trivial
  | .upperBounded => isFalse id
  | .closed => isTrue trivial

/-- The antonym's scale: the same degrees with the ends exchanged ([kennedy-2007] (61)). -/
def dual : Boundedness → Boundedness
  | .open_ => .open_
  | .lowerBounded => .upperBounded
  | .upperBounded => .lowerBounded
  | .closed => .closed

@[simp] theorem dual_dual (b : Boundedness) : b.dual.dual = b := by cases b <;> rfl

@[simp] theorem hasMax_dual {b : Boundedness} : b.dual.HasMax ↔ b.HasMin := by
  cases b <;> exact Iff.rfl

@[simp] theorem hasMin_dual {b : Boundedness} : b.dual.HasMin ↔ b.HasMax := by
  cases b <;> exact Iff.rfl

/-! ### Degree carrier per scale shape

A computable order carrier for each shape — only the `OrderTop`/`NoMaxOrder` mixin matters,
not the carrier. The grounding is proved once here; per-dimension views transport it
(`Features.ScalarDimension.degree`). -/

/-- Degree carrier per boundedness shape: a greatest element exists exactly when the scale
`HasMax`. -/
abbrev degreeShape : Boundedness → Type
  | .open_ | .lowerBounded => ℕ
  | .upperBounded | .closed => WithTop ℕ

instance instLinearOrderDegreeShape (b : Boundedness) : LinearOrder b.degreeShape := by
  cases b <;> exact inferInstance

/-- A greatest degree exists exactly when the classification says `HasMax`. -/
theorem hasGreatest_degreeShape_iff (b : Boundedness) :
    (∃ m : b.degreeShape, IsTop m) ↔ b.HasMax := by
  cases b
  · exact iff_of_false (fun ⟨m, hm⟩ => not_isMax m hm.isMax) (by decide)
  · exact iff_of_false (fun ⟨m, hm⟩ => not_isMax m hm.isMax) (by decide)
  · exact iff_of_true ⟨⊤, isTop_top⟩ (by decide)
  · exact iff_of_true ⟨⊤, isTop_top⟩ (by decide)

end Boundedness

/-! ### Scale polarity -/

/-- Intrinsic polarity of a scale dimension: `positive` is the unmarked direction (*tall*,
*hot*), `negative` the inverted one (*short*, *cold*). -/
inductive ScalePolarity where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The scale an adjective measures on: its dimension's scale for the positive member of an
antonym pair, the same scale with the ends exchanged for the negative member. -/
def Boundedness.ofPolarity (b : Boundedness) : ScalePolarity → Boundedness
  | .positive => b
  | .negative => b.dual

@[simp] theorem Boundedness.ofPolarity_positive (b : Boundedness) :
    b.ofPolarity .positive = b := rfl

@[simp] theorem Boundedness.ofPolarity_negative (b : Boundedness) :
    b.ofPolarity .negative = b.dual := rfl

end Degree
