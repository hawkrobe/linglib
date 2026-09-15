import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Order.Directed
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.WithBot
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Degree.Polarity

/-!
# Scale boundedness

This file defines `Degree.Boundedness`, the four-way classification of scales by the endpoints
they have, of [kennedy-mcnally-2005] (22) and [kennedy-2007] (59), found independently by
[rotstein-winter-2004]. A boundedness is the endpoint profile of an order: `Boundedness.ofOrder D`
reads it off the order `D` from the existence of a least and a greatest element, so that a scale's
tag is a fact about its degrees. The tag itself is what a lexical entry stores, since a record
field cannot hold an `OrderTop` instance, and `Boundedness.degreeShape` is a canonical linear order
of each shape, a section of `ofOrder`.

The negative member of an antonym pair measures on the same degrees under the inverse ordering
([kennedy-2007] (60) and fn. 29, [kennedy-mcnally-2005] fn. 7). `Boundedness.dual` is that
operation on tags, and `ofOrder_orderDual` identifies it with mathlib's order dual; the sign
group `Polarity` acts on tags through it, `p • b` being the scale the `p` member of an antonym
pair on `b` measures on. `withMin` and `withMax` adjoin an endpoint, the shapes of the
rays `Set.Ici a` and `Set.Iic a`.

## Main definitions

* `Boundedness`, with the endpoint predicates `HasMin` and `HasMax`.
* `Boundedness.ofOrder`: the boundedness of an order.
* `Boundedness.dual`, `Boundedness.withMin`, `Boundedness.withMax`: the ends exchanged, a least
  degree adjoined, a greatest degree adjoined.
* `Boundedness.degreeShape`: a linear order of each boundedness.
* The `MulAction Polarity Boundedness` instance: the negative member of an antonym pair
  measures on the dual.

## Main results

* `Boundedness.ofOrder_orderDual`, `Boundedness.ofOrder_Ici`, `Boundedness.ofOrder_Iic`: the
  order dual and the two rays have the dual, `withMin` and `withMax` boundedness.
* `Boundedness.ofOrder_degreeShape`: every boundedness is that of a linear order.

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
* [rotstein-winter-2004]
-/

namespace Degree

/-- Which endpoints a scale has ([kennedy-mcnally-2005] (22), [kennedy-2007] (59)). Open
scales may further approach a value without reaching it or be unbounded ([kennedy-2007]
fn. 28); the tag does not record that. -/
inductive Boundedness where
  | open_        -- neither endpoint: *tall*
  | lowerBounded -- a minimum, no maximum: *wet*
  | upperBounded -- a maximum, no minimum: *dry*
  | closed       -- both: *full*
  deriving DecidableEq, Repr, Fintype

namespace Boundedness

/-! ### Endpoints -/

/-- The scale has a minimum. -/
def HasMin : Boundedness → Prop
  | .lowerBounded | .closed => True
  | .open_ | .upperBounded => False

/-- The scale has a maximum. -/
def HasMax : Boundedness → Prop
  | .upperBounded | .closed => True
  | .open_ | .lowerBounded => False

instance : DecidablePred HasMin
  | .open_ | .upperBounded => isFalse id
  | .lowerBounded | .closed => isTrue trivial

instance : DecidablePred HasMax
  | .open_ | .lowerBounded => isFalse id
  | .upperBounded | .closed => isTrue trivial

/-- A boundedness is determined by which endpoints it has. -/
@[ext] theorem ext {b c : Boundedness} (hmin : b.HasMin ↔ c.HasMin) (hmax : b.HasMax ↔ c.HasMax) :
    b = c := by
  revert hmin hmax; cases b <;> cases c <;> decide

/-! ### The boundedness of an order -/

section OfOrder
variable {D : Type*}

open Classical in
/-- The boundedness of an order: which of a least and a greatest element it has. -/
noncomputable def ofOrder (D : Type*) [LE D] : Boundedness :=
  if ∃ m : D, IsBot m then if ∃ m : D, IsTop m then closed else lowerBounded
  else if ∃ m : D, IsTop m then upperBounded else open_

section LE
variable [LE D]

theorem hasMin_ofOrder : (ofOrder D).HasMin ↔ ∃ m : D, IsBot m := by
  unfold ofOrder; split_ifs <;> simp [HasMin, *]

theorem hasMax_ofOrder : (ofOrder D).HasMax ↔ ∃ m : D, IsTop m := by
  unfold ofOrder; split_ifs <;> simp [HasMax, *]

@[simp] theorem hasMin_ofOrder_of_orderBot [OrderBot D] : (ofOrder D).HasMin :=
  hasMin_ofOrder.2 ⟨⊥, isBot_bot⟩

@[simp] theorem hasMax_ofOrder_of_orderTop [OrderTop D] : (ofOrder D).HasMax :=
  hasMax_ofOrder.2 ⟨⊤, isTop_top⟩

end LE

section Preorder
variable [Preorder D]

@[simp] theorem not_hasMin_ofOrder [NoMinOrder D] : ¬ (ofOrder D).HasMin :=
  λ h => let ⟨m, hm⟩ := hasMin_ofOrder.1 h; not_isMin m hm.isMin

@[simp] theorem not_hasMax_ofOrder [NoMaxOrder D] : ¬ (ofOrder D).HasMax :=
  λ h => let ⟨m, hm⟩ := hasMax_ofOrder.1 h; not_isMax m hm.isMax

end Preorder
end OfOrder

/-! ### The ends exchanged -/

/-- The antonym's scale: the same degrees with the ends exchanged ([kennedy-2007] (60)). -/
def dual : Boundedness → Boundedness
  | .open_ => .open_
  | .lowerBounded => .upperBounded
  | .upperBounded => .lowerBounded
  | .closed => .closed

@[simp] theorem hasMin_dual {b : Boundedness} : b.dual.HasMin ↔ b.HasMax := by
  cases b <;> exact Iff.rfl

@[simp] theorem hasMax_dual {b : Boundedness} : b.dual.HasMax ↔ b.HasMin := by
  cases b <;> exact Iff.rfl

theorem dual_involutive : Function.Involutive dual := λ b => by cases b <;> rfl

@[simp] theorem dual_dual (b : Boundedness) : b.dual.dual = b := dual_involutive b

/-- Inverting the ordering of the degrees exchanges the ends of the scale: the negative antonym
of [kennedy-2007] fn. 29 and [kennedy-mcnally-2005] fn. 7 measures on the order dual. -/
@[simp] theorem ofOrder_orderDual {D : Type*} [LE D] : ofOrder Dᵒᵈ = (ofOrder D).dual :=
  ext (by simp [hasMin_ofOrder, hasMax_ofOrder, OrderDual.exists])
    (by simp [hasMin_ofOrder, hasMax_ofOrder, OrderDual.exists])

/-! ### An endpoint adjoined -/

/-- A least degree adjoined: the shape of the ray `Set.Ici a` (`ofOrder_Ici`). -/
def withMin : Boundedness → Boundedness
  | .open_ | .lowerBounded => .lowerBounded
  | .upperBounded | .closed => .closed

/-- A greatest degree adjoined: the shape of the ray `Set.Iic a` (`ofOrder_Iic`). -/
def withMax : Boundedness → Boundedness
  | .open_ | .upperBounded => .upperBounded
  | .lowerBounded | .closed => .closed

@[simp] theorem hasMin_withMin (b : Boundedness) : b.withMin.HasMin := by cases b <;> trivial

@[simp] theorem hasMax_withMin {b : Boundedness} : b.withMin.HasMax ↔ b.HasMax := by
  cases b <;> exact Iff.rfl

@[simp] theorem hasMax_withMax (b : Boundedness) : b.withMax.HasMax := by cases b <;> trivial

@[simp] theorem hasMin_withMax {b : Boundedness} : b.withMax.HasMin ↔ b.HasMin := by
  cases b <;> exact Iff.rfl

@[simp] theorem dual_withMin (b : Boundedness) : b.withMin.dual = b.dual.withMax := by
  cases b <;> rfl

@[simp] theorem dual_withMax (b : Boundedness) : b.withMax.dual = b.dual.withMin := by
  cases b <;> rfl

section Ray
variable {D : Type*} [Preorder D] {a : D}

/-- The ray from `a` up has a least degree, `a`, and a greatest one exactly when `D` has. -/
theorem ofOrder_Ici [IsDirectedOrder D] : ofOrder (Set.Ici a) = (ofOrder D).withMin := by
  refine ext (iff_of_true (hasMin_ofOrder.2 ⟨⟨a, le_rfl⟩, λ x => x.2⟩) (hasMin_withMin _)) ?_
  rw [hasMax_ofOrder, hasMax_withMin, hasMax_ofOrder]
  refine ⟨λ ⟨⟨m, _⟩, hm⟩ => ⟨m, λ x => ?_⟩, λ ⟨m, hm⟩ => ⟨⟨m, hm a⟩, λ x => hm x⟩⟩
  obtain ⟨c, hxc, hac⟩ := exists_ge_ge x a
  exact le_trans hxc (hm ⟨c, hac⟩)

/-- The ray from `a` down has a greatest degree, `a`, and a least one exactly when `D` has. -/
theorem ofOrder_Iic [IsCodirectedOrder D] : ofOrder (Set.Iic a) = (ofOrder D).withMax := by
  refine ext ?_ (iff_of_true (hasMax_ofOrder.2 ⟨⟨a, le_rfl⟩, λ x => x.2⟩) (hasMax_withMax _))
  rw [hasMin_ofOrder, hasMin_withMax, hasMin_ofOrder]
  refine ⟨λ ⟨⟨m, _⟩, hm⟩ => ⟨m, λ x => ?_⟩, λ ⟨m, hm⟩ => ⟨⟨m, hm a⟩, λ x => hm x⟩⟩
  obtain ⟨c, hcx, hca⟩ := exists_le_le x a
  exact le_trans (hm ⟨c, hca⟩) hcx

end Ray

/-! ### A linear order of each shape -/

/-- A linear order of each boundedness: the integers with the tagged endpoints adjoined. -/
abbrev degreeShape : Boundedness → Type
  | .open_ => ℤ
  | .lowerBounded => WithBot ℤ
  | .upperBounded => WithTop ℤ
  | .closed => WithTop (WithBot ℤ)

instance instLinearOrderDegreeShape (b : Boundedness) : LinearOrder b.degreeShape := by
  cases b <;> exact inferInstance

/-- `degreeShape` is a section of `ofOrder`: every boundedness is that of a linear order. -/
@[simp] theorem ofOrder_degreeShape : ∀ b : Boundedness, ofOrder b.degreeShape = b
  | .open_ => ext (iff_of_false not_hasMin_ofOrder id) (iff_of_false not_hasMax_ofOrder id)
  | .lowerBounded =>
    ext (iff_of_true hasMin_ofOrder_of_orderBot trivial) (iff_of_false not_hasMax_ofOrder id)
  | .upperBounded =>
    ext (iff_of_false not_hasMin_ofOrder id) (iff_of_true hasMax_ofOrder_of_orderTop trivial)
  | .closed =>
    ext (iff_of_true hasMin_ofOrder_of_orderBot trivial)
      (iff_of_true hasMax_ofOrder_of_orderTop trivial)

theorem exists_isBot_degreeShape (b : Boundedness) : (∃ m : b.degreeShape, IsBot m) ↔ b.HasMin := by
  rw [← hasMin_ofOrder, ofOrder_degreeShape]

theorem exists_isTop_degreeShape (b : Boundedness) : (∃ m : b.degreeShape, IsTop m) ↔ b.HasMax := by
  rw [← hasMax_ofOrder, ofOrder_degreeShape]

end Boundedness

/-! ### The polarity action -/

/-- The negative member of an antonym pair measures on the dual scale. -/
instance : MulAction Polarity Boundedness where
  smul p b := if p = .positive then b else b.dual
  one_smul _ := rfl
  mul_smul p q b := by
    rcases Polarity.eq_positive_or_eq_negative p with rfl | rfl <;>
      rcases Polarity.eq_positive_or_eq_negative q with rfl | rfl <;> simp [HSMul.hSMul, SMul.smul]

@[simp] theorem Boundedness.negative_smul (b : Boundedness) : Polarity.negative • b = b.dual :=
  rfl

end Degree
