module

public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Polarity

The polarity of an expression is positive or negative. The two polarities form the group of order
two, a negation cancelling a negation; they are the units of `ℤ` (`Polarity.unitsEquiv`). Each
notion of polarity in the library is an action of this one group:

* the polarity of a sentence acts on propositions, the negative polarity by complement
  (`negative • p = pᶜ`);
* the polarity of an antonym acts on degrees by negation (`negative • x = -x`) and on scales by
  duality (`Semantics/Degree/Antonymy`);
* the relative polarity of a response to an antecedent, [same] or [reverse], is the product of
  their polarities;
* the direction of a function, strictly monotone or strictly antitone (`StrictDirected`), with
  directions composing as polarities multiply.

Since these are one group acting in different ways, their interaction is statable: the negative
antonym *short* measures on the dual scale of *tall*, while sentential negation takes the
complement, so *not short* does not entail *tall*.

Two other notions called polarity are distinct types: `UD.Polarity`, a morphological feature of
the annotation scheme, and `NaturalLogic.ContextPolarity`, the monotonicity of a context, which
adds a non-monotone value absorbing the others and into which a polarity maps, negation being
downward (`NaturalLogic.ContextPolarity.ofPolarity`).
-/

@[expose] public section

/-- The polarity of an expression: positive or negative. -/
inductive Polarity where
  | positive
  | negative
  deriving Repr, DecidableEq, Inhabited, Fintype

namespace Polarity

instance : One Polarity where
  one := positive

/-- Composition of polarities: two negations cancel. -/
instance : Mul Polarity where
  mul
    | positive, s => s
    | negative, positive => negative
    | negative, negative => positive

/-- The polarities form the group of order two, each polarity its own inverse. -/
instance : CommGroup Polarity where
  inv := id
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide
  mul_comm := by decide

@[simp] theorem one_eq_positive : (1 : Polarity) = positive := rfl

@[simp] theorem inv_eq_self (s : Polarity) : s⁻¹ = s := rfl

@[simp] theorem mul_self (s : Polarity) : s * s = positive := by cases s <;> rfl

@[simp] theorem positive_mul (s : Polarity) : positive * s = s := rfl

@[simp] theorem mul_positive (s : Polarity) : s * positive = s := mul_one s

/-- The polarities are the units of `ℤ`, `positive` being `1` and `negative` being `-1`. -/
def unitsEquiv : Polarity ≃* ℤˣ where
  toFun
    | positive => 1
    | negative => -1
  invFun u := if u = 1 then positive else negative
  left_inv s := by cases s <;> decide
  right_inv u := by rcases Int.units_eq_one_or u with rfl | rfl <;> decide
  map_mul' s t := by cases s <;> cases t <;> decide

@[simp] theorem positive_smul {M : Type*} [MulAction Polarity M] (x : M) : positive • x = x :=
  one_smul _ x

variable {α : Type*}

/-- The polarity of a sentence acts on propositions: the positive polarity leaves a proposition,
the negative one takes its complement. -/
instance : MulAction Polarity (Set α) where
  smul
    | positive, p => p
    | negative, p => pᶜ
  one_smul _ := rfl
  mul_smul s t p := by cases s <;> cases t <;> first | rfl | exact (compl_compl p).symm

@[simp] theorem negative_smul_set (p : Set α) : negative • p = pᶜ := rfl

/-- A polarity acts on an additive group through the units of `ℤ`: the negative polarity
negates. -/
instance [AddCommGroup α] : MulAction Polarity α :=
  MulAction.compHom α unitsEquiv.toMonoidHom

@[simp] theorem negative_smul [AddCommGroup α] (x : α) : negative • x = -x :=
  show ((-1 : ℤˣ) : ℤ) • x = -x by simp

section Directed

variable {α β γ : Type*} [Preorder α] [Preorder β] [Preorder γ]

/-- A function directed by a polarity: strictly monotone under the positive polarity, strictly
antitone under the negative one. -/
def StrictDirected : Polarity → (α → β) → Prop
  | positive, f => StrictMono f
  | negative, f => StrictAnti f

/-- Directions compose as polarities multiply. -/
theorem StrictDirected.comp {s t : Polarity} {g : β → γ} {f : α → β} (hg : s.StrictDirected g)
    (hf : t.StrictDirected f) : (s * t).StrictDirected (g ∘ f) := by
  cases s <;> cases t
  exacts [StrictMono.comp hg hf, StrictMono.comp_strictAnti hg hf,
    StrictAnti.comp_strictMono hg hf, StrictAnti.comp hg hf]

end Directed

end Polarity
