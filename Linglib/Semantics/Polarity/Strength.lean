/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Basic

/-!
# The Zwarts hierarchy of negative strength

The strengths of negation a context can carry, ordered as the chain `weak < antiAdditive <
antiMorphic` ([zwarts-1998]; [vanderwouden-1997]'s minimal, regular and classical negation):
a context is weakly negative when it is downward entailing, anti-additive when it also turns
disjunctions into conjunctions, and anti-morphic when it also turns conjunctions into
disjunctions, as clausal negation does. Each strength is the function class of a natural-logic
signature (`DEStrength.toSignature`), so its semantic content is `Signature.HoldsFor`, with the
unit conditions that keep a constant map from holding every strength, and a signature realizes a
strength through its projection behavior (`Signature.toDEStrength`).

## Main declarations

* `PolarityItem.DEStrength`: the three strengths, a linear order.
* `PolarityItem.DEStrength.toSignature`: the signature whose function class a strength is.
* `NaturalLogic.Signature.toDEStrength`: the strength a signature realizes, `⊥` for a
  signature that is not downward entailing.
* `NaturalLogic.Signature.toDEStrength_ne_bot_iff`: a signature realizes a strength exactly
  when it is downward entailing.

## References

* [zwarts-1998]
* [vanderwouden-1997]
* [icard-2012]
* [ladusaw-1979]
-/

@[expose] public section

namespace PolarityItem

open NaturalLogic

/-! ### The hierarchy -/

/-- The three strengths of negation ([zwarts-1998]): `weak` is plain downward entailment,
`antiAdditive` adds the ∨→∧ distributivity of *nobody*, and `antiMorphic` the ∧→∨
distributivity of clausal negation. -/
inductive DEStrength where
  | weak
  | antiAdditive
  | antiMorphic
  deriving DecidableEq, Repr, Fintype

/-- Rank in the chain `weak < antiAdditive < antiMorphic`. -/
def DEStrength.toNat : DEStrength → ℕ
  | .weak => 0
  | .antiAdditive => 1
  | .antiMorphic => 2

theorem DEStrength.toNat_injective : Function.Injective DEStrength.toNat := by decide

/-- The Zwarts hierarchy as the linear order `weak < antiAdditive < antiMorphic`. -/
instance : LinearOrder DEStrength :=
  LinearOrder.lift' DEStrength.toNat DEStrength.toNat_injective

/-- The natural-logic signature whose function class a strength of negation is: an antitone, an
anti-additive or an anti-morphic map, with the unit conditions of [icard-2012]. -/
def DEStrength.toSignature : DEStrength → Signature
  | .weak => .anti
  | .antiAdditive => .antiAdd
  | .antiMorphic => .antiAddMult

/-- A stronger strength is a more specific signature. -/
theorem DEStrength.toSignature_antitone : Antitone DEStrength.toSignature := by
  intro a b h; cases a <;> cases b <;> first | exact absurd h (by decide) | decide

end PolarityItem

/-! ### Signatures and strength -/

namespace NaturalLogic.Signature

open PolarityItem

/-- `toDEStrength φ` is the strength of negation the signature `φ` realizes, `⊥` when `φ` is not
downward entailing. It is read off `project`: a signature is downward entailing when it reverses
forward entailment, anti-additive when it also turns `cover` into `alternation`, and anti-morphic
when it also turns `alternation` into `cover`. -/
def toDEStrength (φ : Signature) : WithBot DEStrength :=
  if project .forward φ != .reverse then ⊥
  else if project .cover φ == .alternation then
    if project .alternation φ == .cover then DEStrength.antiMorphic
    else DEStrength.antiAdditive
  else DEStrength.weak

example : toDEStrength .anti = DEStrength.weak := rfl
example : toDEStrength .antiAdd = DEStrength.antiAdditive := rfl
example : toDEStrength .antiMult = DEStrength.weak := rfl
example : toDEStrength .antiAddMult = DEStrength.antiMorphic := rfl
example : toDEStrength .mono = ⊥ := rfl

/-- A signature realizes a strength of negation exactly when it is downward entailing
([ladusaw-1979]). -/
theorem toDEStrength_ne_bot_iff (σ : Signature) : σ.toDEStrength ≠ ⊥ ↔ σ.sign = -1 := by
  cases σ <;> decide

/-- A strength is the one its signature realizes. -/
theorem toDEStrength_toSignature (s : DEStrength) : s.toSignature.toDEStrength = s := by
  cases s <;> rfl

end NaturalLogic.Signature
