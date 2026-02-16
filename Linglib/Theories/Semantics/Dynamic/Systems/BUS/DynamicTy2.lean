/-
# BUS Embedding into Dynamic Ty2

BUS is ORTHOGONAL to Dynamic Ty2 - it adds bilateral structure
(positive/negative dimensions) to any dynamic system.

## The Structure

BUS adds a layer on top of Dynamic Ty2:
- Base: DRS S = S → S → Prop (from Dynamic Ty2)
- BUS: BilateralDRS S = { positive : DRS S, negative : DRS S }

Negation swaps dimensions, giving DNE definitionally.

## References

- Elliott (2023). Donkey disjunctions and overlapping updates.
- Elliott & Sudo (2025). Free choice with anaphora.
-/

import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2
import Linglib.Theories.Semantics.Dynamic.Effects.Bilateral.Basic
import Linglib.Theories.Semantics.Dynamic.Systems.BUS.Basic

namespace Semantics.Dynamic.BUS

open Semantics.Dynamic.Core
open Semantics.Dynamic.Core.DynamicTy2


/--
Bilateral DRS: positive and negative DRS meanings.
This is Dynamic Ty2 lifted to bilateral form.
-/
structure BilateralDRS (S : Type*) where
  positive : DRS S
  negative : DRS S

namespace BilateralDRS

variable {S : Type*}


/-- Bilateral test -/
def btest (C : Condition S) : BilateralDRS S :=
  { positive := test C
  , negative := test (λ i => ¬C i) }

/-- Bilateral negation: swap -/
def bneg (D : BilateralDRS S) : BilateralDRS S :=
  { positive := D.negative, negative := D.positive }

prefix:max "∼ᵇ" => bneg

/-- DNE is definitional -/
@[simp] theorem bneg_bneg (D : BilateralDRS S) : ∼ᵇ(∼ᵇD) = D := rfl

/-- Bilateral sequencing -/
def bseq (D₁ D₂ : BilateralDRS S) : BilateralDRS S :=
  { positive := dseq D₁.positive D₂.positive
  , negative := λ i j =>
      D₁.negative i j ∨ (∃ k, D₁.positive i k ∧ D₂.negative k j) }

infixl:65 " ⨟ᵇ " => bseq

/-- Bilateral disjunction -/
def bdisj (D₁ D₂ : BilateralDRS S) : BilateralDRS S :=
  { positive := λ i j => D₁.positive i j ∨ D₂.positive i j
  , negative := λ i j => D₁.negative i j ∧ D₂.negative i j }


/--
Lift unilateral DRS to bilateral with complement negation.
This is how standard dynamic systems embed into BUS.
-/
def ofDRS (D : DRS S) : BilateralDRS S :=
  { positive := D
  , negative := λ i j => i = j ∧ ¬∃ k, D i k }

/-- The positive dimension preserves the original DRS -/
theorem ofDRS_positive (D : DRS S) : (ofDRS D).positive = D := rfl

/-- The negative dimension is the test-based negation -/
theorem ofDRS_negative (D : DRS S) : (ofDRS D).negative = test (dneg D) := by
  ext i j
  simp only [ofDRS, test, dneg, eq_iff_iff]
  constructor
  · intro ⟨heq, hnex⟩; exact ⟨heq, by rw [← heq]; exact hnex⟩
  · intro ⟨heq, hnex⟩; exact ⟨heq, by rw [heq]; exact hnex⟩


/-!
BilateralDen (from Core.Bilateral) uses InfoStates:
  BilateralDen W E = { positive, negative : InfoState W E → InfoState W E }

BilateralDRS uses DRS directly:
  BilateralDRS S = { positive, negative : S → S → Prop }

For worldless systems (W = Unit), we can relate them via:
  InfoState Unit E ≅ Set (Nat → E)
  CCP Unit E = InfoState Unit E → InfoState Unit E

The relation: a DRS D : S → S → Prop induces a CCP:
  λ s => { j | ∃ i ∈ s, D i j }
-/

/-- Convert DRS to CCP (set-based update) -/
def drsToUpdate {S : Type*} (D : DRS S) : Set S → Set S :=
  λ s => { j | ∃ i ∈ s, D i j }

/-- BilateralDRS induces pair of CCPs -/
def toUpdatePair (D : BilateralDRS S) : (Set S → Set S) × (Set S → Set S) :=
  (drsToUpdate D.positive, drsToUpdate D.negative)

end BilateralDRS


/--
BUS negation preserves DNE at the DRS level.
This is the formal content of "bathroom sentences work in BUS".
-/
theorem bus_dne {S : Type*} (D : BilateralDRS S) :
    (BilateralDRS.bneg (BilateralDRS.bneg D)).positive = D.positive := rfl

/--
Sequencing positive dimensions is associative.
-/
theorem bseq_positive_assoc {S : Type*} (D₁ D₂ D₃ : BilateralDRS S) :
    ((D₁.bseq D₂).bseq D₃).positive = (D₁.bseq (D₂.bseq D₃)).positive := by
  ext i j
  simp only [BilateralDRS.bseq, dseq]
  constructor
  · intro ⟨h, ⟨h', hD₁, hD₂⟩, hD₃⟩; exact ⟨h', hD₁, h, hD₂, hD₃⟩
  · intro ⟨h', hD₁, h, hD₂, hD₃⟩; exact ⟨h, ⟨h', hD₁, hD₂⟩, hD₃⟩

end Semantics.Dynamic.BUS
