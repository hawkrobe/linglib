/-
# Bilateral Update Semantics (Elliott 2023; Elliott & Sudo 2025)

Dynamic semantics with two update dimensions (positive and negative) that validates DNE and handles cross-disjunct anaphora.

## Main definitions

`BUSDen`, `hasGap`, `defined`, `strawsonEntails`, `strongEntails`

## References

- Elliott, P. (2023). Donkey disjunctions and overlapping updates. SALT 33: 666-685.
- Elliott, P. & Sudo, Y. (2025). Free choice with anaphora. Semantics & Pragmatics 18.
-/

import Linglib.Theories.Semantics.Dynamic.Effects.Bilateral.Basic

namespace DynamicSemantics.BUS

open DynamicSemantics.Core

export BilateralDen (atom neg conj disj exists_ existsFull forall_ pred1 pred2
  supports entails toPair ofPair toUnilateral)

/-- BUS denotation as bilateral denotation. -/
abbrev BUSDen (W : Type*) (E : Type*) := BilateralDen W E

namespace BUSDen

variable {W E : Type*}

/-- Truth-value gap: presupposition failure. -/
def hasGap (φ : BUSDen W E) (s : InfoState W E) : Prop :=
  φ.positive s ∪ φ.negative s ⊂ s

/-- Sentence is defined (no presupposition failure). -/
def defined (φ : BUSDen W E) (s : InfoState W E) : Prop :=
  φ.positive s ∪ φ.negative s = s

/-- Strong Kleene conjunction. -/
def skConj (φ ψ : BUSDen W E) : BUSDen W E := BilateralDen.conj φ ψ

/-- Presupposition-preserving conjunction. -/
def pConj (φ ψ : BUSDen W E) : BUSDen W E :=
  { positive := λ s => ψ.positive (φ.positive s)
  , negative := λ s =>
      φ.negative s ∪ (s \ (φ.positive s ∪ φ.negative s)) ∪
        (φ.positive s ∩ ψ.negative (φ.positive s)) }

/-- Strawson entailment: φ entails ψ when φ is defined and true. -/
def strawsonEntails (φ ψ : BUSDen W E) : Prop :=
  ∀ s : InfoState W E,
    defined φ s →
    (φ.positive s).consistent →
    (φ.positive s) ⊆ ψ.positive (φ.positive s)

/-- Strong entailment: φ entails ψ with no presupposition failure. -/
def strongEntails (φ ψ : BUSDen W E) : Prop :=
  ∀ s : InfoState W E,
    (φ.positive s).consistent →
    defined ψ (φ.positive s) ∧
    (φ.positive s) ⊆ ψ.positive (φ.positive s)

theorem neg_positive_eq_negative (φ : BUSDen W E) (s : InfoState W E) :
    (BilateralDen.neg φ).positive s = φ.negative s := rfl

theorem neg_negative_eq_positive (φ : BUSDen W E) (s : InfoState W E) :
    (BilateralDen.neg φ).negative s = φ.positive s := rfl

theorem de_morgan_disj_negative (φ ψ : BUSDen W E) (s : InfoState W E) :
    (BilateralDen.disj φ ψ).negative s = φ.negative s ∩ ψ.negative s := rfl
theorem conj_negative (φ ψ : BUSDen W E) (s : InfoState W E) :
    (BilateralDen.conj φ ψ).negative s =
    φ.negative s ∪ (φ.positive s ∩ ψ.negative (φ.positive s)) := rfl

end BUSDen

namespace Compat

/-- Backward compatibility alias. -/
abbrev BilateralDen := DynamicSemantics.Core.BilateralDen

end Compat


end DynamicSemantics.BUS
