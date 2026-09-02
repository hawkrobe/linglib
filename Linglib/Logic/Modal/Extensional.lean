import Mathlib.Logic.Function.Basic

/-!
# Extensional operators

An operator `O` on intensions `W → α` is *extensional at* `w` when its value at `w` depends on
its argument only through the argument's extension at `w`, i.e. `O · w` factors through
evaluation at `w`. The pointwise connectives are extensional; quantifiers over indices such as
`ModalLogic.nec` are not. Extensionality is closed under the pointwise connectives and under
composition, so scope-inertness lifts through a whole stack of extensional operators.

## Main definitions

* `IsExtensionalAt O w`, `IsExtensional O`: local truth-functionality of an operator.

## Main results

* `IsExtensionalAt.and`, `IsExtensionalAt.or`, `IsExtensionalAt.not`,
  `IsExtensionalAt.comp`: closure of extensional operators.
-/

namespace ModalLogic

variable {W α β : Type*}

/-- `O` is extensional at `w`: its value at `w` depends on the argument intension only
through the argument's extension at `w`, i.e. `O · w` factors through evaluation at `w`. -/
def IsExtensionalAt (O : (W → α) → W → β) (w : W) : Prop :=
  ∀ p q : W → α, p w = q w → O p w = O q w

/-- `O` is extensional at every index. -/
def IsExtensional (O : (W → α) → W → β) : Prop :=
  ∀ w, IsExtensionalAt O w

theorem isExtensionalAt_iff_factorsThrough (O : (W → α) → W → β) (w : W) :
    IsExtensionalAt O w ↔ Function.FactorsThrough (O · w) (· w) :=
  ⟨fun h _ _ hpq => h _ _ hpq, fun h _ _ hpq => h hpq⟩

theorem not_isExtensionalAt_iff_exists_witness {O : (W → α) → W → β} {w : W} :
    ¬ IsExtensionalAt O w ↔ ∃ p q, p w = q w ∧ O p w ≠ O q w := by
  simp only [IsExtensionalAt, not_forall, exists_prop]

namespace IsExtensionalAt

variable {w : W}

theorem eval : IsExtensionalAt (fun (p : W → α) w' => p w') w :=
  fun _ _ hpq => hpq

theorem const (P : W → Prop) : IsExtensionalAt (fun (_ : W → α) w' => P w') w :=
  fun _ _ _ => rfl

/-- Pointwise negation is extensional: negation is not an intensional operator. -/
theorem neg : IsExtensionalAt (fun p (w' : W) => ¬ p w') w :=
  fun _ _ hpq => congrArg Not hpq

theorem and {O₁ O₂ : (W → α) → W → Prop} (h₁ : IsExtensionalAt O₁ w)
    (h₂ : IsExtensionalAt O₂ w) : IsExtensionalAt (fun p w' => O₁ p w' ∧ O₂ p w') w :=
  fun p q hpq => congrArg₂ And (h₁ p q hpq) (h₂ p q hpq)

theorem or {O₁ O₂ : (W → α) → W → Prop} (h₁ : IsExtensionalAt O₁ w)
    (h₂ : IsExtensionalAt O₂ w) : IsExtensionalAt (fun p w' => O₁ p w' ∨ O₂ p w') w :=
  fun p q hpq => congrArg₂ Or (h₁ p q hpq) (h₂ p q hpq)

theorem not {O : (W → α) → W → Prop} (h : IsExtensionalAt O w) :
    IsExtensionalAt (fun p w' => ¬ O p w') w :=
  fun p q hpq => congrArg Not (h p q hpq)

/-- Extensional operators compose: scope-inertness lifts through a stack of them. -/
theorem comp {O₁ : (W → α) → W → β} {O₂ : (W → β) → W → Prop}
    (h₂ : IsExtensionalAt O₂ w) (h₁ : IsExtensionalAt O₁ w) :
    IsExtensionalAt (fun p w' => O₂ (fun s => O₁ p s) w') w :=
  fun p q hpq => h₂ _ _ (h₁ p q hpq)

end IsExtensionalAt

end ModalLogic
