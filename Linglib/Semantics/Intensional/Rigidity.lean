import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Image

/-!
# Rigid intensions and extensional operators

An intension over an index type `W` is a function `W → τ`, and it is *rigid* when it takes
the same value at every index: a rigid designator in the sense of Kripke, a stable content
in the sense of Kaplan. `IsRigid` and its set-relativised form `IsRigidOn` are closed under
post- and pre-composition, and rigid intensions that agree at one index agree everywhere,
which is the necessity of identity. On the operator side, `IsExtensionalAt O w` says that
an operator on intensions reads its argument only through the argument's extension at `w`:
the pointwise connectives are extensional, quantifiers over indices are not.

## Main definitions

* `IsRigid f`, `IsRigidOn f S`: constancy of `f : W → τ` everywhere, or on `S`.
* `IsExtensionalAt O w`, `IsExtensional O`: local truth-functionality of an operator.

## Main results

* `IsRigid.eq_of_apply_eq`: rigid intensions that agree at one index are equal.
* `IsRigid.map`, `IsRigid.precomp`, `IsRigidOn.precomp`: closure under composition.
* `IsExtensionalAt.and`, `IsExtensionalAt.or`, `IsExtensionalAt.not`,
  `IsExtensionalAt.comp`: closure of extensional operators.

## References

* [S. Kripke, *Naming and Necessity* (1980)][kripke-1980]
* [D. Kaplan, *Demonstratives* (1989)][kaplan-1989]
* [D. Gallin, *Intensional and Higher-Order Modal Logic* (1975)][gallin-1975]
-/

namespace Intensional

variable {W W' τ τ' : Type*}

/-- An intension is rigid when it takes the same value at every index. -/
def IsRigid (f : W → τ) : Prop := ∀ w₁ w₂, f w₁ = f w₂

/-- An intension is rigid on `S` when it takes the same value at every index in `S`. -/
def IsRigidOn (f : W → τ) (S : Set W) : Prop := ∀ w₁ ∈ S, ∀ w₂ ∈ S, f w₁ = f w₂

theorem isRigid_const (x : τ) : IsRigid fun _ : W => x := fun _ _ => rfl

theorem IsRigid.isRigidOn {f : W → τ} (h : IsRigid f) (S : Set W) : IsRigidOn f S :=
  fun w₁ _ w₂ _ => h w₁ w₂

/-- A rigid intension is the constant function of its value at any index. -/
theorem IsRigid.eq_const {f : W → τ} (h : IsRigid f) (w : W) : f = fun _ => f w :=
  funext fun w' => h w' w

/-- Necessity of identity: rigid intensions that agree at one index are equal. -/
theorem IsRigid.eq_of_apply_eq {f g : W → τ} (hf : IsRigid f) (hg : IsRigid g) {w : W}
    (h : f w = g w) : f = g :=
  funext fun w' => (hf w' w).trans (h.trans (hg w w'))

/-- A non-rigid intension differs from the constant function of any of its values. -/
theorem const_ne_of_not_isRigid {f : W → τ} (h : ¬ IsRigid f) (w : W) :
    (fun _ => f w) ≠ f :=
  fun e => h (e ▸ isRigid_const (f w))

theorem IsRigid.map {f : W → τ} (h : IsRigid f) (g : τ → τ') : IsRigid (g ∘ f) :=
  fun w₁ w₂ => congrArg g (h w₁ w₂)

theorem IsRigid.precomp {f : W → τ} (h : IsRigid f) (g : W' → W) : IsRigid (f ∘ g) :=
  fun w₁ w₂ => h (g w₁) (g w₂)

theorem IsRigidOn.precomp {f : W → τ} {S : Set W} (h : IsRigidOn f S) (g : W' → W) :
    IsRigidOn (f ∘ g) (g ⁻¹' S) :=
  fun w₁ hw₁ w₂ hw₂ => h (g w₁) hw₁ (g w₂) hw₂

/-! ### Extensional operators -/

variable {α β : Type*}

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

end Intensional
