import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Image

/-!
# Rigid designation

An intension over an index type `W` is a function `W → τ`, and it is *rigid* when it takes
the same value at every index: a rigid designator in the sense of Kripke, a stable content
in the sense of Kaplan. `IsRigid` and its set-relativised form `IsRigidOn` are closed under
post- and pre-composition, and rigid intensions that agree at one index agree everywhere,
which is the necessity of identity.

## Main definitions

* `IsRigid f`, `IsRigidOn f S`: constancy of `f : W → τ` everywhere, or on `S`.

## Main results

* `IsRigid.eq_of_apply_eq`: rigid intensions that agree at one index are equal.
* `IsRigid.map`, `IsRigid.precomp`, `IsRigidOn.precomp`: closure under composition.

## References

* [S. Kripke, *Naming and Necessity* (1980)][kripke-1980]
* [D. Kaplan, *Demonstratives* (1989)][kaplan-1989]
* [D. Gallin, *Intensional and Higher-Order Modal Logic* (1975)][gallin-1975]
-/

namespace Reference

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

end Reference
