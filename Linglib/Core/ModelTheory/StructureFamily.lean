import Linglib.Core.ModelTheory.Binders

/-!
# Satisfaction in an indexed family of structures

Classical satisfaction at an index of a structure family
`interp : W → L.Structure M` — mathlib's `Formula.Realize` with the
instance selected per index — and the transport of the `Formula.realize_*`
simp set. `[UPSTREAM]` candidate for `Mathlib/ModelTheory`, which carries
one structure at a time.
-/

namespace FirstOrder.Language

variable {L : Language} {W M α : Type*}

/-- Satisfaction at an index of a structure family: mathlib's
    `Formula.Realize` in the structure the family carries at `w`. -/
def Formula.RealizeAt (ψ : L.Formula α) (interp : W → L.Structure M)
    (w : W) (v : α → M) : Prop :=
  letI := interp w; ψ.Realize v

variable (interp : W → L.Structure M) (w : W) (v : α → M)

@[simp] theorem Formula.realizeAt_not (ψ : L.Formula α) :
    ψ.not.RealizeAt interp w v ↔ ¬ ψ.RealizeAt interp w v :=
  letI := interp w
  Formula.realize_not

@[simp] theorem Formula.realizeAt_inf (ψ₁ ψ₂ : L.Formula α) :
    (ψ₁ ⊓ ψ₂).RealizeAt interp w v ↔
      ψ₁.RealizeAt interp w v ∧ ψ₂.RealizeAt interp w v :=
  letI := interp w
  Formula.realize_inf

@[simp] theorem Formula.realizeAt_sup (ψ₁ ψ₂ : L.Formula α) :
    (ψ₁ ⊔ ψ₂).RealizeAt interp w v ↔
      ψ₁.RealizeAt interp w v ∨ ψ₂.RealizeAt interp w v :=
  letI := interp w
  Formula.realize_sup

section Binders

variable [DecidableEq α]

@[simp] theorem Formula.realizeAt_all₁ (x : α) (ψ : L.Formula α) :
    (Formula.all₁ x ψ).RealizeAt interp w v ↔
      ∀ d : M, ψ.RealizeAt interp w (Function.update v x d) :=
  letI := interp w
  Formula.realize_all₁

@[simp] theorem Formula.realizeAt_ex₁ (x : α) (ψ : L.Formula α) :
    (Formula.ex₁ x ψ).RealizeAt interp w v ↔
      ∃ d : M, ψ.RealizeAt interp w (Function.update v x d) :=
  letI := interp w
  Formula.realize_ex₁

end Binders

end FirstOrder.Language
