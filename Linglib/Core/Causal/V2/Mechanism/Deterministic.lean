import Linglib.Core.Causal.V2.Mechanism.Defs

/-!
# Mechanism.deterministic: Deterministic-as-Dirac Constructor (V2)

The deterministic mechanism induced by an honest function over parents
is built as a Dirac PMF — the exact mathlib pattern from
`Mathlib/Probability/Kernel/Basic.lean` where
`Kernel.deterministic (f) := dirac ∘ f`.
-/

namespace Core.Causal.V2.Mechanism

variable {V : Type*} {α : V → Type*} {G : CausalGraph V} {v : V}

/-- The deterministic mechanism induced by an honest function over
    parents. Mirrors `Kernel.deterministic` from
    `Mathlib/Probability/Kernel/Basic.lean`. Noncomputable because
    `PMF.pure` is noncomputable. -/
noncomputable def deterministic (f : (∀ u : G.parents v, α u.val) → α v) :
    Mechanism G α v :=
  ⟨fun ρ => PMF.pure (f ρ)⟩

@[simp] theorem deterministic_run
    (f : (∀ u : G.parents v, α u.val) → α v)
    (ρ : ∀ u : G.parents v, α u.val) :
    (deterministic f).run ρ = PMF.pure (f ρ) := rfl

/-- Deterministic mechanisms satisfy the `IsDeterministic` mixin. -/
instance (f : (∀ u : G.parents v, α u.val) → α v) :
    IsDeterministic (deterministic f) where
  toFun := f
  run_eq _ := rfl

@[simp] theorem deterministic_toFun
    (f : (∀ u : G.parents v, α u.val) → α v) :
    IsDeterministic.toFun (deterministic f) = f := rfl

/-- A constant mechanism: ignores parents, always returns the same value
    via Dirac. Useful for `intervene`-style mechanism replacement.
    Noncomputable inherited via `deterministic`. -/
noncomputable def const (x : α v) : Mechanism G α v := deterministic (fun _ => x)

@[simp] theorem const_run (x : α v) (ρ : ∀ u : G.parents v, α u.val) :
    (const (G := G) x).run ρ = PMF.pure x := rfl

instance (x : α v) : IsDeterministic (const (G := G) x) :=
  inferInstanceAs (IsDeterministic (deterministic _))

end Core.Causal.V2.Mechanism
