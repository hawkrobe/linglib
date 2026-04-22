import Linglib.Core.Causal.V2.Mechanism.Defs

/-!
# Mechanism.deterministic: Deterministic-as-Dirac Constructor (V2)

The deterministic mechanism induced by an honest function over parents
is built as a Dirac PMF — the exact mathlib pattern from
`Mathlib/Probability/Kernel/Basic.lean` where
`Kernel.deterministic (f) := dirac ∘ f`.

Provides:
- `Mechanism.deterministic` — the constructor
- `IsDeterministic` instance for the constructor's image
- `simp` lemma for unfolding `(deterministic f).run`
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

/-- The deterministic constructor unfolds to `PMF.pure`. -/
@[simp] theorem deterministic_run
    (f : (∀ u : G.parents v, α u.val) → α v)
    (ρ : ∀ u : G.parents v, α u.val) :
    (deterministic f).run ρ = PMF.pure (f ρ) := rfl

/-- Deterministic mechanisms satisfy the `IsDeterministic` mixin. -/
instance (f : (∀ u : G.parents v, α u.val) → α v) :
    IsDeterministic (deterministic f) where
  pure_run ρ := ⟨f ρ, rfl⟩

/-- Extract the deterministic function from any `IsDeterministic` mechanism.
    Noncomputable because uses `Classical.choose` over the `pure_run` witness;
    consumers that need computability should construct via `deterministic`
    directly and avoid the round-trip. -/
noncomputable def toFun (m : Mechanism G α v) [h : IsDeterministic m] :
    (∀ u : G.parents v, α u.val) → α v :=
  fun ρ => Classical.choose (h.pure_run ρ)

theorem toFun_spec (m : Mechanism G α v) [h : IsDeterministic m]
    (ρ : ∀ u : G.parents v, α u.val) :
    m.run ρ = PMF.pure (m.toFun ρ) :=
  Classical.choose_spec (h.pure_run ρ)

/-- The deterministic constructor's `toFun` recovers the underlying function,
    via injectivity of `PMF.pure` (which holds because `pure a`'s support is
    `{a}`). -/
@[simp] theorem deterministic_toFun
    (f : (∀ u : G.parents v, α u.val) → α v)
    (ρ : ∀ u : G.parents v, α u.val) :
    (deterministic f).toFun ρ = f ρ := by
  have h : (deterministic f).run ρ = PMF.pure ((deterministic f).toFun ρ) :=
    toFun_spec _ ρ
  simp only [deterministic_run] at h
  -- pure a = pure b → a = b via support analysis
  have := congrArg PMF.support h
  simp [PMF.support_pure] at this
  exact this.symm

/-- A constant mechanism: ignores parents, always returns the same value
    via Dirac. Useful for `intervene`-style mechanism replacement. -/
noncomputable def const (x : α v) : Mechanism G α v := deterministic (fun _ => x)

@[simp] theorem const_run (x : α v) (ρ : ∀ u : G.parents v, α u.val) :
    (const (G := G) x).run ρ = PMF.pure x := rfl

instance (x : α v) : IsDeterministic (const (G := G) x) :=
  inferInstanceAs (IsDeterministic (deterministic _))

end Core.Causal.V2.Mechanism
