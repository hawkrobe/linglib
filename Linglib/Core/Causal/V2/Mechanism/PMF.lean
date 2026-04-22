import Linglib.Core.Causal.V2.Mechanism.Defs

/-!
# Mechanism.pmf: Stochastic Mechanism Constructor (V2)

Trivial wrapper turning a `PMF`-valued function into a `Mechanism`.
Symmetric counterpart to `Mechanism.deterministic` — kept for naming
parallelism and discoverability.
-/

namespace Core.Causal.V2.Mechanism

variable {V : Type*} {α : V → Type*} {G : CausalGraph V} {v : V}

/-- The general (probabilistic) mechanism constructor. Turns any
    `PMF`-valued function over parents into a `Mechanism`. -/
def pmf (f : (∀ u : G.parents v, α u.val) → PMF (α v)) :
    Mechanism G α v := ⟨f⟩

@[simp] theorem pmf_run
    (f : (∀ u : G.parents v, α u.val) → PMF (α v))
    (ρ : ∀ u : G.parents v, α u.val) :
    (pmf f).run ρ = f ρ := rfl

end Core.Causal.V2.Mechanism
