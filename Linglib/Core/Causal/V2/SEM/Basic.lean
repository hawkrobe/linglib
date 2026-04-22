import Linglib.Core.Causal.V2.SEM.Defs
import Linglib.Core.Causal.V2.Mechanism.Deterministic

/-!
# SEM: Intervention + Forward-Propagation Stubs (V2)

Basic operations on `SEM`:

- **`intervene`** (Pearl `do(v := x)`): replace the mechanism for `v`
  with `Mechanism.const x`. Cleaner than the old approach (filter laws
  targeting `v`); a Pearl intervention becomes one mechanism replacement.

- **`stepOnce` / `develop`**: forward propagation of a deterministic SEM
  against a partial valuation. Phase A leaves these as **stubs** —
  the real fixpoint implementation (with termination proof) ports in
  Phase C alongside the migration of `causallySufficient` /
  `causallyNecessary` from `SEM/Counterfactual.lean`.
-/

namespace Core.Causal.V2.SEM

variable {V : Type*} {α : V → Type*}

/-- **Pearl's `do(v := x)` intervention**: replace the mechanism for `v`
    with the constant Dirac-PMF mechanism returning `x`. Other vertices'
    mechanisms are unchanged.

    Cleaner than the old `CausalDynamics`-era version (which had to
    filter `dyn.laws` for laws targeting `v`); under the new
    architecture, an intervention is one mechanism replacement. -/
noncomputable def intervene [DecidableEq V] (M : SEM V α) (v : V) (x : α v) : SEM V α :=
  { graph := M.graph
    mech  := fun w =>
      if h : w = v then h ▸ Mechanism.const (G := M.graph) x else M.mech w }

@[simp] theorem intervene_graph [DecidableEq V] (M : SEM V α) (v : V) (x : α v) :
    (M.intervene v x).graph = M.graph := rfl

/-- The intervened vertex's mechanism becomes a constant Dirac. -/
theorem intervene_mech_self [DecidableEq V] (M : SEM V α) (v : V) (x : α v) :
    (M.intervene v x).mech v = Mechanism.const (G := M.graph) x := by
  simp [intervene]

/-- Other vertices' mechanisms are unaffected by intervention. -/
theorem intervene_mech_other [DecidableEq V] (M : SEM V α) {v w : V} (x : α v)
    (h : w ≠ v) : (M.intervene v x).mech w = M.mech w := by
  simp [intervene, h]

-- ════════════════════════════════════════════════════
-- § Forward propagation (stubs — Phase C ports the real implementation)
-- ════════════════════════════════════════════════════

/-- **Forward-development stub** (Phase C will implement properly).

    The real `develop` will:
    1. Iterate `stepOnce` to a fixpoint (terminating by well-founded
       induction on `Valuation.undeterminedCount` over `Fintype.elems`)
    2. Require `[Fintype V] [CausalGraph.IsDAG M.graph] [IsDeterministic M]`
    3. Mirror the old `normalDevelopment` semantics

    Phase A returns the input unchanged so downstream stubs compile. -/
def develop (_M : SEM V α) (s : Valuation α) : Valuation α := s

end Core.Causal.V2.SEM
