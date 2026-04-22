import Linglib.Core.Causal.V2.SEM.Defs
import Linglib.Core.Causal.V2.Mechanism.Deterministic

/-!
# SEM: Intervention + Forward-Propagation Stubs (V2)

- **`intervene`** (Pearl `do(v := x)`): replace the mechanism for `v`
  with `Mechanism.const x`.

- **`develop`**: forward-propagation fixpoint. Phase A leaves the body
  as `s` (returns input); Phase C ports the real implementation. The
  signature already carries the constraints the real implementation
  will need (`[Fintype V] [DecidableEq V] [IsDAG] [IsDeterministic]`)
  so consumers don't break when the body is replaced.
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
@[simp] theorem intervene_mech_self [DecidableEq V] (M : SEM V α) (v : V) (x : α v) :
    (M.intervene v x).mech v = Mechanism.const (G := M.graph) x := by
  simp [intervene]

/-- Other vertices' mechanisms are unaffected by intervention. -/
@[simp] theorem intervene_mech_other [DecidableEq V] (M : SEM V α) {v w : V} (x : α v)
    (h : w ≠ v) : (M.intervene v x).mech w = M.mech w := by
  simp [intervene, h]

-- ════════════════════════════════════════════════════
-- § Forward propagation
-- ════════════════════════════════════════════════════

/-- **Forward-development** of a deterministic acyclic SEM against a
    partial valuation. Iterates fireable mechanisms in topological order
    until fixpoint.

    Phase A returns `s` unchanged (stub); Phase C ports the real
    implementation (well-founded fixpoint via `Valuation.undeterminedCount`).
    The full type signature is in place so Phase C only changes the body. -/
noncomputable def develop [Fintype V] [DecidableEq V] (M : SEM V α)
    [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) : Valuation α := s

end Core.Causal.V2.SEM
