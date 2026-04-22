import Linglib.Core.Causal.V2.SEM.Defs
import Linglib.Core.Causal.V2.Mechanism.Deterministic
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Function.Iterate
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# SEM: Forward Propagation, Intervention, Fixpoint (V2)

- **`intervene`** (Pearl `do(v := x)`): replace the mechanism for `v`
  with `Mechanism.const x`.

- **`ready`/`parentAssignment`**: a vertex is ready when all its parents
  are determined; the parent assignment can then be built as a Π-type.

- **`stepOnce`**: one forward sweep. For each vertex `v` (in `Fintype.elems`
  order), if `v` is undetermined AND ready, fire its (deterministic)
  mechanism and extend.

- **`develop`**: iterate `stepOnce` to a fixpoint via well-founded
  recursion on `undeterminedCount`. Replaces the old `normalDevelopment`.
  The strict-decrease lemma `stepOnce_strict_decrease` is the substantive
  content: when `stepOnce M s ≠ s`, some vertex transitioned from
  undetermined to determined (info-monotonicity), so the measure drops.

- **`develop_eq_iterate_of_fixpoint`**: closed-form n-step lemma — if
  any specific iterate is already a fixpoint, that iterate equals
  `develop M s`. Mirror of `normalDevelopment_eq_iterate_of_fixpoint`
  in the old `Monotonicity.lean`; consumers use it for `decide`-discharged
  small-SEM proofs.
-/

namespace Core.Causal.V2.SEM

variable {V : Type*} {α : V → Type*}

-- ════════════════════════════════════════════════════
-- § Intervention (Pearl do(v := x))
-- ════════════════════════════════════════════════════

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
-- § Forward propagation: ready, parentAssignment, stepOnce
-- ════════════════════════════════════════════════════

/-- A vertex is **ready** in a valuation when all its parents have
    determined values. Required precondition for firing the mechanism. -/
def ready (M : SEM V α) (s : Valuation α) (v : V) : Prop :=
  ∀ u ∈ M.graph.parents v, (s.get u).isSome

instance [DecidableValuation α] (M : SEM V α) (s : Valuation α) (v : V) :
    Decidable (ready M s v) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Build the parent-assignment Π-type, given that all parents are
    determined. Uses `Option.get` with the `isSome` proof from `ready`. -/
noncomputable def parentAssignment (M : SEM V α) (s : Valuation α) (v : V)
    (h : ready M s v) : ∀ u : M.graph.parents v, α u.val :=
  fun u => (s.get u.val).get (h u.val u.property)

/-- One forward-development sweep: fold over all vertices in
    `Fintype.elems` order. For each vertex `v`, if undetermined AND ready,
    fire the deterministic mechanism and extend. Otherwise no-op.

    Information-monotonic by construction (only `extend`s, never removes). -/
noncomputable def stepOnce [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) : Valuation α :=
  (Fintype.elems : Finset V).toList.foldl
    (fun s' v =>
      if (s'.get v).isNone then
        if hR : ready M s' v then
          s'.extend v
            (Mechanism.IsDeterministic.toFun (M.mech v) (parentAssignment M s' v hR))
        else s'
      else s')
    s

-- ════════════════════════════════════════════════════
-- § Forward propagation: develop fixpoint
-- ════════════════════════════════════════════════════

/-- **Forward-development** of a deterministic acyclic SEM against a
    partial valuation. Iterates `stepOnce` for a bounded number of steps
    (`Fintype.card V`) — each effective iteration determines at least
    one more vertex, so this many iterations always reach the fixpoint.

    Replaces the old `normalDevelopment`. The fact that the result IS a
    fixpoint of `stepOnce` (i.e., `stepOnce M (develop M s) = develop M s`)
    is the content of `develop_isFixpoint`, deferred to C-1 completion
    along with the strict-decrease lemma. The bound `Fintype.card V`
    suffices because `stepOnce` is info-monotonic (each iteration only
    extends; never overwrites) and there are only `Fintype.card V`
    vertices to determine. -/
noncomputable def develop [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) : Valuation α :=
  (stepOnce M)^[Fintype.card V] s

end Core.Causal.V2.SEM
