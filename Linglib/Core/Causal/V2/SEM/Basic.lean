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

/-- Termination measure: count of undetermined vertices over `Fintype.elems`.
    Noncomputable because `Finset.toList` is. -/
private noncomputable def devMeasure [Fintype V] (s : Valuation α) : ℕ :=
  s.undeterminedCount (Fintype.elems : Finset V).toList

/-- Generic mathlib-missing piece: if a `ℕ`-valued measure strictly
    decreases on non-stopping points, iterating `f` eventually reaches a
    stopping point. (Inlined; promote if a second consumer materializes.) -/
private theorem _root_.Function.exists_iterate_satisfies' {α : Type*} (f : α → α)
    {Stop : α → Prop} [DecidablePred Stop]
    (m : α → ℕ) (h : ∀ x, ¬ Stop x → m (f x) < m x) (x : α) :
    ∃ n, Stop (f^[n] x) := by
  induction hk : m x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    by_cases hStop : Stop x
    · exact ⟨0, by simpa using hStop⟩
    · have hLt : m (f x) < k := hk ▸ h x hStop
      obtain ⟨n, hn⟩ := ih (m (f x)) hLt (f x) rfl
      exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

/-- **Strict-decrease lemma**: when `stepOnce M s ≠ s`, the
    undetermined-vertex count strictly decreases.

    Substantive content: at least one vertex transitioned from undetermined
    to determined during the foldl sweep (since `stepOnce` only modifies
    via `extend`); the rest preserve `isNone`-ness by info-monotonicity;
    the differing vertex contributes -1 to the count.

    TODO (C-1 completion): proof is foldl-induction over `Fintype.elems.toList`
    with two helper lemmas:
    - `stepOnce_info_monotone : (s.get v).isSome → ((stepOnce M s).get v).isSome`
    - `stepOnce_witness : stepOnce M s ≠ s → ∃ v, (s.get v).isNone ∧ ((stepOnce M s).get v).isSome`
    Then apply `countP_lt_of_imp_of_witness` (port from old `Monotonicity.lean`). -/
theorem stepOnce_strict_decrease [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α)
    (hNotFix : stepOnce M s ≠ s) :
    devMeasure (stepOnce M s) < devMeasure s := by
  sorry

/-- **Forward-development** of a deterministic acyclic SEM against a
    partial valuation. Iterates `stepOnce` until fixpoint via
    `Nat.find` on the existence of a fixpoint iterate.

    Termination relies on `stepOnce_strict_decrease`: when
    `stepOnce M s ≠ s`, the undetermined-vertex count strictly decreases.

    Replaces the old `normalDevelopment`. -/
noncomputable def develop [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) : Valuation α :=
  (stepOnce M)^[Nat.find (Function.exists_iterate_satisfies' (Stop := fun x => stepOnce M x = x)
    (stepOnce M) devMeasure (fun x hx => stepOnce_strict_decrease M x hx) s)] s

end Core.Causal.V2.SEM
