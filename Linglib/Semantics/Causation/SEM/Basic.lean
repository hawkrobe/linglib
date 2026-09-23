module

public import Linglib.Semantics.Causation.SEM.Defs
public import Linglib.Semantics.Causation.SEM.Deterministic
public import Linglib.Semantics.Causation.Mechanism.Defs

/-!
# SEM: intervention

Pearl's `do(v := x)` (`intervene`) replaces the equation of `v` by the constant `x`. On an
acyclic model, intervening on a vertex the valuation leaves undetermined develops exactly as
setting it in the valuation does (`developDet_intervene_eq_developDet_extend`), which is why the
counterfactual predicates of `SEM/Counterfactual.lean` are stated with `Valuation.extend`.

## References

* [pearl-2000]
-/

@[expose] public section

namespace Causation.SEM

variable {V : Type*} {α : V → Type*}

/-! ### Intervention (Pearl do(v := x)) -/

/-- **Pearl's `do(v := x)` intervention**: replace the mechanism for `v`
    with the constant mechanism returning `x`. Other vertices'
    mechanisms are unchanged. -/
def intervene [DecidableEq V] (M : SEM V α) (v : V) (x : α v) : SEM V α :=
  { graph := M.graph
    mech  := fun w =>
      if h : w = v then h ▸ Mechanism.const (G := M.graph) x else M.mech w }

@[simp] theorem intervene_graph [DecidableEq V] (M : SEM V α) (v : V) (x : α v) :
    (M.intervene v x).graph = M.graph := rfl

/-- The intervened vertex's mechanism becomes constant. -/
@[simp] theorem intervene_mech_self [DecidableEq V] (M : SEM V α) (v : V) (x : α v) :
    (M.intervene v x).mech v = Mechanism.const (G := M.graph) x := by
  simp [intervene]

/-- Other vertices' mechanisms are unaffected by intervention. -/
@[simp] theorem intervene_mech_other [DecidableEq V] (M : SEM V α) {v w : V} (x : α v)
    (h : w ≠ v) : (M.intervene v x).mech w = M.mech w := by
  simp [intervene, h]

/-- An intervention preserves the graph (only the mechanism at `v` is
    replaced), so it preserves the `IsDAG` mixin. -/
instance [DecidableEq V] (M : SEM V α) [h : CausalGraph.IsDAG M.graph]
    (v : V) (x : α v) : CausalGraph.IsDAG (M.intervene v x).graph := by
  rw [intervene_graph]; exact h

/-- **Intervention-as-Extend bridge**: for an acyclic deterministic SEM
    with `cause` undetermined in `s`, Pearl-intervening to set
    `cause := xC` is equivalent (at the level of `developDet`) to
    extending the valuation with `cause = xC` and developing under the
    original mechanisms.

    Substrate fact connecting `intervene`-based development to
    `extend`-based development (the latter underlies `causallySufficient`).
    The proof goes by `WellFounded.induction` on `IsDAG` on vertices: at `cause` both sides
    produce `xC` (LHS via the constant intervention mechanism; RHS via
    `developDetVtx_extended` short-circuit on the extended valuation);
    off-cause both sides reduce to the same mechanism applied to
    recursively-equal parent values via the IH. -/
theorem developDet_intervene_eq_developDet_extend
    [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [hDag : CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause)
    (h : s.get cause = none) :
    (M.intervene cause xC).developDet s = M.developDet (s.extend cause xC) := by
  funext v
  show some (developDetVtx (M.intervene cause xC) s v) =
       some (developDetVtx M (s.extend cause xC) v)
  congr 1
  induction v using hDag.induction with
  | _ w ih =>
    rw [developDetVtx_unfold (M.intervene cause xC) s w]
    rw [developDetVtx_unfold M (s.extend cause xC) w]
    by_cases hwc : w = cause
    · subst hwc
      simp only [h, Valuation.extend_get_same]
      rw [intervene_mech_self]
      rfl
    · rw [Valuation.extend_get_ne hwc]
      cases s.get w with
      | some y => rfl
      | none =>
        simp only
        rw [intervene_mech_other M xC hwc]
        congr 1
        funext u
        exact ih u.val (Relation.TransGen.single u.property)

end Causation.SEM
