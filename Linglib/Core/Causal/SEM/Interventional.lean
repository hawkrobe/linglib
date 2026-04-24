import Linglib.Core.Causal.SEM.Basic
import Linglib.Core.Causal.SEM.Deterministic

/-!
# SEM: Interventional Probability

`P(E = xE | do(C := xC))` — the **interventional** probability of an
effect under Pearl's `do`-operator. Distinct from counterfactual
reasoning: there is no observation conditioning, no abduction step.

This file is the home for `probabilisticSuf` (@cite{cao-white-lassiter-2025}'s
graded ALT measure for causal sufficiency) and its deterministic-collapse
bridge.

## Why a separate file from `Counterfactual.lean`

Counterfactual reasoning (Lewis 1973, N&L 2020 Defs 23/24/25, B&G 2025
W/H/S, Lassiter 2017) involves **observation conditioning** — given that
we observed the actual world, what would have happened if X had been
different? This requires an abduction step (Pearl 3-step:
abduction-action-prediction).

Interventional probability skips abduction: just intervene and predict.
Mathematically simpler; conceptually different. They share the substrate
(`develop`, `intervene`) but answer different questions.

Mathlib analogue: `Mathlib/Probability/Kernel/CondCDF.lean` (conditional)
vs `Mathlib/Probability/Kernel/Defs.lean` (unconditional kernel) — same
substrate, distinct files for distinct mathematical questions.

## Computability

`probabilisticSuf` is `noncomputable` (uses `tsum` over PMF). The
deterministic-collapse bridge `probabilisticSuf_of_deterministic` reduces
it to a {0,1} indicator under `IsDeterministic`. The bridge currently
relies on `develop_eq_pure_of_deterministic` (sorry'd in `Basic.lean`
pending the per-vertex `developDet` proof), so the chain has one
substrate sorry. Documented; not a regression from the pre-refactor state.
-/

namespace Core.Causal.SEM

variable {V : Type*} {α : V → Type*} [Fintype V] [DecidableEq V] [DecidableValuation α]

/-- **Interventional probability of an effect**: `P(effect = xE | do(cause := xC))`.
    Pearl's `do`-operator gives the probability of the effect under
    forward intervention; no observation conditioning.

    @cite{cao-white-lassiter-2025}'s graded ALT measure for causal
    sufficiency. PMF-valued via `develop`; reduces to a {0,1} indicator
    under `IsDeterministic` via `probabilisticSuf_of_deterministic`. -/
noncomputable def probabilisticSuf
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) : ENNReal :=
  ∑' v : Valuation α, if v.hasValue effect xE
                      then ((M.intervene cause xC).develop s) v
                      else 0

/-- Bridge: under `IsDeterministic`, `probabilisticSuf` is the {0,1}
    indicator of whether the deterministic intervened development hits
    `effect = xE`. -/
theorem probabilisticSuf_of_deterministic
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    probabilisticSuf M s cause xC effect xE =
      if ((M.intervene cause xC).developDet s).hasValue effect xE then 1 else 0 := by
  unfold probabilisticSuf
  rw [develop_eq_pure_of_deterministic]
  rw [tsum_eq_single ((M.intervene cause xC).developDet s)
      (fun v hv => by
        rw [PMF.pure_apply_of_ne _ _ hv]; simp)]
  by_cases h : ((M.intervene cause xC).developDet s).hasValue effect xE
  · simp [h, PMF.pure_apply_self]
  · simp [h]

end Core.Causal.SEM
