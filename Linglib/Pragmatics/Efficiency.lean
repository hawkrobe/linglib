import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Linglib.Core.Optimization.Profile

/-!
# Communicative Efficiency: β-scalarization and Frontier Deviation
[xu-etal-2024] [kemp-regier-2012] [zaslavsky-kemp-regier-tishby-2018]

A `CostPair` is a 2-component cost profile (effort, information loss).
Many linguistic phenomena arise from a tension between two functional
pressures, and attested forms tend to be Pareto-efficient compromises.

**Pareto dominance lives in `Core.Optimization.Pareto`.** This file does
not redefine it. `CostPair.toProfile` projects a cost pair into
`Core.Optimization.Profile ℝ 2`, where `paretoPullbackPreorder` answers
"is `a` Pareto-dominated by `b`?" via the substrate.

What this file does contribute is the β-scalarization (`weightedCost`)
and the frontier-deviation primitives (`efficiencyLossAt`, `efficiencyLoss`)
specific to the Xu-et-al / Kemp-Regier / Zaslavsky efficient-communication
framework. These are not generic preorder operations.

## Main definitions

- `CostPair`: 2-component cost (effort, information loss)
- `CostPair.toProfile`: bridge to `Profile ℝ 2` for substrate-side Pareto
- `weightedCost`: linear scalarization `L_β = cost₂ + β · cost₁`
- `efficiencyLossAt`: per-β deviation from optimal
- `efficiencyLoss`: minimum deviation across a list of β values
  (corresponds to ε in [xu-etal-2024] eq. 8)
-/

namespace Pragmatics.Efficiency

/-- A pair of communicative costs. The framework is general: `cost₁` and
    `cost₂` can represent any two pressures in a functional tradeoff.

    In [xu-etal-2024]: cost₁ = speaker effort (word length),
    cost₂ = information loss (listener surprisal).
    In [kemp-regier-2012]: cost₁ = complexity, cost₂ = informativeness loss.
    In [zaslavsky-kemp-regier-tishby-2018]: cost₁ = I(W;U), cost₂ = D[p||q]. -/
structure CostPair where
  cost₁ : ℝ
  cost₂ : ℝ

/-- Bridge a `CostPair` into the substrate `Core.Optimization.Profile ℝ 2`.
    Pareto dominance and optimality on cost pairs come for free via
    `Core.Optimization.paretoPullbackPreorder` composed with this function;
    no per-file `dominates` / `isParetoOptimal` redefinition is needed. -/
def CostPair.toProfile (c : CostPair) : Core.Optimization.Profile ℝ 2 :=
  fun i => match i with | 0 => c.cost₁ | 1 => c.cost₂

@[simp] theorem CostPair.toProfile_zero (c : CostPair) :
    c.toProfile 0 = c.cost₁ := rfl

@[simp] theorem CostPair.toProfile_one (c : CostPair) :
    c.toProfile 1 = c.cost₂ := rfl

/-- Weighted cost: linear scalarization of two costs.
    `L_β = cost₂ + β · cost₁`.
    `β = 0` considers only `cost₂`; large β emphasizes `cost₁`. -/
def weightedCost (c : CostPair) (β : ℝ) : ℝ :=
  c.cost₂ + β * c.cost₁

/-- Efficiency loss at a specific β: deviation from the optimal encoding. -/
def efficiencyLossAt (attested optimal : CostPair) (β : ℝ) : ℝ :=
  weightedCost attested β - weightedCost optimal β

/-- Overall efficiency loss: minimum deviation across β values.
    `ε = min_β (L_β[attested] − L_β[optimal_β])` ([xu-etal-2024] eq. 8). -/
noncomputable def efficiencyLoss (attested : CostPair) (optimalAt : ℝ → CostPair)
    (βs : List ℝ) : ℝ :=
  match βs.map (fun β => efficiencyLossAt attested (optimalAt β) β) with
  | [] => 0
  | x :: xs => xs.foldl min x

@[simp] theorem efficiencyLossAt_self (c : CostPair) (β : ℝ) :
    efficiencyLossAt c c β = 0 := by
  simp [efficiencyLossAt]

theorem weightedCost_mono_β (c : CostPair) {β₁ β₂ : ℝ}
    (hβ : β₁ ≤ β₂) (hc : 0 ≤ c.cost₁) :
    weightedCost c β₁ ≤ weightedCost c β₂ :=
  add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hβ hc)

end Pragmatics.Efficiency
