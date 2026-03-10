import Mathlib.Algebra.Order.Ring.Rat

/-!
# Communicative Efficiency and Pareto Optimality
@cite{xu-etal-2024} @cite{kemp-regier-2012} @cite{zaslavsky-kemp-regier-tishby-2018}

Domain-agnostic infrastructure for formalizing tradeoffs between competing
communicative pressures via Pareto optimality. Many linguistic phenomena arise
from the tension between two functional pressures — informativity vs. brevity,
specificity vs. learnability, transparency vs. economy — and the resulting
attested forms tend to be Pareto-efficient compromises.

## Main definitions

- `CostPair`: two communicative costs (e.g., effort and information loss)
- `dominates`: strict Pareto dominance
- `isParetoOptimal`: non-dominated w.r.t. a set of alternatives
- `weightedCost`: linear scalarization with tradeoff parameter β
- `efficiencyLoss`: deviation from the Pareto frontier (Eq. 8 of @cite{xu-etal-2024})
-/

namespace Core.Efficiency

/-- A pair of communicative costs. The framework is general: `cost₁` and
    `cost₂` can represent any two pressures in a functional tradeoff.

    In @cite{xu-etal-2024}: cost₁ = speaker effort (word length),
    cost₂ = information loss (listener surprisal).
    In @cite{kemp-regier-2012}: cost₁ = complexity, cost₂ = informativeness loss.
    In @cite{zaslavsky-kemp-regier-tishby-2018}: cost₁ = I(W;U), cost₂ = D[p||q]. -/
structure CostPair where
  cost₁ : ℚ
  cost₂ : ℚ
  deriving Repr, DecidableEq, BEq

/-- Pareto dominance: `a` dominates `b` iff `a` is at least as good on
    both dimensions and strictly better on at least one. -/
def dominates (a b : CostPair) : Prop :=
  a.cost₁ ≤ b.cost₁ ∧ a.cost₂ ≤ b.cost₂ ∧ (a.cost₁ < b.cost₁ ∨ a.cost₂ < b.cost₂)

theorem dominates_irrefl (a : CostPair) : ¬dominates a a := by
  intro ⟨_, _, h⟩; exact h.elim (lt_irrefl _) (lt_irrefl _)

theorem dominates_trans {a b c : CostPair}
    (hab : dominates a b) (hbc : dominates b c) : dominates a c := by
  obtain ⟨h1, h2, h3⟩ := hab; obtain ⟨h4, h5, _⟩ := hbc
  exact ⟨le_trans h1 h4, le_trans h2 h5,
    h3.elim (fun h => .inl (lt_of_lt_of_le h h4)) (fun h => .inr (lt_of_lt_of_le h h5))⟩

/-- A cost pair is Pareto optimal if no alternative dominates it. -/
def isParetoOptimal (x : CostPair) (alternatives : List CostPair) : Prop :=
  ∀ y ∈ alternatives, ¬dominates y x

/-- Weighted cost: linear scalarization of two costs.
    L_β = cost₂ + β · cost₁.
    β = 0 considers only cost₂; large β emphasizes cost₁. -/
def weightedCost (c : CostPair) (β : ℚ) : ℚ :=
  c.cost₂ + β * c.cost₁

/-- Efficiency loss at a specific β: deviation from the optimal encoding. -/
def efficiencyLossAt (attested optimal : CostPair) (β : ℚ) : ℚ :=
  weightedCost attested β - weightedCost optimal β

/-- Overall efficiency loss: minimum deviation across β values.
    ε = min_β (L_β[attested] − L_β[optimal_β])   (Eq. 8, @cite{xu-etal-2024}). -/
def efficiencyLoss (attested : CostPair) (optimalAt : ℚ → CostPair)
    (βs : List ℚ) : ℚ :=
  match βs.map (fun β => efficiencyLossAt attested (optimalAt β) β) with
  | [] => 0
  | x :: xs => xs.foldl min x

theorem efficiencyLossAt_self (c : CostPair) (β : ℚ) :
    efficiencyLossAt c c β = 0 := by
  simp [efficiencyLossAt]

theorem weightedCost_mono_β (c : CostPair) {β₁ β₂ : ℚ}
    (hβ : β₁ ≤ β₂) (hc : 0 ≤ c.cost₁) :
    weightedCost c β₁ ≤ weightedCost c β₂ := by
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hβ hc)

end Core.Efficiency
