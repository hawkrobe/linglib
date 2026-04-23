import Linglib.Core.Agent.SocialUtility
import Mathlib.Data.Fintype.Basic

/-!
# Strategic Games @cite{fehr-schmidt-1999}
@cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}

Multi-agent game infrastructure for social cognition.

Existing `DecisionTheory.lean` is single-agent: one decision-maker, one
prior, one utility. But emotion prediction, politeness, and game-theoretic
pragmatics all require **strategic interaction** — one agent's payoff
depends on what another agent does.

This module provides:

- `SymmetricGame`: 2-player symmetric game with payoff matrix
- Base features (Money, AI, DI) as deterministic functions of action pairs
- Split-or-Steal (@cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}) as a weak Prisoner's Dilemma

## Connection to BToM

A `SymmetricGame` determines the `utility` field of a BToM generative
model: the agent's `Desire` type becomes the Fehr-Schmidt preference
weights (ω_Money, ω_AIA, ω_DIA), and the `planModel` implements
expected-utility maximization over those weighted base features.

## Connection to Pragmatics

Signaling games (@cite{franke-2011}, @cite{lewis-1969}) extend this to
games where actions = utterances and payoffs depend on communicated
information. The current module covers non-communicative games; signaling
games are in `Theories/Semantics/Questions/SignalingGames.lean`.
-/

set_option autoImplicit false

namespace Pragmatics.GameTheory

open Core.Agent.SocialUtility

-- ============================================================================
-- §1. Binary Actions
-- ============================================================================

/-- Binary action in a 2-player game. -/
inductive Action2 where
  | cooperate  -- Split (cooperate, prosocial)
  | defect     -- Steal (defect, selfish)
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Action2 where
  elems := {.cooperate, .defect}
  complete := λ x => by cases x <;> simp

-- ============================================================================
-- §2. Symmetric Games
-- ============================================================================

/-- A 2-player symmetric game: `payoff a₁ a₂` is player 1's material payoff
when player 1 plays `a₁` and player 2 plays `a₂`.

Symmetric: player 2's payoff when (a₁, a₂) is played equals
player 1's payoff when (a₂, a₁) is played. -/
structure SymmetricGame where
  payoff : Action2 → Action2 → ℚ

namespace SymmetricGame

variable (g : SymmetricGame)

/-- Player 2's payoff (by symmetry). -/
def otherPayoff (a₁ a₂ : Action2) : ℚ := g.payoff a₂ a₁

/-- Disadvantageous inequality for player 1 in outcome (a₁, a₂). -/
def di (a₁ a₂ : Action2) : ℚ :=
  disadvantageousInequality (g.payoff a₁ a₂) (g.otherPayoff a₁ a₂)

/-- Advantageous inequality for player 1 in outcome (a₁, a₂). -/
def ai (a₁ a₂ : Action2) : ℚ :=
  advantageousInequality (g.payoff a₁ a₂) (g.otherPayoff a₁ a₂)

/-- Base features: the three Fehr-Schmidt utility components.
Returns (Money, AI, DI) — all deterministic given the action pair. -/
def baseFeatures (a₁ a₂ : Action2) : ℚ × ℚ × ℚ :=
  (g.payoff a₁ a₂, g.ai a₁ a₂, g.di a₁ a₂)

/-- Weighted social utility for player 1 given Fehr-Schmidt weights.

    U = ω_m · Money − ω_aia · AI − ω_dia · DI

Note the negative signs: AI and DI are *costs*. -/
def socialUtility (a₁ a₂ : Action2) (ωMoney ωAIA ωDIA : ℚ) : ℚ :=
  ωMoney * g.payoff a₁ a₂ - ωAIA * g.ai a₁ a₂ - ωDIA * g.di a₁ a₂

/-- Social utility with Fehr-Schmidt weights equals applying fehrSchmidt
with rescaled parameters, when ωMoney = 1. -/
theorem socialUtility_eq_fehrSchmidt (a₁ a₂ : Action2) (ωAIA ωDIA : ℚ) :
    g.socialUtility a₁ a₂ 1 ωAIA ωDIA =
    fehrSchmidt (g.payoff a₁ a₂) (g.otherPayoff a₁ a₂) ωDIA ωAIA := by
  unfold socialUtility ai di fehrSchmidt
  unfold advantageousInequality disadvantageousInequality otherPayoff
  ring

end SymmetricGame

-- ============================================================================
-- §3. Split or Steal
-- ============================================================================

/-- The Split-or-Steal game from @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}.

A weak Prisoner's Dilemma: CC gives (pot/2, pot/2), CD gives (0, pot),
DC gives (pot, 0), DD gives (0, 0). Unlike a standard PD, mutual
defection yields the same payoff as being cooperated against — hence
"weak." -/
def splitOrSteal (pot : ℚ) : SymmetricGame where
  payoff
    | .cooperate, .cooperate => pot / 2
    | .cooperate, .defect    => 0
    | .defect,    .cooperate => pot
    | .defect,    .defect    => 0

/-- CC: equal split, no inequality. -/
theorem splitOrSteal_cc_equal (pot : ℚ) :
    (splitOrSteal pot).payoff .cooperate .cooperate =
    (splitOrSteal pot).otherPayoff .cooperate .cooperate := rfl

/-- Defecting weakly dominates: ∀ a₂, payoff(D, a₂) ≥ payoff(C, a₂). -/
theorem splitOrSteal_defect_weakly_dominates (pot : ℚ) (hpot : 0 < pot)
    (a₂ : Action2) :
    (splitOrSteal pot).payoff .defect a₂ ≥
    (splitOrSteal pot).payoff .cooperate a₂ := by
  cases a₂ <;> simp [splitOrSteal] <;> linarith

/-- DC: defector gets everything — maximum advantageous inequality. -/
theorem splitOrSteal_dc_ai (pot : ℚ) (hpot : 0 < pot) :
    (splitOrSteal pot).ai .defect .cooperate = pot := by
  simp only [SymmetricGame.ai, advantageousInequality,
    SymmetricGame.otherPayoff, splitOrSteal, sub_zero]
  exact max_eq_right (le_of_lt hpot)

/-- CD: cooperator gets nothing — maximum disadvantageous inequality. -/
theorem splitOrSteal_cd_di (pot : ℚ) (hpot : 0 < pot) :
    (splitOrSteal pot).di .cooperate .defect = pot := by
  simp only [SymmetricGame.di, disadvantageousInequality,
    SymmetricGame.otherPayoff, splitOrSteal, sub_zero]
  exact max_eq_right (le_of_lt hpot)

/-- Despite weak dominance, a player with high enough AIA weight
prefers to cooperate when the opponent cooperates.

CC: payoffs equal ⇒ AI = DI = 0 ⇒ socialUtility = pot/2.
DC: payoff = pot, other = 0, AI = pot, DI = 0 ⇒ socialUtility = pot(1 − ωAIA).
When ωAIA > 1/2: pot(1 − ωAIA) < pot/2, so cooperation is preferred.

This is the Fehr-Schmidt explanation of cooperation: an agent with high
advantageous inequity aversion (AIA) — who dislikes getting more than
others — will cooperate even though defection weakly dominates in
material terms. -/
theorem splitOrSteal_cooperate_preferred_high_aia (pot : ℚ) (hpot : 0 < pot)
    (ωAIA : ℚ) (haia : ωAIA > 1) :
    (splitOrSteal pot).socialUtility .cooperate .cooperate 1 ωAIA 0 >
    (splitOrSteal pot).socialUtility .defect .cooperate 1 ωAIA 0 := by
  unfold SymmetricGame.socialUtility SymmetricGame.ai SymmetricGame.di
    advantageousInequality disadvantageousInequality SymmetricGame.otherPayoff splitOrSteal
  simp only [sub_self, max_self, sub_zero]
  rw [max_eq_right (le_of_lt hpot), max_eq_left (show (0 : ℚ) - pot ≤ 0 by linarith)]
  nlinarith

end Pragmatics.GameTheory
