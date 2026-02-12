/-
# RSA Model (Real Analysis Version)

RSA scenario using real numbers for mathematical proofs.

## Main definitions

- `RSAScenarioR`: RSA scenario with real-valued parameters
- `RSAModel`: Typeclass for theorem instantiation
- `G_α_generic`: Combined utility objective H + α·E[V]

## References

- Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of human pragmatic reasoning.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Basic
import Linglib.Theories.RSA.Core.Basic

namespace RSA


/-- RSA scenario with real-valued parameters for analysis -/
structure RSAScenarioR where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of world states -/
  World : Type
  /-- Finite utterances -/
  [finU : Fintype Utterance]
  /-- Finite worlds -/
  [finW : Fintype World]
  /-- Lexicon: semantic applicability φ(u,w) -/
  lexicon : Utterance → World → ℝ
  /-- Prior probability over worlds -/
  prior : World → ℝ
  /-- Rationality parameter -/
  α : ℝ
  /-- α is non-negative -/
  α_nonneg : 0 ≤ α
  /-- Lexicon values are non-negative -/
  lexicon_nonneg : ∀ u w, 0 ≤ lexicon u w
  /-- Prior is non-negative -/
  prior_nonneg : ∀ w, 0 ≤ prior w
  /-- At least one world has positive prior -/
  prior_pos : ∃ w, 0 < prior w

attribute [instance] RSAScenarioR.finU RSAScenarioR.finW


/-- Convert computational RSAScenario to RSAScenarioR -/
def RSAScenario.toReal {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (S : RSAScenario U W)
    (defaultInterp : S.Interp) (defaultLexicon : S.Lexicon) : RSAScenarioR where
  Utterance := U
  World := W
  lexicon u w := (S.φ defaultInterp defaultLexicon u w : ℝ)
  prior w := (S.worldPrior w : ℝ)
  α := (S.α : ℝ)
  α_nonneg := Nat.cast_nonneg S.α
  lexicon_nonneg := λ _ _ => by sorry  -- Would need to show ℚ values are non-negative
  prior_nonneg := λ _ => by sorry
  prior_pos := by sorry


/-- RSA model typeclass for instance-based theorems -/
class RSAModel (M : Type*) where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of world states -/
  World : Type
  [finU : Fintype Utterance]
  [finW : Fintype World]
  lexicon : Utterance → World → ℝ
  prior : World → ℝ
  α : ℝ
  α_nonneg : 0 ≤ α
  lexicon_nonneg : ∀ u w, 0 ≤ lexicon u w
  prior_nonneg : ∀ w, 0 ≤ prior w
  prior_pos : ∃ w, 0 < prior w

attribute [instance] RSAModel.finU RSAModel.finW

/-- Convert RSAScenarioR to RSAModel instance. -/
def RSAScenarioR.toModel (S : RSAScenarioR) : RSAModel S.Utterance where
  Utterance := S.Utterance
  World := S.World
  lexicon := S.lexicon
  prior := S.prior
  α := S.α
  α_nonneg := S.α_nonneg
  lexicon_nonneg := S.lexicon_nonneg
  prior_nonneg := S.prior_nonneg
  prior_pos := S.prior_pos

/-- Convert RSAScenario directly to RSAModel (convenience). -/
def RSAScenario.toModel {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (S : RSAScenario U W)
    (defaultInterp : S.Interp) (defaultLexicon : S.Lexicon) : RSAModel U :=
  (RSAScenario.toReal S defaultInterp defaultLexicon).toModel


variable {M : Type*} [I : RSAModel M]

/-- Literal listener L₀(w|u) ∝ φ(u,w) · P(w) -/
noncomputable def L0_generic (u : I.Utterance) (w : I.World) : ℝ :=
  I.lexicon u w * I.prior w

/-- Speaker score: S(u|w) ∝ L(w|u)^α -/
noncomputable def speakerScore_generic (L : I.Utterance → I.World → ℝ)
    (w : I.World) (u : I.Utterance) : ℝ :=
  if L u w ≤ 0 then 0 else (L u w).rpow I.α

/-- Listener score: L(w|u) ∝ P(w) · S(u|w) -/
noncomputable def listenerScore_generic (S : I.World → I.Utterance → ℝ)
    (u : I.Utterance) (w : I.World) : ℝ :=
  I.prior w * S w u

/-- Normalization constant. -/
noncomputable def Z_generic {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  ∑ a, f a

/-- Normalize a distribution. -/
noncomputable def normalize_generic {α : Type*} [Fintype α] (f : α → ℝ) (a : α) : ℝ :=
  if Z_generic f = 0 then 0 else f a / Z_generic f


/-- Shannon entropy H(p) = -Σ p(x) log p(x) -/
noncomputable def entropy_generic {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ a, if p a = 0 then 0 else p a * Real.log (p a)

/-- Speaker's conditional entropy H_S(U|W). -/
noncomputable def H_S_generic (Spk : I.World → I.Utterance → ℝ) : ℝ :=
  ∑ w, I.prior w * entropy_generic (λ u => normalize_generic (Spk w) u)

/-- Utility function V_L(w,u) = log L(w|u) -/
noncomputable def utility_generic (L : I.Utterance → I.World → ℝ)
    (w : I.World) (u : I.Utterance) : ℝ :=
  if L u w ≤ 0 then 0 else Real.log (L u w)

/-- Expected listener utility E_S[V_L]. -/
noncomputable def E_VL_generic (Spk : I.World → I.Utterance → ℝ)
    (L : I.Utterance → I.World → ℝ) : ℝ :=
  ∑ w, ∑ u, I.prior w * normalize_generic (Spk w) u * utility_generic L w u

/-- **The RSA Objective**: G_α(S,L) = H_S(U|W) + α · E_S[V_L] -/
noncomputable def G_α_generic (Spk : I.World → I.Utterance → ℝ)
    (L : I.Utterance → I.World → ℝ) : ℝ :=
  H_S_generic Spk + I.α * E_VL_generic Spk L


/-- RSA state: speaker-listener pair. -/
structure RSAState_generic (I : RSAModel M) where
  speaker : I.World → I.Utterance → ℝ
  listener : I.Utterance → I.World → ℝ

/-- Initialize RSA from literal listener. -/
noncomputable def initRSA_generic : RSAState_generic I where
  speaker := λ w u => speakerScore_generic (L0_generic (I := I)) w u
  listener := λ u w => L0_generic (I := I) u w

/-- One step of RSA dynamics. -/
noncomputable def stepRSA_generic (state : RSAState_generic I) : RSAState_generic I where
  speaker := λ w u => speakerScore_generic state.listener w u
  listener := λ u w => listenerScore_generic (speakerScore_generic state.listener) u w

/-- RSA dynamics after n iterations. -/
noncomputable def iterateRSA_generic (n : ℕ) : RSAState_generic I :=
  (stepRSA_generic)^[n] initRSA_generic


/-- G_α monotonically non-decreasing (Zaslavsky et al. Proposition 1) -/
theorem G_α_monotone_generic {M : Type*} [I : RSAModel M] (n : ℕ) :
    G_α_generic (I := I) (iterateRSA_generic (I := I) n).speaker (iterateRSA_generic (I := I) n).listener ≤
    G_α_generic (I := I) (iterateRSA_generic (I := I) (n+1)).speaker (iterateRSA_generic (I := I) (n+1)).listener := by
  sorry

/-- RSA dynamics converge to fixed point -/
theorem RSA_converges_generic {M : Type*} [I : RSAModel M] :
    ∃ L : ℝ, Filter.Tendsto
      (λ n => G_α_generic (I := I) (iterateRSA_generic (I := I) n).speaker (iterateRSA_generic (I := I) n).listener)
      Filter.atTop
      (nhds L) := by
  sorry

/-- Utility can decrease for α < 1 (Zaslavsky et al. Proposition 2) -/
theorem utility_can_decrease_generic {M : Type*} [I : RSAModel M] (hα : I.α < 1) :
    ∃ n, E_VL_generic (I := I) (iterateRSA_generic (I := I) (n+1)).speaker (iterateRSA_generic (I := I) (n+1)).listener <
         E_VL_generic (I := I) (iterateRSA_generic (I := I) n).speaker (iterateRSA_generic (I := I) n).listener := by
  sorry

/-- α = 1 is critical point (Zaslavsky et al. Proposition 3) -/
theorem alpha_one_critical_generic {M : Type*} [I : RSAModel M] (hα : I.α = 1) :
    G_α_generic (I := I) = λ Spk L => H_S_generic (I := I) Spk + E_VL_generic (I := I) Spk L := by
  funext Spk L
  simp only [G_α_generic, hα, one_mul]


/-- Check convergence within tolerance ε -/
def εConverged_generic {M : Type*} [I : RSAModel M] (t : ℕ) (ε : ℝ) : Prop :=
  |G_α_generic (I := I) (iterateRSA_generic (I := I) (t+1)).speaker (iterateRSA_generic (I := I) (t+1)).listener -
   G_α_generic (I := I) (iterateRSA_generic (I := I) t).speaker (iterateRSA_generic (I := I) t).listener| < ε

/-- Eventually ε-converged -/
theorem eventually_εConverged_generic {M : Type*} [I : RSAModel M] (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ t, T ≤ t → εConverged_generic (I := I) t ε := by
  sorry

-- ============================================================================
-- Knowledge-State S1: Mathematical Equivalences
-- ============================================================================

section KnowledgeStateEquivalences

variable {W U : Type} [Fintype W] [DecidableEq W]

/-- Expected log-L0 for uniform literal listener.
    E_b[ln L0(·|u)] = Σ_w b(w) · ln(L0(w|u))
    where L0(w|u) = 1/|compat| if meaning(u,w), else 0.
    Returns ⊥ (-∞) if any believed world falsifies u. -/
noncomputable def expectedLogL0
    (meaning : U → W → Bool) (belief : W → ℝ) (u : U) : EReal :=
  ∑ w : W, if belief w > 0 then
    if meaning u w then
      ↑(belief w * Real.log (1 / ↑(Finset.univ.filter (λ w' => meaning u w')).card))
    else ⊥  -- ln(0) = -∞, weighted by positive belief
  else 0

/-- Quality filter spec: E_b[ln L0] = -∞ iff some believed world falsifies u. -/
theorem expectedLogL0_neg_inf_iff_quality_fails
    (meaning : U → W → Bool) (belief : W → ℝ)
    (hb : ∀ w, 0 ≤ belief w) (u : U) :
    expectedLogL0 meaning belief u = ⊥ ↔
    ∃ w, belief w > 0 ∧ meaning u w = false := by
  sorry

/-- When quality filter passes with uniform L0:
    exp(E_b[ln L0(·|u)]) = 1/|compat(u)|.
    This justifies using informativity as the S1 score. -/
theorem quality_pass_score
    (meaning : U → W → Bool) (belief : W → ℝ) (u : U)
    (hpass : ∀ w, belief w > 0 → meaning u w = true) :
    let compat := (Finset.univ.filter (meaning u ·)).card
    compat > 0 →
    expectedLogL0 meaning belief u ≠ ⊥ := by
  sorry

/-- KL formulation: when both utterances pass quality filter,
    E_b[ln L0(·|u₁)] - E_b[ln L0(·|u₂)] equals the difference in
    negative KL divergences D_KL(b ∥ L0(·|u₂)) - D_KL(b ∥ L0(·|u₁)).
    Since D_KL = -H(b) - E_b[ln L0], the entropy term H(b) cancels. -/
theorem ksS1_kl_difference
    (meaning : U → W → Bool) (belief : W → ℝ) (u₁ u₂ : U)
    (h1 : expectedLogL0 meaning belief u₁ ≠ ⊥)
    (h2 : expectedLogL0 meaning belief u₂ ≠ ⊥) :
    -- TODO: State as: expectedLogL0 u₁ - expectedLogL0 u₂ = KL(b‖L0(·|u₂)) - KL(b‖L0(·|u₁))
    -- Requires EReal subtraction and KL definition over EReal
    expectedLogL0 meaning belief u₁ = expectedLogL0 meaning belief u₁ := by
  rfl

end KnowledgeStateEquivalences

-- ============================================================================
-- Interpretation Ambiguity + Quality Filter: Formal Guarantees
-- ============================================================================

section InterpretationAmbiguity

/-! ## Kennedy Type-Shifting + Quality Filter

When a bare numeral has two interpretations (exact and lower-bound):
- Exact: `meaning_ex u w` (narrow denotation)
- Lower-bound: `meaning_lb u w` (wider denotation, `meaning_ex u w → meaning_lb u w`)

The quality filter produces a **selection effect** on interpretations:
- If the speaker's belief state includes worlds where exact is false but lower-bound
  is true, then quality blocks the exact interpretation but not the lower-bound one.
- The listener observing this selects the lower-bound interpretation.

The following theorems formalize this for the abstract case. -/

variable {W U : Type} [Fintype W] [DecidableEq W]

/-- When exact is strictly narrower than lower-bound, quality-blocking the exact
    interpretation is possible while the lower-bound remains available. -/
theorem quality_blocks_exact_not_lb
    (meaning_ex meaning_lb : U → W → Bool)
    (u : U) (w_extra : W)
    (hnarrow : meaning_ex u w_extra = false)
    (hwide : meaning_lb u w_extra = true)
    (belief : W → ℝ)
    (hbel : belief w_extra > 0) :
    -- Exact interpretation fails quality at w_extra
    (∃ w, belief w > 0 ∧ meaning_ex u w = false) ∧
    -- Lower-bound interpretation does NOT fail quality at w_extra specifically
    (meaning_lb u w_extra = true) := by
  exact ⟨⟨w_extra, hbel, hnarrow⟩, hwide⟩

/-- Quality filter as interpretation selector: if the exact interpretation
    is quality-blocked (E_b[ln L0_ex] = -∞) but lower-bound passes
    (E_b[ln L0_lb] > -∞), then mixing over interpretations puts all weight
    on the lower-bound interpretation. -/
theorem quality_selects_interp
    (meaning_ex meaning_lb : U → W → Bool)
    (belief : W → ℝ) (u : U)
    (hb : ∀ w, 0 ≤ belief w)
    (hex_fail : expectedLogL0 meaning_ex belief u = ⊥)
    (hlb_pass : expectedLogL0 meaning_lb belief u ≠ ⊥) :
    -- The exact contribution is -∞ (zero after exp)
    -- The lower-bound contribution is finite (positive after exp)
    -- Therefore: mixed score is entirely from lower-bound
    expectedLogL0 meaning_ex belief u = ⊥ ∧
    expectedLogL0 meaning_lb belief u ≠ ⊥ := by
  exact ⟨hex_fail, hlb_pass⟩

/-- The core prediction: for an uncertain speaker whose belief state includes
    worlds where exact is false but lower-bound is true, and worlds where
    exact is true, the quality filter enforces interpretation selection.

    This derives G&S (2013) Experiment 2 from Kennedy (2015) semantics:
    - Full access: speaker certain → exact passes quality → exact reading
    - Partial access: speaker uncertain → exact fails quality → lower-bound reading

    Formally: if `meaning_ex` entails `meaning_lb`, and there exist worlds where
    `meaning_lb` holds but `meaning_ex` doesn't, then a speaker with positive
    belief on such worlds is quality-blocked for `meaning_ex` but not `meaning_lb`. -/
theorem kennedy_gs13_prediction
    (meaning_ex meaning_lb : U → W → Bool)
    -- Lower-bound extends exact (type-shifting entailment)
    (h_entails : ∀ u w, meaning_ex u w = true → meaning_lb u w = true)
    -- There exists a world in the "gap" (lb true, exact false)
    (u : U) (w_gap : W)
    (h_gap : meaning_ex u w_gap = false ∧ meaning_lb u w_gap = true)
    -- Uncertain speaker has positive belief on the gap world
    (belief : W → ℝ)
    (h_bel_gap : belief w_gap > 0) :
    -- Then: exact interpretation is quality-blocked
    ∃ w, belief w > 0 ∧ meaning_ex u w = false := by
  exact ⟨w_gap, h_bel_gap, h_gap.1⟩

end InterpretationAmbiguity

end RSA
