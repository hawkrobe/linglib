/-
# RSA Model (Real Analysis Version)

RSA scenario using real numbers for mathematical proofs.

## Architecture

```
RSAScenario (Core.lean)  →  ℚ, ℕ  →  Computation  →  #eval works!
RSAScenarioR (this file) →  ℝ     →  Proofs      →  Zaslavsky theorems
```

Convert between them with `RSAScenario.toReal`.

## Future

Once migration is complete, this will become the main `RSAScenario` type,
with the computational version as a specialization.

## References

- Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of human
  pragmatic reasoning. arXiv:2005.06641.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Basic
import Linglib.Theories.RSA.Core

namespace RSA

-- ============================================================================
-- PART 1: RSA Scenario with Real Numbers (for proofs)
-- ============================================================================

/--
RSA scenario using real numbers.

This version supports:
- Real-valued rationality parameter α (including α < 1)
- Zaslavsky et al. convergence theorems
- Real analysis (limits, continuity)

For computation, use `RSAScenario` from Core.lean instead.
-/
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

-- ============================================================================
-- PART 2: Conversion from RSAScenario (ℚ) to RSAScenarioR (ℝ)
-- ============================================================================

/--
Convert a computational RSAScenario to RSAScenarioR for proofs.

This lifts ℚ → ℝ and ℕ → ℝ, enabling real analysis.

Note: This uses specified default values for Interp and Lexicon parameters.
-/
def RSAScenario.toReal (S : RSAScenario)
    [Fintype S.Utterance] [Fintype S.World]
    (defaultInterp : S.Interp) (defaultLexicon : S.Lexicon) : RSAScenarioR where
  Utterance := S.Utterance
  World := S.World
  lexicon u w := (S.φ defaultInterp defaultLexicon u w : ℝ)
  prior w := (S.worldPrior w : ℝ)
  α := (S.α : ℝ)
  α_nonneg := Nat.cast_nonneg S.α
  lexicon_nonneg := fun _ _ => by sorry  -- Would need to show ℚ values are non-negative
  prior_nonneg := fun _ => by sorry
  prior_pos := by sorry

-- ============================================================================
-- PART 3: RSAModel typeclass (for generic theorems)
-- ============================================================================

/--
RSAModel typeclass - enables instance-based theorem application.

This is equivalent to RSAScenarioR but as a typeclass, allowing:
```lean
instance : RSAModel MyType := scenario.toModel
-- Now G_α_monotone_generic applies to MyType
```
-/
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
def RSAScenario.toModel (S : RSAScenario)
    [Fintype S.Utterance] [Fintype S.World]
    (defaultInterp : S.Interp) (defaultLexicon : S.Lexicon) : RSAModel S.Utterance :=
  (RSAScenario.toReal S defaultInterp defaultLexicon).toModel

-- ============================================================================
-- PART 4: RSA Dynamics (Generic)
-- ============================================================================

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

-- ============================================================================
-- PART 5: Information-Theoretic Quantities
-- ============================================================================

/-- Shannon entropy H(p) = -Σ p(x) log p(x) -/
noncomputable def entropy_generic {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ a, if p a = 0 then 0 else p a * Real.log (p a)

/-- Speaker's conditional entropy H_S(U|W). -/
noncomputable def H_S_generic (Spk : I.World → I.Utterance → ℝ) : ℝ :=
  ∑ w, I.prior w * entropy_generic (fun u => normalize_generic (Spk w) u)

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

-- ============================================================================
-- PART 6: RSA State and Dynamics
-- ============================================================================

/-- RSA state: speaker-listener pair. -/
structure RSAState_generic (I : RSAModel M) where
  speaker : I.World → I.Utterance → ℝ
  listener : I.Utterance → I.World → ℝ

/-- Initialize RSA from literal listener. -/
noncomputable def initRSA_generic : RSAState_generic I where
  speaker := fun w u => speakerScore_generic (L0_generic (I := I)) w u
  listener := fun u w => L0_generic (I := I) u w

/-- One step of RSA dynamics. -/
noncomputable def stepRSA_generic (state : RSAState_generic I) : RSAState_generic I where
  speaker := fun w u => speakerScore_generic state.listener w u
  listener := fun u w => listenerScore_generic (speakerScore_generic state.listener) u w

/-- RSA dynamics after n iterations. -/
noncomputable def iterateRSA_generic (n : ℕ) : RSAState_generic I :=
  (stepRSA_generic)^[n] initRSA_generic

-- ============================================================================
-- PART 7: Zaslavsky Theorems
-- ============================================================================

/--
**Proposition 1 (Zaslavsky et al.)**: G_α is monotonically non-decreasing.

This theorem applies to ANY model satisfying `RSAModel`.
-/
theorem G_α_monotone_generic {M : Type*} [I : RSAModel M] (n : ℕ) :
    G_α_generic (I := I) (iterateRSA_generic (I := I) n).speaker (iterateRSA_generic (I := I) n).listener ≤
    G_α_generic (I := I) (iterateRSA_generic (I := I) (n+1)).speaker (iterateRSA_generic (I := I) (n+1)).listener := by
  sorry

/--
**Convergence**: RSA dynamics converge to a fixed point in G_α.
-/
theorem RSA_converges_generic {M : Type*} [I : RSAModel M] :
    ∃ L : ℝ, Filter.Tendsto
      (fun n => G_α_generic (I := I) (iterateRSA_generic (I := I) n).speaker (iterateRSA_generic (I := I) n).listener)
      Filter.atTop
      (nhds L) := by
  sorry

/--
**Proposition 2 (Zaslavsky et al.)**: Utility can decrease for α < 1.
-/
theorem utility_can_decrease_generic {M : Type*} [I : RSAModel M] (hα : I.α < 1) :
    ∃ n, E_VL_generic (I := I) (iterateRSA_generic (I := I) (n+1)).speaker (iterateRSA_generic (I := I) (n+1)).listener <
         E_VL_generic (I := I) (iterateRSA_generic (I := I) n).speaker (iterateRSA_generic (I := I) n).listener := by
  sorry

/--
**Proposition 3 (Zaslavsky et al.)**: α = 1 is the critical point.
-/
theorem alpha_one_critical_generic {M : Type*} [I : RSAModel M] (hα : I.α = 1) :
    G_α_generic (I := I) = fun Spk L => H_S_generic (I := I) Spk + E_VL_generic (I := I) Spk L := by
  funext Spk L
  simp only [G_α_generic, hα, one_mul]

-- ============================================================================
-- PART 8: Convergence Criteria
-- ============================================================================

/-- Check if RSA has converged within tolerance ε. -/
def εConverged_generic {M : Type*} [I : RSAModel M] (t : ℕ) (ε : ℝ) : Prop :=
  |G_α_generic (I := I) (iterateRSA_generic (I := I) (t+1)).speaker (iterateRSA_generic (I := I) (t+1)).listener -
   G_α_generic (I := I) (iterateRSA_generic (I := I) t).speaker (iterateRSA_generic (I := I) t).listener| < ε

/-- Eventually ε-converged: For any ε > 0, RSA is eventually ε-converged. -/
theorem eventually_εConverged_generic {M : Type*} [I : RSAModel M] (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ t, T ≤ t → εConverged_generic (I := I) t ε := by
  sorry

end RSA
