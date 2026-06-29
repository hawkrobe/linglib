import Linglib.Phonology.HarmonicGrammar.OTLimit
import Linglib.Core.Probability.SoftmaxTheory

/-!
# [goldwater-johnson-2003]: Learning OT Constraint Rankings Using a Maximum Entropy Model
[goldwater-johnson-2003]

[goldwater-johnson-2003] introduce Maximum Entropy models to
constraint-based phonology. Their eq (1) defines the conditional probability
of output y given input x as:

  `Pr(y|x) = exp(Σ wᵢfᵢ(y,x)) / Z(x)`

This IS `softmax(harmonyScore constraints, 1)` — the same `softmax` from
`Core.Agent.RationalAction` used throughout linglib for RSA pragmatics.
The phonology–pragmatics connection is structural: both are log-linear
models over weighted features, differing only in what the features measure.

## Key contributions formalized here

1. **MaxEnt = softmax** (§1): `gjProb` is eq (1) by definition — the conditional
   probability is `softmax (harmonyScore con w (i, ·))`, a constraint set
   `con : CON (I × O) n` weighted by `w : Fin n → ℝ` and softmax-decoded.

2. **Log-likelihood** (§2): The learning objective is log pseudo-likelihood,
   which decomposes as `Σⱼ (H(yⱼ,xⱼ) − logSumExp(H(·,xⱼ)))` — the harmony
   of each observed output minus the log-partition function.

3. **Concavity** (§2): Log-likelihood is concave in each weight
   (`concavity` via `logConditional_concaveOn`). The decomposition
   `log P(y|x;w) = affine(wⱼ) − logSumExpOffset(s,r,wⱼ)` makes this
   affine minus convex = concave, guaranteeing a unique global maximum.

4. **Learning gradient = E[feature]** (§3): The derivative of log-likelihood
   w.r.t. each weight equals observed minus expected feature value
   (`gradient` via `hasDerivAt_logConditional`). At the optimum, observed
   feature counts equal expected feature counts.

5. **Wolof data** (§4): The learned weights for a categorical grammar are
   exponentially separated (`ExponentiallySeparated wolofWeights 1`),
   confirming that MaxEnt reproduces OT for categorical data — the
   empirical counterpart of `maxent_ot_limit`.
-/

namespace GoldwaterJohnson2003

open Core.Optimization Constraints HarmonicGrammar Core Finset Real

-- ============================================================================
-- § 1: MaxEnt = softmax (eq (1))
-- ============================================================================

/-- [goldwater-johnson-2003] eq (1): the conditional probability of output
    `o` given input `i` is the softmax of the harmony score over a constraint
    set `con` weighted by `w` — `Pr(o ∣ i) ∝ exp(-harmonyScore con w (i, o))`.
    Mirrors the per-mapping probability of a classical MaxEnt grammar (a
    constraint set + weight vector, no record). -/
noncomputable def gjProb {I O : Type} [Fintype O] {n : ℕ}
    (con : CON (I × O) n) (w : Fin n → ℝ) (i : I) (o : O) : ℝ :=
  softmax (fun o' => harmonyScore con w (i, o')) o

/-- [goldwater-johnson-2003] eq (1) is `gjProb` by definition — both are
    `softmax(harmonyScore con w, 1)`.

    The same `softmax` function powers RSA pragmatic reasoning
    (`Core.Agent.RationalAction`): both phonological grammar and
    pragmatic inference are log-linear models over weighted features. -/
theorem eq1_is_softmax {I O : Type} [Fintype O] {n : ℕ}
    (con : CON (I × O) n) (w : Fin n → ℝ) (i : I) (o : O) :
    gjProb con w i o = softmax (fun o' => harmonyScore con w (i, o')) o := rfl

-- ============================================================================
-- § 2: Log-Likelihood and Concavity
-- ============================================================================

/-- Log pseudo-likelihood of training data under a MaxEnt grammar (eq (2)).

    `logPL(w) = Σⱼ log P_w(yⱼ | xⱼ)`

    Each term decomposes as `H(yⱼ, xⱼ) − logSumExp(H(·, xⱼ), 1)` via
    `softmax_exponential_family`. -/
noncomputable def logPseudoLikelihood {I O : Type} [Fintype O] {n : ℕ}
    (con : CON (I × O) n) (w : Fin n → ℝ)
    (data : List (I × O)) : ℝ :=
  data.foldl (fun acc ⟨x, y⟩ => acc + Real.log (gjProb con w x y)) 0

/-- Regularized objective (eq (3)): log-likelihood minus L2 penalty.

    `J(w) = logPL(w) − Σᵢ (wᵢ − μᵢ)² / (2σᵢ²)`

    [goldwater-johnson-2003] use μᵢ = 0, σᵢ = σ for all constraints, so the
    penalty is `Σⱼ wⱼ² / (2σ²)` over the grammar's weight vector. -/
noncomputable def regularizedObjective {I O : Type} [Fintype O] {n : ℕ}
    (con : CON (I × O) n) (w : Fin n → ℝ)
    (data : List (I × O))
    (σ : ℝ) : ℝ :=
  logPseudoLikelihood con w data - ∑ j, (w j) ^ 2 / (2 * σ ^ 2)

/-- **Concavity of log-likelihood** (fn. 4): the log conditional likelihood
    of a single observation is concave in each weight, guaranteeing a
    unique global maximum.

    When all weights except `wⱼ` are held fixed, `log P(y|x;w)` decomposes as
    `(wⱼ · sᵧ + rᵧ) − logSumExpOffset(s, r, wⱼ)` where `sᵢ = −cⱼ(yᵢ,x)`
    and `rᵢ = Σₖ≠ⱼ wₖ(−cₖ(yᵢ,x))`. The first term is affine (hence concave);
    the second is convex (`logSumExpOffset_convex`). Concave − convex = concave.

    This is `logConditional_concaveOn` from `Core.Agent.RationalAction`. -/
theorem concavity {ι : Type*} [Fintype ι] [Nonempty ι] (s r : ι → ℝ) (y : ι) :
    ConcaveOn ℝ Set.univ
      (fun wⱼ => (wⱼ * s y + r y) - logSumExp (wⱼ • s + r)) :=
  logConditional_concaveOn s r y

-- ============================================================================
-- § 3: Learning Gradient (connecting to deriv_logSumExp)
-- ============================================================================

/-- **Learning gradient = observed − expected** (§2, §4.2):

    `∂/∂wⱼ log P(y|x) = sᵧ − Σᵢ softmaxOffset(s,r,wⱼ)ᵢ · sᵢ`

    where `sᵢ = −cⱼ(yᵢ,x)` (negated violation count of constraint j on
    candidate i) and `rᵢ = Σₖ≠ⱼ wₖ(−cₖ(yᵢ,x))` (contribution of other
    constraints, constant w.r.t. wⱼ).

    At the maximum, this derivative is zero, so `sᵧ = E_P[s]`: the
    observed feature value equals the expected feature value.

    This is `hasDerivAt_logConditional` from `Core.Agent.RationalAction`. -/
theorem gradient {ι : Type*} [Fintype ι] [Nonempty ι]
    (s r : ι → ℝ) (y : ι) (wⱼ : ℝ) :
    HasDerivAt (fun w => (w * s y + r y) - logSumExp (w • s + r))
      (s y - ∑ i : ι, softmax (wⱼ • s + r) i * s i) wⱼ :=
  hasDerivAt_logConditional s r y wⱼ

-- ============================================================================
-- § 4: Wolof Data (Table 1) — Categorical Grammar
-- ============================================================================

/-- Wolof tongue-root harmony constraints (§3.1, from Boersma 1999).

    The five constraints in ranked order, with learned MaxEnt weights
    from Table 1 (nσ² ≈ 1,200,000). -/
-- UNVERIFIED: exact weight values from Table 1
noncomputable def wolofWeights : Fin 5 → ℝ
  | 0 => 3389/100   -- *RTRHI (33.89)
  | 1 => 17          -- PARSE[RTR] (17.00)
  | 2 => 10          -- GESTURE[CONTOUR] (10.00)
  | 3 => 353/100     -- PARSE[ATR] (3.53)
  | 4 => 41/100      -- *ATRLO (0.41)

/-- All Wolof weights are positive. -/
theorem wolof_pos (i : Fin 5) : 0 < wolofWeights i := by
  fin_cases i <;> norm_num [wolofWeights]

/-- **The learned Wolof weights are exponentially separated (M = 1)**:
    each weight exceeds the sum of all lower-ranked weights.

    This is the empirical counterpart of `maxent_ot_limit`: for a
    categorical grammar (no free variation), MaxEnt learning produces
    weights that satisfy `ExponentiallySeparated`, recovering OT's
    strict ranking. The theoretical direction is:

    `ExponentiallySeparated` ⟹ `lex_imp_lower_violations` ⟹ HG = OT

    Here we verify the converse empirically: OT-like data ⟹ learning
    produces `ExponentiallySeparated` weights. -/
theorem wolof_separated : ExponentiallySeparated wolofWeights 1 := by
  refine ⟨wolof_pos, fun k => ?_⟩
  fin_cases k <;>
    simp +decide only [wolofWeights, Finset.sum_filter, Fin.sum_univ_five] <;>
    norm_num

end GoldwaterJohnson2003
