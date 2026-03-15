import Linglib.Theories.Phonology.HarmonicGrammar.Basic
import Linglib.Core.Agent.Thurstone

/-!
# Noisy Harmonic Grammar and Normal MaxEnt
@cite{boersma-pater-2016} @cite{flemming-2021}

Noisy HG (@cite{boersma-pater-2016}) adds i.i.d. Gaussian noise N(0,σ²) to
each constraint weight before evaluation. For binary choice between
candidates a and b, the harmony score difference H(a)−H(b) becomes a
Gaussian random variable with variance σ² · Σⱼ(cⱼ(a)−cⱼ(b))² — the noise
is **context-dependent**, scaling with squared violation differences.

Normal MaxEnt (@cite{flemming-2021}) instead adds i.i.d. Gaussian noise
N(0,ε²) directly to candidate scores, giving a constant noise standard
deviation σ_d = ε√2 for binary choice.

Both are instances of Thurstone Case V (`Core.Thurstone`).

## MaxEnt logit-harmony identity

For classical MaxEnt (Gumbel noise → softmax), the log-odds ratio between
any two candidates equals their harmony score difference:

  `log(P(a)/P(b)) = H(a) − H(b)`

This implies **logit uniformity** (@cite{flemming-2021} §3): adding one
violation of constraint j changes the logit by exactly −wⱼ, regardless
of the violation profile elsewhere. NHG lacks this property because its
noise variance σ_d depends on the violation profile.
-/

namespace Theories.Phonology.HarmonicGrammar

open Core Real

-- ============================================================================
-- § 1: NHG Noise Variance
-- ============================================================================

/-- Sum of squared violation differences between two candidates.
    This determines the NHG noise variance: σ_d² = σ² · violationDiffSqSum. -/
noncomputable def violationDiffSqSum {C : Type}
    (constraints : List (WeightedConstraint C)) (a b : C) : ℝ :=
  constraints.foldl (λ acc con =>
    acc + ((con.eval a : ℝ) - (con.eval b : ℝ)) ^ 2) 0

/-- Sum of squared violation differences (ℚ, computable).
    Use this for concrete examples with `native_decide`. -/
def violationDiffSqSumQ {C : Type}
    (constraints : List (WeightedConstraint C)) (a b : C) : ℚ :=
  constraints.foldl (λ acc con =>
    acc + ((con.eval a : ℚ) - (con.eval b : ℚ)) ^ 2) 0

/-- NHG noise standard deviation for binary choice:
    σ_d = σ · √(Σⱼ (cⱼ(a) − cⱼ(b))²).

    The noise is **context-dependent**: it scales with the violation
    difference profile, not just the per-weight noise σ. -/
noncomputable def nhgSigmaD {C : Type}
    (constraints : List (WeightedConstraint C)) (sigma : ℝ) (a b : C) : ℝ :=
  sigma * Real.sqrt (violationDiffSqSum constraints a b)

-- ============================================================================
-- § 2: NHG as Thurstone Case V
-- ============================================================================

/-- NHG binary choice as a Thurstone Case V model.

    - Scale values are harmony scores: `scale(0) = H(a)`, `scale(1) = H(b)`
    - Thurstone σ = σ_d / √2, so that Thurstone's `Φ(d/(σ_T·√2))`
      equals NHG's `Φ((H(a)−H(b))/σ_d)`.

    Requires non-zero violation differences (otherwise σ_d = 0 and
    the choice is deterministic). -/
noncomputable def nhgAsThurstoneV {C : Type}
    (constraints : List (WeightedConstraint C)) (sigma : ℝ) (hsigma : 0 < sigma)
    (a b : C) (h_diff : 0 < violationDiffSqSum constraints a b) :
    ThurstoneCaseV (Fin 2) where
  scale i := if i = 0 then harmonyScoreR constraints a
             else harmonyScoreR constraints b
  sigma := nhgSigmaD constraints sigma a b / Real.sqrt 2
  sigma_pos := div_pos (mul_pos hsigma (Real.sqrt_pos.mpr h_diff))
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))

/-- **NHG binary choice probability** (@cite{flemming-2021} eq (15)):
    `P(a ≻ b) = Φ((H(a) − H(b)) / σ_d)`.

    The Thurstone σ is set to `σ_d / √2` so that Thurstone's
    `Φ(d / (σ_T · √2))` reduces to `Φ(d / σ_d)`. -/
theorem nhg_choiceProb_eq {C : Type}
    (constraints : List (WeightedConstraint C)) (sigma : ℝ) (hsigma : 0 < sigma)
    (a b : C) (h_diff : 0 < violationDiffSqSum constraints a b) :
    (nhgAsThurstoneV constraints sigma hsigma a b h_diff).choiceProb 0 1 =
    normalCDF ((harmonyScoreR constraints a - harmonyScoreR constraints b) /
               nhgSigmaD constraints sigma a b) := by
  simp only [nhgAsThurstoneV, ThurstoneCaseV.choiceProb, nhgSigmaD]
  have h01 : ¬(1 : Fin 2) = (0 : Fin 2) := by decide
  simp only [h01, ↓reduceIte]
  have hsqrt2 : (Real.sqrt 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  simp only [div_mul_cancel₀ _ hsqrt2]

-- ============================================================================
-- § 3: Normal MaxEnt
-- ============================================================================

/-- Normal MaxEnt noise standard deviation: σ_d = ε√2 (constant).

    When noise is added i.i.d. N(0,ε²) to each candidate score, the
    difference of two candidates is N(H(a)−H(b), 2ε²), giving σ_d = ε√2
    regardless of the violation profile. This is the key distinction
    from NHG, where σ_d varies by context. -/
noncomputable def normalMaxEntSigmaD (epsilon : ℝ) : ℝ :=
  epsilon * Real.sqrt 2

/-- Normal MaxEnt binary choice as a Thurstone Case V model.

    Same as NHG but with constant σ_d = ε√2, so Thurstone σ = ε. -/
noncomputable def normalMaxEntAsThurstoneV {C : Type}
    (constraints : List (WeightedConstraint C)) (epsilon : ℝ) (heps : 0 < epsilon)
    (a b : C) : ThurstoneCaseV (Fin 2) where
  scale i := if i = 0 then harmonyScoreR constraints a
             else harmonyScoreR constraints b
  sigma := epsilon
  sigma_pos := heps

/-- **Normal MaxEnt binary choice probability** (@cite{flemming-2021} eq (17)):
    `P(a ≻ b) = Φ((H(a) − H(b)) / (ε√2))`.

    Since the Thurstone σ is ε and `normalMaxEntSigmaD ε = ε√2`,
    Thurstone's `Φ(d / (ε · √2))` directly gives the Normal MaxEnt formula. -/
theorem normalMaxEnt_choiceProb_eq {C : Type}
    (constraints : List (WeightedConstraint C)) (epsilon : ℝ) (heps : 0 < epsilon)
    (a b : C) :
    (normalMaxEntAsThurstoneV constraints epsilon heps a b).choiceProb 0 1 =
    normalCDF ((harmonyScoreR constraints a - harmonyScoreR constraints b) /
               normalMaxEntSigmaD epsilon) := by
  simp only [normalMaxEntAsThurstoneV, ThurstoneCaseV.choiceProb, normalMaxEntSigmaD]
  have h01 : ¬(1 : Fin 2) = (0 : Fin 2) := by decide
  simp only [h01, ↓reduceIte]

-- ============================================================================
-- § 4: MaxEnt Logit-Harmony Identity
-- ============================================================================

/-- **Logit uniformity** (MaxEnt diagnostic; @cite{flemming-2021} §3):
    for softmax with α = 1, the log-odds between any two alternatives
    equals their score difference. Hence changing one score by −w
    changes the log-odds by exactly −w, regardless of context.

    This property characterizes MaxEnt among stochastic HG variants.
    NHG lacks it because its noise variance σ_d depends on the violation
    profile (see `nhgSigmaD`).

    See also `maxent_logit_as_finsum` (Separability.lean) for the
    Fin-indexed decomposition, and `me_predicts_hz` for the consequence
    that independent violation differences yield HZ's generalization. -/
theorem logit_uniformity {ι : Type} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) (a b : ι) :
    log (softmax s 1 a / softmax s 1 b) = s a - s b := by
  rw [log_softmax_odds]; ring

/-- **MaxEnt logit-harmony identity**: the log-odds ratio between two
    candidates equals their harmony score difference.

    `log(P(a)/P(b)) = H(a) − H(b)`

    Instantiation of `logit_uniformity` with harmony scores. -/
theorem maxent_logit_harmony {C : Type} [Fintype C] [Nonempty C]
    (constraints : List (WeightedConstraint C)) (a b : C) :
    log (softmax (harmonyScoreR constraints) 1 a /
         softmax (harmonyScoreR constraints) 1 b) =
    harmonyScoreR constraints a - harmonyScoreR constraints b :=
  logit_uniformity (harmonyScoreR constraints) a b

/-- **Ratio independence** (IIA for MaxEnt): the probability ratio between
    two candidates depends only on their own harmony scores.

    `P(a)/P(b) = exp(H(a) − H(b))`

    Adding or removing other candidates from the competition doesn't
    change the ratio. Corollary of `softmax_odds` with α = 1. -/
theorem maxent_iia {C : Type} [Fintype C] [Nonempty C]
    (constraints : List (WeightedConstraint C)) (a b : C) :
    softmax (harmonyScoreR constraints) 1 a /
    softmax (harmonyScoreR constraints) 1 b =
    exp (harmonyScoreR constraints a - harmonyScoreR constraints b) := by
  rw [softmax_odds]; congr 1; ring

-- ============================================================================
-- § 5: Harmony Difference Decomposition
-- ============================================================================

/-- Helper: foldl with subtraction equals initial value minus the sum. -/
private lemma foldl_sub_eq_init_sub_sum {α : Type} (f : α → ℚ)
    (l : List α) (init : ℚ) :
    l.foldl (fun acc x => acc - f x) init = init - (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons _ _ ih => simp only [List.foldl, List.map, List.sum_cons]; rw [ih]; ring

/-- **Harmony difference decomposition**: the harmony score difference
    equals the negated weighted sum of violation differences.

    `H(a) − H(b) = −Σⱼ wⱼ · (cⱼ(a) − cⱼ(b))`

    This is the bridge between abstract harmony scores and the constraint
    violation patterns used in empirical analyses (e.g., French schwa). -/
theorem harmonyScore_diff {C : Type}
    (constraints : List (WeightedConstraint C)) (a b : C) :
    harmonyScore constraints a - harmonyScore constraints b =
    -(constraints.map (fun con =>
        con.weight * ((con.eval a : ℚ) - (con.eval b : ℚ)))).sum := by
  simp only [harmonyScore, foldl_sub_eq_init_sub_sum, zero_sub]
  have h_sum : ∀ (l : List (WeightedConstraint C)),
      (l.map (fun con => con.weight * (con.eval a : ℚ))).sum -
      (l.map (fun con => con.weight * (con.eval b : ℚ))).sum =
      (l.map (fun con => con.weight * ((con.eval a : ℚ) - (con.eval b : ℚ)))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons _ _ ih => simp only [List.map, List.sum_cons]; linarith
  linarith [h_sum constraints]

/-- Harmony difference decomposition in ℝ. -/
theorem harmonyScoreR_diff {C : Type}
    (constraints : List (WeightedConstraint C)) (a b : C) :
    harmonyScoreR constraints a - harmonyScoreR constraints b =
    -((constraints.map (fun con =>
        con.weight * ((con.eval a : ℚ) - (con.eval b : ℚ)))).sum : ℝ) := by
  simp only [harmonyScoreR, ← Rat.cast_sub, harmonyScore_diff, Rat.cast_neg]

end Theories.Phonology.HarmonicGrammar
