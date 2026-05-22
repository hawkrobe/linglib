import Linglib.Core.Constraint.NoisyHG
import Linglib.Core.Constraint.Separability
import Linglib.Core.Constraint.System
import Linglib.Core.Agent.GumbelLuce

/-!
# @cite{flemming-2021}: Comparing MaxEnt and Noisy Harmonic Grammar
@cite{flemming-2021}

@cite{flemming-2021} compares three stochastic Harmonic Grammar variants —
MaxEnt, Noisy HG (NHG), and Normal MaxEnt — identifying **logit uniformity**
as the diagnostic that distinguishes them.

## The three models as Random Utility Models

All three HG variants are Random Utility Models (RUMs) differing only in
the noise distribution added to the deterministic harmony scores:

| Model           | Noise target  | Distribution | Binary P        | Reference |
|-----------------|---------------|--------------|-----------------|-----------|
| MaxEnt          | candidates    | Gumbel       | logistic(H−H')  | `maxent_eq_gumbelRUM` |
| NHG             | weights       | Gaussian     | Φ((H−H')/σ_d)  | `nhg_choiceProb_eq` |
| Normal MaxEnt   | candidates    | Gaussian     | Φ((H−H')/(ε√2))| `normalMaxEnt_choiceProb_eq` |

## Key diagnostic: logit uniformity

MaxEnt exhibits **logit uniformity** (eq (10)): adding one violation of
constraint j changes the logit by exactly −wⱼ, regardless of the tableau
context. This follows from the log-odds identity (`logit_uniformity`):

  `log(P(a)/P(b)) = H(a) − H(b)`

NHG violates logit uniformity because its noise standard deviation
σ_d = σ · √(Σ(cⱼ(a)−cⱼ(b))²) (`nhgSigmaD`) depends on the violation
difference profile. The same harmony difference ΔH produces different
probits ΔH/σ_d in different contexts.

Normal MaxEnt has **probit** uniformity (constant σ_d = ε√2) rather than
logit uniformity, leading to probit (Φ) rather than logistic probability
functions — an empirically distinguishable prediction.

## French schwa data

Flemming tests logit uniformity on French schwa deletion across 8
phonological contexts with 6 constraints (Table (35)). Contexts that share
the same \*Clash violation difference should show the same logit difference
under MaxEnt. We encode this data and verify:
- `logit_uniformity_clash`: the \*Clash contribution to the harmony
  difference is identical across all four paired contexts (MaxEnt prediction)
- `nhg_sigmaD_sq_varies`: the NHG noise variance σ_d² differs between
  paired contexts, violating probit uniformity (NHG prediction)
-/

namespace Flemming2021

open Core.Constraint Core Real

-- ============================================================================
-- § 1: MaxEnt as Gumbel RUM (McFadden)
-- ============================================================================

/-- **MaxEnt = Gumbel RUM** (@cite{flemming-2021} §4/§10): MaxEnt probability
    is exactly the McFadden integral with Gumbel scale β = 1.

    This formalizes the RUM connection: MaxEnt adds i.i.d. Gumbel noise to
    candidate harmonies, and by McFadden's theorem
    (`mcfaddenIntegral_eq_softmax`), the resulting choice probability is
    softmax — i.e., the standard MaxEnt formula. -/
theorem maxent_eq_gumbelRUM {C : Type} [Fintype C] [Nonempty C]
    (constraints : List (WeightedConstraint C)) (c : C) :
    mcfaddenIntegral (harmonyScoreR constraints) 1 c =
    softmax (harmonyScoreR constraints) 1 c := by
  rw [mcfaddenIntegral_eq_softmax _ one_pos]
  simp only [div_one]

-- ============================================================================
-- § 2: MaxEnt Logit Uniformity (eq (10))
-- ============================================================================

/-- Flemming's eq (10): `logit(P_a) = h_a − h_b`.
    The MaxEnt logit-harmony identity. Alias for `maxent_logit_harmony`. -/
theorem eq10_logit_harmony {C : Type} [Fintype C] [Nonempty C]
    (constraints : List (WeightedConstraint C)) (a b : C) :
    log (softmax (harmonyScoreR constraints) 1 a /
         softmax (harmonyScoreR constraints) 1 b) =
    harmonyScoreR constraints a - harmonyScoreR constraints b :=
  maxent_logit_harmony constraints a b

/-- MaxEnt ratio independence (IIA): `P(a)/P(b) = exp(H(a) − H(b))`.
    The probability ratio depends only on the candidates' own scores,
    not on any other candidates. Corollary of `softmax_odds` with α = 1. -/
theorem iia {C : Type} [Fintype C] [Nonempty C]
    (constraints : List (WeightedConstraint C)) (a b : C) :
    softmax (harmonyScoreR constraints) 1 a /
    softmax (harmonyScoreR constraints) 1 b =
    exp (harmonyScoreR constraints a - harmonyScoreR constraints b) :=
  maxent_iia constraints a b

/-- **MaxEnt binary logistic** (@cite{flemming-2021} eq (9)/(11)):
    with two candidates, MaxEnt probability is the logistic function
    of the harmony difference.

    `P(0) = 1 / (1 + e^{-(H(0) − H(1))})` = `logistic(H(0) − H(1))`

    Corollary of `softmax_binary` with α = 1. -/
theorem eq9_maxent_binary_logistic
    (constraints : List (WeightedConstraint (Fin 2))) :
    softmax (harmonyScoreR constraints) 1 0 =
    logistic (harmonyScoreR constraints 0 - harmonyScoreR constraints 1) := by
  rw [softmax_binary, one_mul]

-- ============================================================================
-- § 3: French Schwa Data (Table (35))
-- ============================================================================

/-- Violation difference matrix: ə candidate minus ∅ candidate.
    Rows = 8 contexts, columns = 6 constraints.
    Constraint order: 0=NoSchwa, 1=\*CCC, 2=\*Clash, 3=Max, 4=Dep, 5=\*Cluster.
    Table (35) from @cite{flemming-2021}, data from @cite{smith-pater-2020}. -/
def schwaDiff (ctx : Fin 8) (con : Fin 6) : Int :=
  match ctx.val, con.val with
  -- /∅/, C, _σσ́
  | 0, 0 => -1 | 0, 1 =>  0 | 0, 2 =>  0 | 0, 3 =>  0 | 0, 4 => -1 | 0, 5 =>  1
  -- /∅/, C, _σ́
  | 1, 0 => -1 | 1, 1 =>  0 | 1, 2 =>  1 | 1, 3 =>  0 | 1, 4 => -1 | 1, 5 =>  1
  -- /∅/, CC, _σσ́
  | 2, 0 => -1 | 2, 1 =>  1 | 2, 2 =>  0 | 2, 3 =>  0 | 2, 4 => -1 | 2, 5 =>  0
  -- /∅/, CC, _σ́
  | 3, 0 => -1 | 3, 1 =>  1 | 3, 2 =>  1 | 3, 3 =>  0 | 3, 4 => -1 | 3, 5 =>  0
  -- /ə/, C, _σσ́
  | 4, 0 => -1 | 4, 1 =>  0 | 4, 2 =>  0 | 4, 3 =>  1 | 4, 4 =>  0 | 4, 5 =>  1
  -- /ə/, C, _σ́
  | 5, 0 => -1 | 5, 1 =>  0 | 5, 2 =>  1 | 5, 3 =>  1 | 5, 4 =>  0 | 5, 5 =>  1
  -- /ə/, CC, _σσ́
  | 6, 0 => -1 | 6, 1 =>  1 | 6, 2 =>  0 | 6, 3 =>  1 | 6, 4 =>  0 | 6, 5 =>  0
  -- /ə/, CC, _σ́
  | 7, 0 => -1 | 7, 1 =>  1 | 7, 2 =>  1 | 7, 3 =>  1 | 7, 4 =>  0 | 7, 5 =>  0
  | _, _ => 0

/-- The four \*Clash pairs: contexts that differ only in \*Clash (index 2).
    Each pair is (without \*Clash, with \*Clash). -/
def clashPairs : Fin 4 → Fin 8 × Fin 8
  | 0 => (0, 1)  -- /∅/, C
  | 1 => (2, 3)  -- /∅/, CC
  | 2 => (4, 5)  -- /ə/, C
  | 3 => (6, 7)  -- /ə/, CC

-- ============================================================================
-- § 4: Logit Uniformity on French Schwa
-- ============================================================================

/-- \*Clash pairs differ only in the \*Clash column (index 2):
    for each pair, all non-\*Clash violations are identical. -/
theorem clash_pairs_identical_except_clash (pair : Fin 4) (j : Fin 6)
    (hj : j ≠ 2) :
    schwaDiff (clashPairs pair).1 j = schwaDiff (clashPairs pair).2 j := by
  fin_cases pair <;> fin_cases j <;> simp_all [clashPairs, schwaDiff]

/-- The \*Clash violation difference is exactly 1 for all pairs. -/
theorem clash_diff_is_one (pair : Fin 4) :
    schwaDiff (clashPairs pair).2 2 - schwaDiff (clashPairs pair).1 2 = 1 := by
  fin_cases pair <;> simp [clashPairs, schwaDiff]

/-- **Logit uniformity for \*Clash** (@cite{flemming-2021} §7.1):
    the \*Clash contribution to the harmony difference is the same
    across all four paired contexts.

    For any weights `w`, the harmony difference change between paired
    contexts = −w₂ (\*Clash weight), independent of context. This follows
    from `clash_pairs_identical_except_clash`: since non-\*Clash violations
    are identical in each pair, their weighted contributions cancel,
    leaving only −w₂ · 1 = −w₂.

    This is a special case of `me_predicts_hz` (Separability.lean):
    the \*Clash violation differences are column-insensitive (constant
    across paired contexts), so the weighted sum satisfies the
    constant-difference identity. -/
theorem logit_uniformity_clash (w : Fin 6 → ℚ) (pair : Fin 4) :
    (Finset.univ.sum fun j => w j * (schwaDiff (clashPairs pair).2 j : ℚ)) -
    (Finset.univ.sum fun j => w j * (schwaDiff (clashPairs pair).1 j : ℚ)) =
    w 2 := by
  have h_eq : ∀ j : Fin 6, j ≠ 2 →
      w j * (schwaDiff (clashPairs pair).2 j : ℚ) =
      w j * (schwaDiff (clashPairs pair).1 j : ℚ) := by
    intro j hj; congr 1; exact_mod_cast (clash_pairs_identical_except_clash pair j hj).symm
  have h_diff : (schwaDiff (clashPairs pair).2 2 : ℚ) -
      (schwaDiff (clashPairs pair).1 2 : ℚ) = 1 := by exact_mod_cast clash_diff_is_one pair
  fin_cases pair <;> simp_all [clashPairs, schwaDiff, Fin.sum_univ_six]

-- ============================================================================
-- § 5: Observed P(schwa) Data (Table 2)
-- ============================================================================

/-- Observed probability of schwa realization across 8 contexts.
    Data from @cite{smith-pater-2020} (Table 2 of @cite{flemming-2021}).

    Values are approximate proportions (hundredths). The key pattern:
    within each \*Clash pair, the +\*Clash context always has higher P(schwa),
    consistent with the \*Clash constraint favoring schwa insertion. -/
def observedP : Fin 8 → ℚ
  | 0 => 9/100   -- /∅/, C, _σσ́
  | 1 => 12/100  -- /∅/, C, _σ́
  | 2 => 68/100  -- /∅/, CC, _σσ́
  | 3 => 83/100  -- /∅/, CC, _σ́
  | 4 => 56/100  -- /ə/, C, _σσ́
  | 5 => 65/100  -- /ə/, C, _σ́
  | 6 => 91/100  -- /ə/, CC, _σσ́
  | 7 => 94/100  -- /ə/, CC, _σ́

/-- Adding a \*Clash violation increases P(schwa) in every paired context. -/
theorem clash_increases_schwa (pair : Fin 4) :
    observedP (clashPairs pair).1 < observedP (clashPairs pair).2 := by
  fin_cases pair <;> simp [clashPairs, observedP] <;> norm_num

-- ============================================================================
-- § 6: NHG Probit Non-Uniformity
-- ============================================================================

/-- Sum of squared violation differences for a context.

    This is the study-local analogue of `violationDiffSqSumQ` from
    `NoisyHG.lean`: both compute `Σⱼ (cⱼ(ə) − cⱼ(∅))²`, but `schwaSqSum`
    operates on the pre-computed difference matrix `schwaDiff` (Table (35))
    rather than a `WeightedConstraint` list. -/
def schwaSqSum (ctx : Fin 8) : Nat :=
  (List.finRange 6).foldl (fun acc j => acc + (schwaDiff ctx j).natAbs ^ 2) 0

/-- NHG noise variance σ_d² is context-dependent: without \*Clash,
    the squared violation sum is 3; with \*Clash, it is 4.
    The same \*Clash violation change produces different σ_d values
    in different tableaux — σ_d = √3 vs σ_d = 2 (Table 3 of
    @cite{flemming-2021}). -/
theorem nhg_sigmaD_sq_varies :
    schwaSqSum 0 = 3 ∧ schwaSqSum 1 = 4 ∧
    schwaSqSum 2 = 3 ∧ schwaSqSum 3 = 4 ∧
    schwaSqSum 4 = 3 ∧ schwaSqSum 5 = 4 ∧
    schwaSqSum 6 = 3 ∧ schwaSqSum 7 = 4 := by native_decide

/-- NHG probit change when moving from one context to another:
    the change in the probit `Φ⁻¹(P) = Δh / σ_d` when σ_d changes.

    `h_init` = initial harmony difference, `Δh` = harmony change (e.g., −w_Clash),
    `σ_d` / `σ_d'` = noise s.d. before/after the change. -/
noncomputable def nhgProbitChange (h_init Δh σ_d σ_d' : ℝ) : ℝ :=
  (h_init + Δh) / σ_d' - h_init / σ_d

/-- **Probit non-uniformity** (@cite{flemming-2021} §7.2): when σ_d ≠ σ_d',
    the NHG probit change depends on the initial harmony difference `h_init`.

    Two contexts with different initial harmonies `h₁ ≠ h₂` but the same
    \*Clash change `Δh` produce different probit changes. This is because
    the denominator shift (σ_d → σ_d') rescales the existing harmony
    difference differently depending on its magnitude.

    Concretely, for French schwa with σ = 1 (@cite{flemming-2021} §7.2):
    adding a \*Clash violation changes σ_d from √3 to 2 in all pairs,
    but the initial harmony difference h_ə − h_∅ differs between pairs
    (e.g., −2.2 for pair (0,1) vs 0.01 for pair (4,5)), so the probit
    changes differ despite the same \*Clash change. -/
theorem nhg_probit_change_depends_on_h_init
    (Δh σ_d σ_d' h₁ h₂ : ℝ) (hσ : σ_d ≠ σ_d')
    (hσ_pos : 0 < σ_d) (hσ'_pos : 0 < σ_d') (hh : h₁ ≠ h₂) :
    nhgProbitChange h₁ Δh σ_d σ_d' ≠ nhgProbitChange h₂ Δh σ_d σ_d' := by
  simp only [nhgProbitChange]
  intro heq
  have h_eq : h₁ * (1 / σ_d' - 1 / σ_d) = h₂ * (1 / σ_d' - 1 / σ_d) := by
    field_simp at heq ⊢; linarith
  have h_ne : (1 : ℝ) / σ_d' - 1 / σ_d ≠ 0 := by
    rw [div_sub_div _ _ (ne_of_gt hσ'_pos) (ne_of_gt hσ_pos)]
    apply div_ne_zero _ (mul_ne_zero (ne_of_gt hσ'_pos) (ne_of_gt hσ_pos))
    simp only [one_mul, mul_one]
    exact sub_ne_zero.mpr hσ
  exact hh (mul_right_cancel₀ h_ne h_eq)

/-- **Probit change decomposition** (@cite{flemming-2021} eq (38b)):
    the NHG probit change decomposes into a context-dependent term
    (proportional to initial harmony difference) and a uniform term.

    `Δprobit = h · (σ_d − σ_d') / (σ_d · σ_d') + Δh / σ_d'`

    The first term is why NHG violates probit uniformity: it depends on
    `h_init`, which varies across contexts. -/
theorem nhgProbitChange_decomp (h_init Δh σ_d σ_d' : ℝ)
    (hσ_pos : 0 < σ_d) (hσ'_pos : 0 < σ_d') :
    nhgProbitChange h_init Δh σ_d σ_d' =
    h_init * (σ_d - σ_d') / (σ_d * σ_d') + Δh / σ_d' := by
  simp only [nhgProbitChange]
  field_simp
  ring

-- ============================================================================
-- § 7: Three-Candidate NHG Example (Table (45))
-- ============================================================================

-- Flemming's Table (45) shows that NHG can distinguish candidates with
-- equal harmony scores: with w₁ = 15, w₂ = w₃ = 8, candidates b and c
-- have the same harmony H = −16, but different NHG noise variances
-- σ²_d(b−a) = 5σ² ≠ 3σ² = σ²_d(c−a) and non-zero covariance
-- Cov(ε_b−ε_a, ε_c−ε_a) ≠ 0. So NHG assigns them different
-- probabilities despite equal MaxEnt probabilities (§9).

private inductive Cand3 | a | b | c deriving DecidableEq, Repr, Fintype

private instance : Nonempty Cand3 := ⟨.a⟩

private def table45C : List (WeightedConstraint Cand3) :=
  [{ name := "C₁", family := .markedness, eval := fun | .a => 1 | _ => 0, weight := 15 },
   { name := "C₂", family := .markedness, eval := fun | .b => 2 | .c => 1 | _ => 0, weight := 8 },
   { name := "C₃", family := .markedness, eval := fun | .c => 1 | _ => 0, weight := 8 }]

/-- Candidates b and c have equal harmony: H(b) = H(c) = −16. -/
theorem table45_equal_harmony :
    harmonyScore table45C .b = harmonyScore table45C .c := by native_decide

/-- NHG noise variances differ: σ²_d(b−a) = 5 ≠ 3 = σ²_d(c−a).
    Equal-harmony candidates can have different NHG probabilities. -/
theorem table45_nhg_variance_differs :
    violationDiffSqSumQ table45C .a .b ≠ violationDiffSqSumQ table45C .a .c := by native_decide

/-- In MaxEnt, equal harmony implies equal probability: since
    `softmax(s, α, b) = exp(α·s(b)) / Σ exp(α·s(i))`, candidates with
    the same score get the same numerator and hence the same probability.

    This is the MaxEnt half of the §9 contrast: MaxEnt assigns
    P(b) = P(c) (both have H = −16), while NHG assigns P(b) ≠ P(c)
    because their noise variances differ (`table45_nhg_variance_differs`). -/
theorem table45_maxent_equal_prob :
    softmax (harmonyScoreR table45C) 1 Cand3.b =
    softmax (harmonyScoreR table45C) 1 Cand3.c := by
  simp only [softmax]
  have h : harmonyScoreR table45C Cand3.b = harmonyScoreR table45C Cand3.c := by
    simp only [harmonyScoreR]; exact_mod_cast table45_equal_harmony
  rw [h]

/-- NHG noise covariance value: `Cov(ε_b−ε_a, ε_c−ε_a) = 3σ²`.

    The paper (@cite{flemming-2021} §9, p. 37) computes `Cov(ε_a−ε_b, ε_c−ε_b) = 2σ²`
    using candidate b as reference. Our formalization uses candidate a as
    reference, giving 3σ² — a different but equally valid demonstration
    that the covariance matrix is non-diagonal. -/
theorem table45_nhg_covariance_value :
    nhgCovarianceQ table45C .a .b .c = 3 := by native_decide

/-- NHG noise covariance is non-zero: Cov(ε_b−ε_a, ε_c−ε_a) ≠ 0.
    The multivariate normal over score differences has a non-diagonal
    covariance matrix, so binary comparisons don't determine the joint
    distribution — NHG violates IIA (@cite{flemming-2021} §9). -/
theorem table45_nhg_covariance_nonzero :
    nhgCovarianceQ table45C .a .b .c ≠ 0 := by native_decide

-- ============================================================================
-- § 8: Square Instantiation — French Schwa × Separability
-- ============================================================================

-- The French schwa data forms two 2×2 squares (one per underlying form):
-- rows = onset type (C vs CC), columns = stress context (_σσ́ vs _σ́).
-- Each constraint is insensitive to at least one dimension, so the
-- violation differences satisfy `ViolDiffIndependence`, and
-- `me_predicts_hz` gives `ConstantLogitDiff` — Flemming's logit
-- uniformity prediction instantiated through Magri's framework.

/-- The /∅/ square: contexts 0–3 (underlying /∅/, varying onset × stress). -/
def schwaSquareNull : Square (Fin 8) := ⟨0, 1, 2, 3⟩

/-- The /ə/ square: contexts 4–7 (underlying /ə/, varying onset × stress). -/
def schwaSquareSchwa : Square (Fin 8) := ⟨4, 5, 6, 7⟩

/-- Violation differences satisfy independence on the /∅/ square:
    each of the 6 constraints is insensitive to either onset (row)
    or stress (column). -/
theorem schwaNull_independence :
    ViolDiffIndependence
      (fun (k : Fin 6) (ctx : Fin 8) => (schwaDiff ctx k : ℝ))
      schwaSquareNull := by
  have h : ∀ k : Fin 6,
      (schwaDiff schwaSquareNull.tl k = schwaDiff schwaSquareNull.bl k ∧
       schwaDiff schwaSquareNull.tr k = schwaDiff schwaSquareNull.br k) ∨
      (schwaDiff schwaSquareNull.tl k = schwaDiff schwaSquareNull.tr k ∧
       schwaDiff schwaSquareNull.bl k = schwaDiff schwaSquareNull.br k) := by native_decide
  intro k; dsimp only
  rcases h k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · exact Or.inr ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- Violation differences satisfy independence on the /ə/ square. -/
theorem schwaSchwa_independence :
    ViolDiffIndependence
      (fun (k : Fin 6) (ctx : Fin 8) => (schwaDiff ctx k : ℝ))
      schwaSquareSchwa := by
  have h : ∀ k : Fin 6,
      (schwaDiff schwaSquareSchwa.tl k = schwaDiff schwaSquareSchwa.bl k ∧
       schwaDiff schwaSquareSchwa.tr k = schwaDiff schwaSquareSchwa.br k) ∨
      (schwaDiff schwaSquareSchwa.tl k = schwaDiff schwaSquareSchwa.tr k ∧
       schwaDiff schwaSquareSchwa.bl k = schwaDiff schwaSquareSchwa.br k) := by native_decide
  intro k; dsimp only
  rcases h k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · exact Or.inr ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- **HZ's generalization for French schwa** (/∅/ square):
    for any MaxEnt weights, the logit-rate difference across onset
    types is constant across stress contexts. Derived from
    `me_predicts_hz` + `schwaNull_independence`. -/
theorem schwaNull_hz (w : Fin 6 → ℝ) :
    ConstantLogitDiff
      (fun ctx => ∑ k : Fin 6, w k * (schwaDiff ctx k : ℝ))
      schwaSquareNull :=
  me_predicts_hz w _ schwaSquareNull schwaNull_independence

/-- **HZ's generalization for French schwa** (/ə/ square). -/
theorem schwaSchwa_hz (w : Fin 6 → ℝ) :
    ConstantLogitDiff
      (fun ctx => ∑ k : Fin 6, w k * (schwaDiff ctx k : ℝ))
      schwaSquareSchwa :=
  me_predicts_hz w _ schwaSquareSchwa schwaSchwa_independence

-- ============================================================================
-- § 9: Generic ConstraintSystem View of Table (45)
-- ============================================================================

/-! Flemming's three-candidate table-(45) MaxEnt model is a
`ConstraintSystem Cand3 ℝ` decoded by `softmaxDecoder 1`. The key
observation `H(b) = H(c) ⟹ predict b = predict c` is a property of
*any* MaxEnt-style decoder: it depends only on the score equality and
the symmetry of softmax. By contrast NHG and Normal MaxEnt distinguish
b and c despite equal harmony (`table45_nhg_variance_differs`,
`table45_nhg_covariance_nonzero`) — same `score`, different `decoder`,
different `predict`. -/

/-- Flemming's table-(45) MaxEnt grammar as a generic
    `ConstraintSystem` over `Cand3`. -/
private noncomputable def flemmingSystem : ConstraintSystem Cand3 ℝ :=
  maxEntSystem Finset.univ table45C

/-- The MaxEnt system assigns equal probability to candidates b and c,
    matching `table45_maxent_equal_prob` but stated through the generic
    `predict` API. The frame here makes the framework distinction
    sharp: NHG (`argmax` after Gaussian noise on weights) and Normal
    MaxEnt (`argmax` after Gaussian noise on candidates) would assign
    different probabilities to b and c despite identical harmonies because
    they differ only in `decoder`, not in `score`. -/
theorem flemmingSystem_b_eq_c :
    flemmingSystem.predict Cand3.b = flemmingSystem.predict Cand3.c :=
  ConstraintSystem.predict_softmax_eq_of_score_eq _ rfl
    (Finset.mem_univ _) (Finset.mem_univ _)
    ((harmonyScoreR_eq_iff_harmonyScore_eq _ _ _).mpr table45_equal_harmony)

/-- The MaxEnt system on `Cand3` is a probability distribution. -/
theorem flemmingSystem_isProb :
    ∑ x : Cand3, flemmingSystem.predict x = 1 :=
  ConstraintSystem.predict_softmax_isProb _ rfl
    ⟨.a, Finset.mem_univ _⟩

end Flemming2021
