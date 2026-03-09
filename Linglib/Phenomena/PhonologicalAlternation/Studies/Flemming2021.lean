import Linglib.Theories.Phonology.HarmonicGrammar.NoisyHG
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

namespace Phenomena.PhonologicalAlternation.Studies.Flemming2021

open Theories.Phonology.HarmonicGrammar Core Real

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
  simp [one_div]

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
    leaving only −w₂ · 1 = −w₂. -/
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
  fin_cases pair <;> simp_all [clashPairs, schwaDiff, Fin.sum_univ_six] <;> ring

-- ============================================================================
-- § 5: NHG Probit Non-Uniformity
-- ============================================================================

/-- Sum of squared violation differences for a context. -/
def schwaSqSum (ctx : Fin 8) : Nat :=
  (List.finRange 6).foldl (fun acc j => acc + (schwaDiff ctx j).natAbs ^ 2) 0

/-- NHG noise variance σ_d² is context-dependent: without \*Clash,
    the squared violation sum is 3; with \*Clash, it is 4.
    The same \*Clash violation change produces different σ_d values
    in different tableaux. -/
theorem nhg_sigmaD_sq_varies :
    schwaSqSum 0 = 3 ∧ schwaSqSum 1 = 4 ∧
    schwaSqSum 2 = 3 ∧ schwaSqSum 3 = 4 ∧
    schwaSqSum 4 = 3 ∧ schwaSqSum 5 = 4 ∧
    schwaSqSum 6 = 3 ∧ schwaSqSum 7 = 4 := by native_decide

-- The NHG probit for a context is (h_ə − h_∅) / σ_d. Adding a *Clash
-- violation changes BOTH the harmony difference (numerator) and σ_d
-- (denominator), so the probit change depends on the initial harmony
-- difference h_ə − h_∅ — which varies across contexts.
--
-- Concretely (Flemming §7.2 with σ = 1):
-- Pair (0,1): σ_d changes √3 → 2, Δh changes by −w_Clash
--   probit change = (Δh − w_Clash)/2 − Δh/√3
-- Pair (4,5): σ_d changes √3 → 2, Δh changes by −w_Clash
--   probit change = (Δh' − w_Clash)/2 − Δh'/√3
-- where Δh ≠ Δh' (different initial harmony differences), so
-- the probit changes differ despite the same *Clash change.

end Phenomena.PhonologicalAlternation.Studies.Flemming2021
