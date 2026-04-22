import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Phenomena.Politeness.Studies.YoonEtAl2020
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# @cite{yoon-etal-2020} on mathlib `PMF` (Phase 2 stress test, S1 submodel)
@cite{yoon-etal-2020}

Fifth stress test for the Phase-2 architecture. Yoon's politeness model
contributes one new ingredient: a **graded literal meaning** (real-valued
in [0, 1], not Boolean), driving the L0 layer through `RSA.L0OfMeaning`
rather than `RSA.L0OfBoolMeaning`. This is the first PMF migration to
exercise the ℝ≥0∞-valued meaning operator.

The S1 utility has a different shape from the previous four pilots:

  U_S1(u, s; φ) = φ · log L0(u, s) + (1−φ) · E_L0[V|u] − cost(u)

This decomposition (informativity weight · log + social weight · expected
value − cost) does **not** fit `RSA.softmaxBelief` (no expected-log over a
*belief*; the log is at the *true world*) and does **not** fit Kao's `rpow`
(it's exp ∘ linear, not power). It is the fifth distinct S1 shape across
five PMF migrations:

  | Paper            | S1 shape                           | Operator    |
  |------------------|------------------------------------|-------------|
  | FG2012           | uniform on extension (no rpow)     | L0OfBool    |
  | Kao2014          | (qudProj L0)^α                     | rpow only   |
  | GS2013           | exp(α · Σ_s belief · log L0)       | softmaxBel. |
  | ScontrasPearl21  | (qudProj L0)^α                     | rpow only   |
  | YoonEtAl2020     | exp(α · (φ·log + (1-φ)·E[V] - c))  | none — custom |

This data point is the strongest argument against extracting Yoon's S1 as
a sixth shared operator: every model has its own utility decomposition,
and they do not factor cleanly through a common abstraction beyond `PMF.normalize`
of an unnormalised score.

## PMF stack

* `worldPrior : PMF HeartState` — uniform on the four heart states
* `meaningE : Utterance → HeartState → ℝ≥0∞` — `ENNReal.ofReal` lift
  of `utteranceSemantics`
* `L0 : Utterance → PMF HeartState` — `RSA.L0OfMeaning` of `meaningE`
* `s1Score : Phi → HeartState → Utterance → ℝ≥0∞` — Yoon's utility,
  lifted via `ENNReal.ofReal` (because the social term mixes log and
  linear, which only make sense on `ℝ`)
* `S1g : Phi → HeartState → PMF Utterance` — `PMF.normalize` of `s1Score`
* `marginalSpeaker : HeartState → PMF Utterance` — `PMF.bind` over a
  `phiPrior : PMF Phi`
* `L1 : Utterance → PMF HeartState` — `PMF.posterior` of marginal speaker

## Coverage discharge

The `.terrible` utterance has positive meaning at every state under
**negation** (`1 - p w` is positive whenever `p w < 1`, and `terrible`'s
meaning is 0 at .h2 → `notTerrible .h2 = 1`). Combined with `Real.exp`
being strictly positive, this gives every L0 sum non-zero and every
S1g support non-empty.

## Scope

S1 submodel only (§2 of the original file). The S2 full model (§3) adds
a third utility term (`ω_pres · log L1(φ̂|u)`) and recomputes via
`combinedUtility` — its own migration target. The 8 S1 inference theorems
(`terrible_map_h0_vs_h3`, `bad_map_h1_vs_h0`, etc.) become L1
inequalities left as `sorry` pending the PMF-shaped `rsa_predict` tactic.

## Reused from `YoonEtAl2020.lean`

* `HeartState`, `Utterance`, `Adjective`, `Phi` — types
* `utteranceSemantics`, `subjectiveValue`, `utteranceCost`, `Phi.val`
* `meaning_bounded` — `0 ≤ utteranceSemantics u w ≤ 1`
-/

set_option autoImplicit false

namespace YoonEtAl2020.PMF

open scoped ENNReal
open YoonEtAl2020

/-! ## §1. World prior — uniform on `HeartState` -/

noncomputable def worldPrior : PMF HeartState := PMF.uniformOfFintype HeartState

theorem worldPrior_ne_zero (w : HeartState) : worldPrior w ≠ 0 :=
  (worldPrior.mem_support_iff w).mp (PMF.mem_support_uniformOfFintype w)

/-! ## §2. Lifted meaning function

The literal semantics is `ℚ`-valued (point-estimate acceptance proportions
from the norming task). Lifted to `ℝ≥0∞` via `ENNReal.ofReal` for
`PMF.normalize`. -/

noncomputable def meaningE (u : Utterance) (w : HeartState) : ℝ≥0∞ :=
  ENNReal.ofReal ((utteranceSemantics u w : ℚ) : ℝ)

theorem meaningE_ne_top (u : Utterance) (w : HeartState) : meaningE u w ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- Witness for the L0 normalisation positivity: every utterance has at least
one heart state where its meaning is non-zero. Concretely: `terrible` is true
at `.h0`, `bad` at `.h0`, `good`/`amazing` at `.h3`, and the negated forms get
their witness from a state where the base adjective is *false* (e.g.
`notTerrible` at `.h2` because `terrible .h2 = 0`). -/
def witnessState : Utterance → HeartState
  | .terrible    | .bad         => .h0
  | .good        | .amazing     => .h3
  | .notTerrible | .notBad      => .h2  -- (1 - 0) = 1
  | .notGood     | .notAmazing  => .h0  -- (1 - 1/49) ≈ 1

theorem meaningE_witness_ne_zero (u : Utterance) : meaningE u (witnessState u) ≠ 0 := by
  unfold meaningE
  rw [ENNReal.ofReal_ne_zero_iff]
  have h : (0 : ℚ) < utteranceSemantics u (witnessState u) := by
    cases u
    · change (0 : ℚ) < 1; norm_num     -- terrible at h0
    · change (0 : ℚ) < 1; norm_num     -- bad at h0
    · change (0 : ℚ) < 1; norm_num     -- good at h3
    · change (0 : ℚ) < 47/49; norm_num -- amazing at h3
    · change (0 : ℚ) < 1 - 0; norm_num -- notTerrible at h2 (= 1)
    · change (0 : ℚ) < 1 - 0; norm_num -- notBad at h2 (= 1)
    · change (0 : ℚ) < 1 - 1/49; norm_num -- notGood at h0 (= 48/49)
    · change (0 : ℚ) < 1 - 1/49; norm_num -- notAmazing at h0 (= 48/49)
  exact_mod_cast h

theorem meaningE_tsum_ne_zero (u : Utterance) : ∑' w, meaningE u w ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨witnessState u, meaningE_witness_ne_zero u⟩

theorem meaningE_tsum_ne_top (u : Utterance) : ∑' w, meaningE u w ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype fun w => meaningE_ne_top u w

/-! ## §3. L0 — literal listener via `RSA.L0OfMeaning`

The graded soft-semantic version of L0: mass proportional to acceptance
probability, normalised over heart states. This is the FIRST PMF migration
to exercise `L0OfMeaning` (the ℝ≥0∞ variant); the previous four all used
`L0OfBoolMeaning` because their meanings happened to be 0/1. -/

noncomputable def L0 (u : Utterance) : PMF HeartState :=
  RSA.L0OfMeaning meaningE u (meaningE_tsum_ne_zero u) (meaningE_tsum_ne_top u)

@[simp] theorem L0_apply (u : Utterance) (w : HeartState) :
    L0 u w = meaningE u w * (∑' w', meaningE u w')⁻¹ :=
  RSA.L0OfMeaning_apply _ _ _ _ _

theorem L0_eq_zero_iff (u : Utterance) (w : HeartState) :
    L0 u w = 0 ↔ meaningE u w = 0 := by
  rw [L0_apply]
  rw [mul_eq_zero]
  refine ⟨fun h => h.elim id (fun hi => ?_), fun h => Or.inl h⟩
  exact absurd hi (ENNReal.inv_ne_zero.mpr (meaningE_tsum_ne_top u))

theorem L0_witness_ne_zero (u : Utterance) : L0 u (witnessState u) ≠ 0 :=
  fun h => meaningE_witness_ne_zero u ((L0_eq_zero_iff _ _).mp h)

/-! ## §4. S1 score — Yoon's custom utility decomposition

  s1Score φ w u = if L0(u, w) = 0 ∧ φ ≠ p0 then 0
                  else exp(α · (φ.val · log L0(u,w)
                                + (1-φ.val) · E_L0[V|u]
                                - cost(u)))

where E_L0[V|u] = Σ_w' L0(u, w') · V(w'). The φ=0 gate keeps utterances
with zero literal mass viable for the pure-social speaker (whose log
weight is 0, making `0 · log 0 = 0` non-issues).

Real-valued internally, lifted to `ℝ≥0∞` at the `PMF.normalize` boundary.
The score is positive iff `L0(u, w) ≠ 0 ∨ φ = p0` — the cover witness
shape needed for the `PMF.normalize` precondition. -/

/-- `α = 3` matches the S1 submodel's value (paper uses BDA-fitted ≈4.47). -/
noncomputable def alpha : ℝ := 3

theorem alpha_pos : 0 < alpha := by unfold alpha; norm_num

/-- Real projection of L0 (drops the ENNReal wrapping). -/
noncomputable def L0Real (u : Utterance) (w : HeartState) : ℝ :=
  (L0 u w).toReal

theorem L0Real_nonneg (u : Utterance) (w : HeartState) : 0 ≤ L0Real u w :=
  ENNReal.toReal_nonneg

/-- Expected subjective value under the literal listener. -/
noncomputable def expectedValue (u : Utterance) : ℝ :=
  ∑ w' : HeartState, L0Real u w' * ((subjectiveValue w' : ℚ) : ℝ)

/-- Yoon's S1 utility (the argument of `exp`). -/
noncomputable def s1Utility (φ : Phi) (w : HeartState) (u : Utterance) : ℝ :=
  alpha * ((φ.val : ℝ) * Real.log (L0Real u w) +
           (1 - (φ.val : ℝ)) * expectedValue u +
           -((utteranceCost u : ℕ) : ℝ))

/-- The unnormalised speaker score, with the φ=0 gate. -/
noncomputable def s1Score (φ : Phi) (w : HeartState) (u : Utterance) : ℝ≥0∞ :=
  if L0Real u w = 0 ∧ φ ≠ .p0 then 0
  else ENNReal.ofReal (Real.exp (s1Utility φ w u))

theorem s1Score_ne_top (φ : Phi) (w : HeartState) (u : Utterance) :
    s1Score φ w u ≠ ∞ := by
  unfold s1Score; split <;> simp [ENNReal.ofReal_ne_top]

theorem s1Score_tsum_ne_top (φ : Phi) (w : HeartState) :
    ∑' u, s1Score φ w u ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype fun u => s1Score_ne_top φ w u

/-! ### Cover discharge

For each `(φ, w)`, we need a witness utterance `u` with `s1Score φ w u ≠ 0`.

The simplest cover: pick `u` such that `L0Real u w ≠ 0`. Then the φ-gate
is bypassed and the score is `exp(...) > 0`.

For each heart state, *some* utterance has positive L0 mass (verified by
inspection: e.g. `terrible` at .h0, `bad` at .h0, `good` at .h2, `amazing`
at .h3). We package this as a per-state witness function. -/

def coverUtterance : HeartState → Utterance
  | .h0 => .terrible
  | .h1 => .bad
  | .h2 => .good
  | .h3 => .amazing

theorem meaningE_coverUtterance_ne_zero (w : HeartState) :
    meaningE (coverUtterance w) w ≠ 0 := by
  unfold meaningE
  rw [ENNReal.ofReal_ne_zero_iff]
  have h : (0 : ℚ) < utteranceSemantics (coverUtterance w) w := by
    cases w
    · change (0 : ℚ) < 1; norm_num     -- terrible at h0
    · change (0 : ℚ) < 45/49; norm_num -- bad at h1
    · change (0 : ℚ) < 47/49; norm_num -- good at h2
    · change (0 : ℚ) < 47/49; norm_num -- amazing at h3
  exact_mod_cast h

theorem L0_coverUtterance_ne_zero (w : HeartState) :
    L0 (coverUtterance w) w ≠ 0 := fun h =>
  meaningE_coverUtterance_ne_zero w ((L0_eq_zero_iff _ _).mp h)

theorem L0Real_coverUtterance_ne_zero (w : HeartState) :
    L0Real (coverUtterance w) w ≠ 0 := by
  unfold L0Real
  rw [ENNReal.toReal_ne_zero]
  exact ⟨L0_coverUtterance_ne_zero w, PMF.apply_ne_top _ _⟩

theorem s1Score_coverUtterance_ne_zero (φ : Phi) (w : HeartState) :
    s1Score φ w (coverUtterance w) ≠ 0 := by
  unfold s1Score
  rw [if_neg]
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  · push_neg
    intro h
    exact absurd h (L0Real_coverUtterance_ne_zero w)

theorem s1Score_tsum_ne_zero (φ : Phi) (w : HeartState) :
    ∑' u, s1Score φ w u ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr
    ⟨coverUtterance w, s1Score_coverUtterance_ne_zero φ w⟩

/-! ### Per-utterance witness (for the L1 marginal direction)

Dual to `coverUtterance`: for each utterance `u`, `witnessState u` is a heart
state where `L0(u)` has positive mass, giving `s1Score φ (witnessState u) u ≠ 0`
for any `φ`. Used to discharge `L1_marginal_ne_zero`. -/

theorem L0Real_witness_ne_zero (u : Utterance) : L0Real u (witnessState u) ≠ 0 := by
  unfold L0Real
  rw [ENNReal.toReal_ne_zero]
  exact ⟨L0_witness_ne_zero u, PMF.apply_ne_top _ _⟩

theorem s1Score_witness_ne_zero (φ : Phi) (u : Utterance) :
    s1Score φ (witnessState u) u ≠ 0 := by
  unfold s1Score
  rw [if_neg]
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  · push_neg
    intro h
    exact absurd h (L0Real_witness_ne_zero u)

/-! ## §5. S1g — speaker conditional on (φ, world) -/

noncomputable def S1g (φ : Phi) (w : HeartState) : PMF Utterance :=
  PMF.normalize (s1Score φ w) (s1Score_tsum_ne_zero φ w) (s1Score_tsum_ne_top φ w)

theorem mem_support_S1g_iff (φ : Phi) (w : HeartState) (u : Utterance) :
    u ∈ (S1g φ w).support ↔ s1Score φ w u ≠ 0 := by
  rw [S1g, PMF.mem_support_normalize_iff]

theorem S1g_coverUtterance_ne_zero (φ : Phi) (w : HeartState) :
    S1g φ w (coverUtterance w) ≠ 0 := by
  rw [← PMF.mem_support_iff, mem_support_S1g_iff]
  exact s1Score_coverUtterance_ne_zero φ w

/-! ## §6. Marginal speaker — `PMF.bind` over a kindness prior

The speaker marginalises over their (latent) kindness weight. -/

noncomputable def marginalSpeaker (phiPrior : PMF Phi) (w : HeartState) : PMF Utterance :=
  phiPrior.bind (fun φ => S1g φ w)

theorem marginalSpeaker_coverUtterance_ne_zero {phiPrior : PMF Phi}
    {φ : Phi} (hφ : phiPrior φ ≠ 0) (w : HeartState) :
    marginalSpeaker phiPrior w (coverUtterance w) ≠ 0 := by
  unfold marginalSpeaker
  rw [PMF.bind_apply]
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨φ, mul_ne_zero hφ ?_⟩
  exact S1g_coverUtterance_ne_zero φ w

/-! ## §7. L1 — Bayesian inversion via `PMF.posterior` -/

theorem L1_marginal_ne_zero {phiPrior : PMF Phi} {φ : Phi} (hφ : phiPrior φ ≠ 0)
    (u : Utterance) :
    PMF.marginal (marginalSpeaker phiPrior) worldPrior u ≠ 0 := by
  refine PMF.marginal_ne_zero _ worldPrior u
    (worldPrior_ne_zero (witnessState u)) ?_
  unfold marginalSpeaker
  rw [PMF.bind_apply]
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨φ, mul_ne_zero hφ ?_⟩
  rw [← PMF.mem_support_iff, mem_support_S1g_iff]
  exact s1Score_witness_ne_zero φ u

/-- Pragmatic listener: `PMF.posterior` of the φ-marginalised speaker
against the world prior. The "L1 = Bayesian inversion" claim is true by
construction. -/
noncomputable def L1 {phiPrior : PMF Phi} {φ : Phi} (hφ : phiPrior φ ≠ 0)
    (u : Utterance) : PMF HeartState :=
  PMF.posterior (marginalSpeaker phiPrior) worldPrior u (L1_marginal_ne_zero hφ u)

end YoonEtAl2020.PMF
