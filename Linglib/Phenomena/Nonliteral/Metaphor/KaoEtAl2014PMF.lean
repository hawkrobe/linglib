import Linglib.Core.Probability.Softmax
import Linglib.Core.Probability.Posterior
import Linglib.Core.Probability.JointPosterior
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# @cite{kao-etal-2014-metaphor} on mathlib `PMF`
@cite{kao-etal-2014-metaphor}

"Formalizing the Pragmatics of Metaphor Understanding"
*Proceedings of the Annual Meeting of the Cognitive Science Society* 36, 719-724.

## Model (verified against paper)

- L0 (Eq. before 1): `L0(c, f⃗ | u) = P(f⃗|c) if c = u, else 0`
- Speaker utility (Eq. 1): `U(u | g, f⃗) = log Σ_{c, f⃗' : g(f⃗') = g(f⃗)} L0(c, f⃗' | u)`
- Speaker (Eq. 2): `S1(u | g, f⃗) ∝ exp(λ · U(u | g, f⃗))`
- Pragmatic listener: `L1(c, f⃗ | u) ∝ P(c) · P(f⃗|c) · Σ_g P(g) · S1(u | g, f⃗)`

Parameters (paper §"Model Evaluation"):
- λ = 3 (speaker rationality)
- P(whale) = 0.01, P(person) = 0.99 (category prior)
- Vague QUD: uniform P(g) = 1/3
- Specific QUD (`f₁`): P(g₁) = 0.6, P(g₂) = P(g₃) = 0.2

## Softmax-of-log at the root, not rpow workaround

The speaker utility `U = log Σ L0` returns `-∞` when the QUD-projected L0
marginal is 0. Mathlib's `Real.log 0 = 0` would silently break this —
`exp(λ · 0) = 1` would give nonzero weight to impossible utterances.

The substrate fix: `PMF.softmax` takes `score : α → EReal`, with
`EReal.exp(⊥) = 0` correctly handling impossible utterances. The Kao S1
is then `PMF.softmax (fun u => (α : EReal) * ENNReal.log (qudProjL0 g u f⃗))`
— directly the paper's formula with no rpow workaround. Mathematically
equivalent to `(qudProjL0)^λ` (via `ENNReal.rpow_eq_exp_mul_log`) when
`qudProjL0 > 0`, but the EReal form makes the boundary case explicit.

For Kao's empirical priors (Experiment 1b), all `featurePriorℕ` entries
are strictly positive (min = 379), so all QUD-marginals are positive and
the boundary doesn't bite numerically. The substrate handles the general
case correctly anyway — RSA papers with sparser literal-listener support
inherit the right behaviour.

## Joint posterior over `(World × Goal)`

Kao's L1 jointly infers the speaker's category-and-features and
marginalises over goal. PMF-natively: posterior of `World × Goal`
projected to the `World`-marginal — exactly `PMF.posterior_fst_apply`
from `Core/Probability/JointPosterior.lean`.

This file uses the equivalent kernel-form: `World → PMF Cat` defined as
`goalPrior.bind ∘ s1`, folding the goal-marginalisation into the kernel.
The two formulations agree by associativity of `bind`.
-/

set_option autoImplicit false

namespace Phenomena.Nonliteral.Metaphor.KaoEtAl2014.PMF

open scoped ENNReal

/-! ## §0. Domain types -/

/-- Categories: whale (metaphor vehicle) and person (literal referent).
    Categories double as utterance types. -/
inductive Cat where
  | whale | person
  deriving DecidableEq, Repr

instance : Fintype Cat where
  elems := {.whale, .person}
  complete := fun x => by cases x <;> simp

instance : Nonempty Cat := ⟨.whale⟩

/-- QUDs: which feature is the speaker trying to communicate? -/
inductive Goal where
  | large | graceful | majestic
  deriving DecidableEq, Repr

instance : Fintype Goal where
  elems := {.large, .graceful, .majestic}
  complete := fun x => by cases x <;> simp

instance : Nonempty Goal := ⟨.large⟩

/-- Feature vector: 3 booleans (e.g. {large, graceful, majestic} for whale). -/
abbrev Features := Bool × Bool × Bool

/-- World = (category, feature vector). 2 × 8 = 16 worlds. -/
abbrev World := Cat × Features

instance : Nonempty World := ⟨(.whale, (true, true, true))⟩

/-! ## §1. Empirical priors (Experiment 1b counts ×10000) -/

/-- Feature prior `P(f⃗ | c)` as integer counts (×10000). Both per-category
sums = 10000 by construction. -/
def featurePriorℕ : Cat → Features → ℕ
  -- whale: large/graceful/majestic biased
  | .whale,  (true,  true,  true)  => 3059
  | .whale,  (true,  true,  false) => 1381
  | .whale,  (true,  false, true)  => 1791
  | .whale,  (true,  false, false) => 1310
  | .whale,  (false, true,  true)  => 947
  | .whale,  (false, true,  false) => 531
  | .whale,  (false, false, true)  => 602
  | .whale,  (false, false, false) => 379
  -- person: roughly uniform across feature vectors
  | .person, (true,  true,  true)  => 1169
  | .person, (true,  true,  false) => 1058
  | .person, (true,  false, true)  => 1157
  | .person, (true,  false, false) => 1308
  | .person, (false, true,  true)  => 1529
  | .person, (false, true,  false) => 1281
  | .person, (false, false, true)  => 1147
  | .person, (false, false, false) => 1351

/-- Category prior `P(c)` as integer counts: 1% whale, 99% person. -/
def catPriorℕ : Cat → ℕ
  | .whale => 1
  | .person => 99

theorem featurePriorℕ_sum_whale :
    (∑ f, featurePriorℕ .whale f) = 10000 := by decide

theorem featurePriorℕ_sum_person :
    (∑ f, featurePriorℕ .person f) = 10000 := by decide

theorem catPriorℕ_sum : (∑ c, catPriorℕ c) = 100 := by decide

/-- Every entry of the feature prior is strictly positive. The witness that
drives every positivity proof in the file. -/
theorem featurePriorℕ_pos (c : Cat) (f : Features) : 0 < featurePriorℕ c f := by
  obtain ⟨a, b, d⟩ := f
  cases c <;> cases a <;> cases b <;> cases d <;>
    (unfold featurePriorℕ; norm_num)

/-! ## §2. PMF construction -/

/-- Feature prior as a PMF over `Features`, parametric in category. -/
noncomputable def featurePmf (c : Cat) : PMF Features :=
  PMF.ofFintype (fun f => (featurePriorℕ c f : ℝ≥0∞) / 10000)
    (by
      have h_div : ∀ f, ((featurePriorℕ c f : ℝ≥0∞) / 10000)
              = (featurePriorℕ c f : ℝ≥0∞) * (10000 : ℝ≥0∞)⁻¹ := fun f =>
        ENNReal.div_eq_inv_mul.trans (mul_comm _ _)
      simp_rw [h_div]
      rw [← Finset.sum_mul]
      cases c
      · rw [show (∑ f, ((featurePriorℕ .whale f : ℕ) : ℝ≥0∞))
              = ((10000 : ℕ) : ℝ≥0∞) from by
              rw [← Nat.cast_sum]; exact_mod_cast featurePriorℕ_sum_whale]
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      · rw [show (∑ f, ((featurePriorℕ .person f : ℕ) : ℝ≥0∞))
              = ((10000 : ℕ) : ℝ≥0∞) from by
              rw [← Nat.cast_sum]; exact_mod_cast featurePriorℕ_sum_person]
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

theorem featurePmf_apply (c : Cat) (f : Features) :
    featurePmf c f = (featurePriorℕ c f : ℝ≥0∞) / 10000 := rfl

theorem featurePmf_pos (c : Cat) (f : Features) : 0 < featurePmf c f := by
  rw [featurePmf_apply]
  refine ENNReal.div_pos ?_ (by norm_num)
  exact_mod_cast (featurePriorℕ_pos c f).ne'

/-- Category prior as a PMF over `Cat`. -/
noncomputable def catPmf : PMF Cat :=
  PMF.ofFintype (fun c => (catPriorℕ c : ℝ≥0∞) / 100)
    (by
      have h_div : ∀ c, ((catPriorℕ c : ℝ≥0∞) / 100)
              = (catPriorℕ c : ℝ≥0∞) * (100 : ℝ≥0∞)⁻¹ := fun c =>
        ENNReal.div_eq_inv_mul.trans (mul_comm _ _)
      simp_rw [h_div]
      rw [← Finset.sum_mul]
      rw [show (∑ c, ((catPriorℕ c : ℕ) : ℝ≥0∞)) = ((100 : ℕ) : ℝ≥0∞) from by
            rw [← Nat.cast_sum]; exact_mod_cast catPriorℕ_sum]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

theorem catPmf_apply (c : Cat) : catPmf c = (catPriorℕ c : ℝ≥0∞) / 100 := rfl

/-- Joint world prior `P(c, f⃗) = P(c) · P(f⃗|c)`. -/
noncomputable def worldPmf : PMF World :=
  catPmf.bind (fun c => (featurePmf c).map (fun f => (c, f)))

/-! ## §3. Literal listener L0

`L0(c, f⃗ | u) = P(f⃗|c) if c = u, else 0`. PMF-form: deterministic embedding
of `featurePmf u` into worlds with category `u`. -/

/-- Literal listener: PMF over `World` concentrated on `c = u`. -/
noncomputable def L0 (u : Cat) : PMF World :=
  (featurePmf u).map (fun f => (u, f))

/-! ## §4. QUD projection -/

/-- Project a feature vector onto the QUD-relevant component. -/
def projectFeature : Goal → Features → Bool
  | .large,    (l, _, _) => l
  | .graceful, (_, g, _) => g
  | .majestic, (_, _, m) => m

/-- The QUD-projected L0 marginal at `(g, u, f⃗)`: outer-measure of the
QUD equivalence class containing `f⃗` under `featurePmf u`. -/
noncomputable def qudProjL0 (g : Goal) (u : Cat) (f : Features) : ℝ≥0∞ :=
  (featurePmf u).toOuterMeasure {f' | projectFeature g f' = projectFeature g f}

theorem qudProjL0_le_one (g : Goal) (u : Cat) (f : Features) :
    qudProjL0 g u f ≤ 1 :=
  PMF.toOuterMeasure_apply_le_one _ _

theorem qudProjL0_ne_top (g : Goal) (u : Cat) (f : Features) :
    qudProjL0 g u f ≠ ∞ :=
  (lt_of_le_of_lt (qudProjL0_le_one g u f) ENNReal.one_lt_top).ne

/-- The QUD-projected L0 marginal at `(g, u, f⃗)` is bounded below by
`featurePmf u f⃗` (since `f⃗` is in its own equivalence class). -/
theorem qudProjL0_ge_apply (g : Goal) (u : Cat) (f : Features) :
    featurePmf u f ≤ qudProjL0 g u f := by
  unfold qudProjL0
  -- f ∈ {f' | projectFeature g f' = projectFeature g f}, and the singleton
  -- {f}'s outer measure equals featurePmf u f.
  rw [show featurePmf u f
        = (featurePmf u).toOuterMeasure {f} from
        (PMF.toOuterMeasure_apply_singleton _ _).symm]
  exact MeasureTheory.OuterMeasure.mono _
    (Set.singleton_subset_iff.mpr (rfl : projectFeature g f = projectFeature g f))

theorem qudProjL0_pos (g : Goal) (u : Cat) (f : Features) : 0 < qudProjL0 g u f :=
  lt_of_lt_of_le (featurePmf_pos u f) (qudProjL0_ge_apply g u f)

theorem qudProjL0_ne_zero (g : Goal) (u : Cat) (f : Features) :
    qudProjL0 g u f ≠ 0 :=
  (qudProjL0_pos g u f).ne'

/-! ## §5. Speaker S1 (softmax of log-utility, Eq. 1-2)

Score `s1Score α g f u = (α : EReal) * ENNReal.log (qudProjL0 g u f)`.
EReal-valued: `-∞` when `qudProjL0 = 0`, finite otherwise. The softmax
substrate `PMF.softmax` correctly handles `-∞` (gives 0 mass).

For Kao's data, `qudProjL0 > 0` always, so the score is always finite —
the substrate's `-∞` handling isn't load-bearing here, but is the right
default for the general RSA pattern. -/

/-- Speaker score `s1Score α g f u = λ · log(qudProjL0 g u f) : EReal`. -/
noncomputable def s1Score (α : ℝ) (g : Goal) (f : Features) (u : Cat) : EReal :=
  (α : EReal) * ENNReal.log (qudProjL0 g u f)

/-- The score is never `+∞`: `qudProjL0 ≤ 1` so `log ≤ 0`, and we'll
restrict to `λ ≥ 0` so the product `≤ 0 < +∞`. -/
theorem s1Score_ne_top (α : ℝ) (hα : 0 ≤ α) (g : Goal) (f : Features) (u : Cat) :
    s1Score α g f u ≠ ⊤ := by
  unfold s1Score
  rcases eq_or_lt_of_le hα with rfl | hα_pos
  · -- λ = 0
    simp [EReal.coe_zero, zero_mul]
  · -- λ > 0: λ · log(qudProjL0) ≠ ⊤ since log ≠ ⊤ (as qudProjL0 ≠ ⊤)
    intro h
    -- (α : EReal) > 0 and product = ⊤ implies log = ⊤
    have h_log_top : ENNReal.log (qudProjL0 g u f) = ⊤ := by
      by_contra h_log_ne_top
      -- finite λ * finite log = finite
      apply h_log_ne_top
      -- if λ > 0 and λ · log = ⊤, then log = ⊤
      sorry  -- TODO: positive coercion times finite = finite
    rw [ENNReal.log_eq_top_iff] at h_log_top
    exact qudProjL0_ne_top g u f h_log_top

/-- For Kao's parameters, `qudProjL0 > 0` so `log > ⊥`, and `λ ≥ 0` keeps
the score finite-below. -/
theorem s1Score_ne_bot (α : ℝ) (hα : 0 ≤ α) (g : Goal) (f : Features) (u : Cat) :
    s1Score α g f u ≠ ⊥ := by
  unfold s1Score
  rcases eq_or_lt_of_le hα with rfl | hα_pos
  · -- λ = 0
    simp [EReal.coe_zero, zero_mul]
  · -- λ > 0: λ · log(qudProjL0) ≠ ⊥ since log ≠ ⊥ (as qudProjL0 ≠ 0)
    intro h
    have h_log_bot : ENNReal.log (qudProjL0 g u f) = ⊥ := by
      by_contra h_log_ne_bot
      sorry  -- TODO: positive coercion times finite-below = finite-below
    rw [ENNReal.log_eq_bot_iff] at h_log_bot
    exact qudProjL0_ne_zero g u f h_log_bot

/-- **Speaker S1**: softmax of QUD-projected log-utility (Eq. 1-2). -/
noncomputable def s1 (α : ℝ) (hα : 0 ≤ α) (g : Goal) (f : Features) : PMF Cat :=
  PMF.softmax (s1Score α g f)
    (fun u => s1Score_ne_top α hα g f u)
    ⟨.whale, s1Score_ne_bot α hα g f .whale⟩

/-! ## §6. Goal-marginalised speaker -/

/-- **Goal-marginalised speaker**: `Σ_g P(g) · S1(· | g, f⃗)`. -/
noncomputable def mixedS1 (α : ℝ) (hα : 0 ≤ α) (goalPrior : PMF Goal)
    (f : Features) : PMF Cat :=
  goalPrior.bind (fun g => s1 α hα g f)

/-! ## §7. Pragmatic listener L1

`L1(c, f⃗ | u) ∝ worldPmf(c, f⃗) · mixedS1(u | f⃗)`.

PMF: posterior of the kernel `(c, f⃗) ↦ mixedS1(· | f⃗)` against `worldPmf`. -/

/-- The kernel for L1: `(c, f⃗) ↦ mixedS1(· | f⃗)`. Independent of `c`. -/
noncomputable def L1Kernel (α : ℝ) (hα : 0 ≤ α) (goalPrior : PMF Goal) :
    World → PMF Cat :=
  fun w => mixedS1 α hα goalPrior w.2

/-- L1 marginal at `u` is non-zero — needed for `posterior` discharge. -/
theorem L1Kernel_marginal_ne_zero (α : ℝ) (hα : 0 ≤ α) (goalPrior : PMF Goal)
    {g : Goal} (hg : goalPrior g ≠ 0) (u : Cat) :
    PMF.marginal (L1Kernel α hα goalPrior) worldPmf u ≠ 0 := by
  sorry  -- TODO: pick witness world (u, (true, true, true)); both prior > 0 and
         -- kernel(u | (u, ...)) > 0 since softmax has full support and goal g has prior > 0.

/-- **Pragmatic listener L1**: posterior over `World` given utterance `u`. -/
noncomputable def L1 (α : ℝ) (hα : 0 ≤ α) (goalPrior : PMF Goal)
    {g : Goal} (hg : goalPrior g ≠ 0) (u : Cat) : PMF World :=
  PMF.posterior (L1Kernel α hα goalPrior) worldPmf u
    (L1Kernel_marginal_ne_zero α hα goalPrior hg u)

/-! ## §8. Standard goal priors -/

/-- Vague QUD: uniform goal prior ("What is he like?"). -/
noncomputable def vaguePrior : PMF Goal := PMF.uniformOfFintype Goal

theorem vaguePrior_pos (g : Goal) : vaguePrior g ≠ 0 := by
  rw [vaguePrior, PMF.uniformOfFintype_apply]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-- Specific QUD targeting `f₁` ("Is he `f₁`?"): P(g₁) = 0.6, P(g₂) = P(g₃) = 0.2. -/
noncomputable def specificF1Prior : PMF Goal :=
  PMF.ofFintype
    (fun g => match g with
      | .large => (6 : ℝ≥0∞) / 10
      | .graceful => (2 : ℝ≥0∞) / 10
      | .majestic => (2 : ℝ≥0∞) / 10)
    (by
      rw [show (Finset.univ : Finset Goal)
            = {.large, .graceful, .majestic} from rfl]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_singleton]
      rw [show (6 : ℝ≥0∞) / 10 + ((2 : ℝ≥0∞) / 10 + (2 : ℝ≥0∞) / 10) = 1 from by
        rw [show ((2 : ℝ≥0∞) / 10 + (2 : ℝ≥0∞) / 10) = 4 / 10 from by
              rw [ENNReal.div_add_div_same]; norm_num,
            show ((6 : ℝ≥0∞) / 10 + 4 / 10) = 10 / 10 from by
              rw [ENNReal.div_add_div_same]; norm_num]
        exact ENNReal.div_self (by norm_num) (by norm_num)])

theorem specificF1Prior_large_pos : specificF1Prior .large ≠ 0 := by
  unfold specificF1Prior PMF.ofFintype
  simp [ne_eq]

/-! ## §9. Empirical findings (paper §"Model Evaluation")

Each finding stated as an outer-measure inequality on the L1 posterior.

Speaker rationality λ = 3 (paper §"Model Evaluation"). -/

/-- Speaker rationality (paper §"Model Evaluation"). -/
def αKao : ℝ := 3

theorem αKao_pos : 0 < αKao := by unfold αKao; norm_num
theorem αKao_nonneg : 0 ≤ αKao := le_of_lt αKao_pos

/-- L1 with vague QUD (the most common condition in §"Model Evaluation"). -/
noncomputable abbrev vagueL1 (u : Cat) : PMF World :=
  L1 αKao αKao_nonneg vaguePrior (vaguePrior_pos .large) u

/-- L1 with specific-`f₁` QUD. -/
noncomputable abbrev specificL1 (u : Cat) : PMF World :=
  L1 αKao αKao_nonneg specificF1Prior specificF1Prior_large_pos u

/-- **Finding 1 (Nonliteral interpretation)**: hearing "whale", listener
infers `person`, not literally `whale`. Paper: P(c_p|u_whale) = 0.994. -/
theorem nonliteral :
    (vagueL1 .whale).toOuterMeasure {w | w.1 = .person} >
    (vagueL1 .whale).toOuterMeasure {w | w.1 = .whale} := by
  sorry  -- 99x catPrior dominates speaker's whale-preference.

/-- **Finding 2 (Feature elevation: large)**: P(large=T | "whale") > P(large=F | "whale"). -/
theorem feature_large :
    (vagueL1 .whale).toOuterMeasure {w | w.2.1 = true} >
    (vagueL1 .whale).toOuterMeasure {w | w.2.1 = false} := by
  sorry  -- featurePriorℕ shows large=T mass dominant for whales (3059+1381+1791+1310 = 7541 vs 947+531+602+379 = 2459).

/-- **Finding 3 (Feature elevation: graceful)**. -/
theorem feature_graceful :
    (vagueL1 .whale).toOuterMeasure {w | w.2.2.1 = true} >
    (vagueL1 .whale).toOuterMeasure {w | w.2.2.1 = false} := by
  sorry

/-- **Finding 4 (Feature elevation: majestic)**. -/
theorem feature_majestic :
    (vagueL1 .whale).toOuterMeasure {w | w.2.2.2 = true} >
    (vagueL1 .whale).toOuterMeasure {w | w.2.2.2 = false} := by
  sorry

/-- **Finding 5 (Context sensitivity)**: specific QUD raises P(large=T)
above the vague-QUD value. Cross-config comparison. -/
theorem context_sensitivity :
    (specificL1 .whale).toOuterMeasure {w | w.2.1 = true} >
    (vagueL1 .whale).toOuterMeasure {w | w.2.1 = true} := by
  sorry  -- specific goal sharpens speaker's preference along f₁.

/-- **Finding 6 (Literal correctness)**: hearing "person", listener
correctly infers `person`. -/
theorem literal_correct :
    (vagueL1 .person).toOuterMeasure {w | w.1 = .person} >
    (vagueL1 .person).toOuterMeasure {w | w.1 = .whale} := by
  sorry  -- both prior AND speaker preferences agree on .person.

/-! ## §10. Cross-paper engagement

@cite{frank-goodman-2012} is the architectural ancestor — basic L0/S1/L1
without QUD inference. Kao's contribution is the joint inference over
goals, opening the door to nonliteral interpretations.

@cite{goodman-stuhlmuller-2013} (`Phenomena/ScalarImplicatures/Studies/GoodmanStuhlmuller2013PMF.lean`)
shares the hypergeometric-kernel architecture with Kao's L0 (both use
"P(features|category) if categories match"). The architectural difference:
G&S2013 is one-step Bayesian (no goal inference); Kao's L1 is two-stage
(joint goal-inference enables metaphorical readings).

@cite{kao-etal-2014-hyperbole} (sister paper, same conference) uses the
identical RSA architecture for hyperbole (with `quantity` rather than
`category` as the literally-false dimension). Migration of the hyperbole
file would reuse most of this file's substrate.
-/

end Phenomena.Nonliteral.Metaphor.KaoEtAl2014.PMF
