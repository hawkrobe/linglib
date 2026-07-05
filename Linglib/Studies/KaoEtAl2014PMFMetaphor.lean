import Linglib.Core.Probability.Softmax
import Linglib.Core.Probability.Posterior
import Linglib.Core.Probability.JointPosterior
import Linglib.Pragmatics.RSA.QUD
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# [kao-etal-2014-metaphor] on mathlib `PMF`
[kao-etal-2014-metaphor]

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

namespace KaoEtAl2014PMFMetaphor

open scoped ENNReal

/-! ## §0. Domain types -/

/-- Categories: whale (metaphor vehicle) and person (literal referent).
    Categories double as utterance types. -/
inductive Cat where
  | whale | person
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Cat := ⟨.whale⟩

/-- QUDs: which feature is the speaker trying to communicate? -/
inductive Goal where
  | large | graceful | majestic
  deriving DecidableEq, Repr, Fintype

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
  cases c <;> cases a <;> cases b <;> cases d <;> decide

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

theorem catPriorℕ_pos (c : Cat) : 0 < catPriorℕ c := by cases c <;> decide

theorem catPmf_pos (c : Cat) : 0 < catPmf c := by
  rw [catPmf_apply]
  exact ENNReal.div_pos (by exact_mod_cast (catPriorℕ_pos c).ne') (by norm_num)

/-- Joint world prior `P(c, f⃗) = P(c) · P(f⃗|c)`. -/
noncomputable def worldPmf : PMF World :=
  catPmf.bind (fun c => (featurePmf c).map (fun f => (c, f)))

/-- **`worldPmf` is full-support**: every world has positive joint prior
mass (since both `catPriorℕ` and `featurePriorℕ` are strictly positive
across the full domain). Discharged via `mem_support_bind_iff` +
`mem_support_map_iff` from mathlib. -/
theorem worldPmf_pos (w : World) : 0 < worldPmf w := by
  show 0 < (catPmf.bind _) w
  rw [PMF.apply_pos_iff, PMF.mem_support_bind_iff]
  refine ⟨w.1, (PMF.apply_pos_iff _ _).mp (catPmf_pos w.1), ?_⟩
  rw [PMF.mem_support_map_iff]
  exact ⟨w.2, (PMF.apply_pos_iff _ _).mp (featurePmf_pos _ _), rfl⟩

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

/-- The QUD-projected L0 marginal at `(g, u, f⃗)`: sum of `featurePmf u f'`
over the QUD-equivalence class of `f⃗`.

Built from the parametric `RSA.QUD.proj` substrate — the same primitive
shared with Kao 2014 hyperbole and Kao 2015 irony. -/
noncomputable def qudProjL0 (g : Goal) (u : Cat) (f : Features) : ℝ≥0∞ :=
  RSA.QUD.proj projectFeature (⇑(featurePmf u)) g f

theorem qudProjL0_le_one (g : Goal) (u : Cat) (f : Features) :
    qudProjL0 g u f ≤ 1 :=
  RSA.QUD.proj_le_one_of_pmf projectFeature (featurePmf u) g f

theorem qudProjL0_ne_top (g : Goal) (u : Cat) (f : Features) :
    qudProjL0 g u f ≠ ∞ :=
  RSA.QUD.proj_ne_top_of_pmf projectFeature (featurePmf u) g f

/-- The QUD-projected L0 marginal at `(g, u, f⃗)` is bounded below by
`featurePmf u f⃗` (since `f⃗` is in its own equivalence class). -/
theorem qudProjL0_ge_apply (g : Goal) (u : Cat) (f : Features) :
    featurePmf u f ≤ qudProjL0 g u f :=
  RSA.QUD.self_le_proj projectFeature (⇑(featurePmf u)) g f

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

/-- The score is never `+∞`: direct from substrate
`PMF.coe_mul_log_ne_top` (real coefficient × `log` of finite ENNReal). -/
theorem s1Score_ne_top (α : ℝ) (hα : 0 ≤ α) (g : Goal) (f : Features) (u : Cat) :
    s1Score α g f u ≠ ⊤ :=
  PMF.coe_mul_log_ne_top hα (qudProjL0_ne_top g u f)

/-- The score is never `−∞`: direct from substrate
`PMF.coe_mul_log_ne_bot` (real coefficient × `log` of nonzero ENNReal). -/
theorem s1Score_ne_bot (α : ℝ) (hα : 0 ≤ α) (g : Goal) (f : Features) (u : Cat) :
    s1Score α g f u ≠ ⊥ :=
  PMF.coe_mul_log_ne_bot hα (qudProjL0_ne_zero g u f)

/-- **Speaker S1**: softmax of QUD-projected log-utility (Eq. 1-2). -/
noncomputable def s1 (α : ℝ) (hα : 0 ≤ α) (g : Goal) (f : Features) : PMF Cat :=
  PMF.softmax (s1Score α g f)
    (fun u => s1Score_ne_top α hα g f u)
    ⟨.whale, s1Score_ne_bot α hα g f .whale⟩

/-- **`s1` is full-support**: every utterance has positive speaker mass.
Direct from the substrate `softmax_pos_iff_score_ne_bot`: the score is
finite-below at every utterance because `qudProjL0 g u f > 0` (full
literal-listener support across the QUD-projection in Kao's model). -/
theorem s1_pos (α : ℝ) (hα : 0 ≤ α) (g : Goal) (f : Features) (u : Cat) :
    0 < s1 α hα g f u := by
  show 0 < PMF.softmax _ _ _ u
  rw [PMF.softmax_pos_iff_score_ne_bot]
  exact s1Score_ne_bot α hα g f u

/-! ## §6. Goal-marginalised speaker -/

/-- **Goal-marginalised speaker**: `Σ_g P(g) · S1(· | g, f⃗)`. -/
noncomputable def mixedS1 (α : ℝ) (hα : 0 ≤ α) (goalPrior : PMF Goal)
    (f : Features) : PMF Cat :=
  goalPrior.bind (fun g => s1 α hα g f)

/-- **`mixedS1` positivity** (the architectural lemma the audit identified).
The goal-marginalised speaker assigns positive mass at every utterance,
provided some goal has positive prior. Witnessed by the `g`-th term of the
bind-tsum: `goalPrior g * s1 ... u > 0` because both factors are positive. -/
theorem mixedS1_pos (α : ℝ) (hα : 0 ≤ α) (goalPrior : PMF Goal)
    {g : Goal} (hg : goalPrior g ≠ 0) (f : Features) (u : Cat) :
    0 < mixedS1 α hα goalPrior f u := by
  show 0 < (goalPrior.bind _) u
  rw [PMF.apply_pos_iff, PMF.mem_support_bind_iff]
  exact ⟨g, hg, (s1_pos α hα g f u).ne'⟩

/-! ## §7. Pragmatic listener L1

`L1(c, f⃗ | u) ∝ worldPmf(c, f⃗) · mixedS1(u | f⃗)`.

PMF: posterior of the kernel `(c, f⃗) ↦ mixedS1(· | f⃗)` against `worldPmf`. -/

/-- The kernel for L1: `(c, f⃗) ↦ mixedS1(· | f⃗)`. Independent of `c`. -/
noncomputable def L1Kernel (α : ℝ) (hα : 0 ≤ α) (goalPrior : PMF Goal) :
    World → PMF Cat :=
  fun w => mixedS1 α hα goalPrior w.2

/-- L1 marginal at `u` is non-zero — needed for `posterior` discharge.
Direct from the witness `(.whale, (true, true, true))`: `worldPmf` is
full-support (`worldPmf_pos`) and `mixedS1` is positive at every utterance
when some goal has positive prior (`mixedS1_pos`). -/
theorem L1Kernel_marginal_ne_zero (α : ℝ) (hα : 0 ≤ α) (goalPrior : PMF Goal)
    {g : Goal} (hg : goalPrior g ≠ 0) (u : Cat) :
    PMF.marginal (L1Kernel α hα goalPrior) worldPmf u ≠ 0 :=
  PMF.marginal_ne_zero _ _ _ (worldPmf_pos (.whale, (true, true, true))).ne'
    (mixedS1_pos α hα goalPrior hg _ u).ne'

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

/-! ### §9a. Architectural theorems (parametric in priors)

The paper's headline isn't "P(person|whale) = 0.994 at Kao's specific
empirical priors". It's the architectural claim: rational speech act
pragmatics, with QUD-projected utility and a kernel that depends only
on features (not category), produces L1 posteriors that combine prior
knowledge with speaker-side preferences according to Bayes.

Each architectural theorem below states the structural content. The
Kao-specific corollaries in §9b instantiate at the empirical priors. -/

/-- **Architectural: posterior-fibre asymmetry follows the unnormalised sums**.
The structural-decomposition lemma applied to cat-fibres of the L1 posterior:
which category L1 favours after observing utterance `u` reduces to which
cat-fibre has more conditional joint mass under `worldPmf · mixedS1(u | ·)`.

This is the architectural form of `nonliteral` and `literal_correct`: both
findings are instances of "the cat-fibre with more conditional joint mass
wins". The numerical content per finding is the inequality of those sums
(Kao's specific values vs the model-class generic structure). -/
theorem L1_cat_fibre_lt_iff_inner_sum_lt
    (α : ℝ) (hα : 0 ≤ α) (goalPrior : PMF Goal)
    {g : Goal} (hg : goalPrior g ≠ 0) (u : Cat) (c₁ c₂ : Cat) :
    (L1 α hα goalPrior hg u).toOuterMeasure
        ↑(Finset.univ.filter (fun w : World => w.1 = c₁)) <
      (L1 α hα goalPrior hg u).toOuterMeasure
        ↑(Finset.univ.filter (fun w : World => w.1 = c₂)) ↔
      (∑ w ∈ Finset.univ.filter (fun w : World => w.1 = c₁),
          worldPmf w * mixedS1 α hα goalPrior w.2 u) <
      (∑ w ∈ Finset.univ.filter (fun w : World => w.1 = c₂),
          worldPmf w * mixedS1 α hα goalPrior w.2 u) := by
  unfold L1
  exact PMF.posterior_toOuterMeasure_lt_iff_finset_score_lt _ _ _ _ _ _

/-- **Architectural: feature-set asymmetry follows the unnormalised sums**.
Companion of `L1_cat_fibre_lt_iff_inner_sum_lt` for feature-event sets
(used by Findings 2-4 and 5).

The `feature_pred` predicate carves out a feature-event in `World`; outer
measure of that event under L1 reduces to summing the conditional joint
masses over the feature-event-fibre. -/
theorem L1_feature_event_lt_iff_inner_sum_lt
    (α : ℝ) (hα : 0 ≤ α) (goalPrior : PMF Goal)
    {g : Goal} (hg : goalPrior g ≠ 0) (u : Cat)
    (P Q : World → Prop) [DecidablePred P] [DecidablePred Q] :
    (L1 α hα goalPrior hg u).toOuterMeasure
        ↑(Finset.univ.filter P) <
      (L1 α hα goalPrior hg u).toOuterMeasure
        ↑(Finset.univ.filter Q) ↔
      (∑ w ∈ Finset.univ.filter P,
          worldPmf w * mixedS1 α hα goalPrior w.2 u) <
      (∑ w ∈ Finset.univ.filter Q,
          worldPmf w * mixedS1 α hα goalPrior w.2 u) := by
  unfold L1
  exact PMF.posterior_toOuterMeasure_lt_iff_finset_score_lt _ _ _ _ _ _

/-! ### §9b. Kao-specific corollaries (paper findings at empirical priors)

The 6 findings from `[kao-etal-2014-metaphor]` §"Model Evaluation"
expressed as direct outer-measure inequalities at Kao's empirical priors.

Each finding reduces via §9a's architectural theorems to a comparison of
conditional joint sums at Kao's specific values. The remaining numerical
discharge is the empirical-fit content — sorried with TODO notes; full
formalisation requires either (a) the `softmaxWeight_natMul_log_eq_pow`
bridge (substrate, available) plus per-feature `gcongr`/`norm_num`
chains over the rpow form, or (b) a `mixedS1_lower` lemma giving an
explicit positive lower bound on the speaker contribution. -/

/-- **Finding 1 (Nonliteral interpretation)**: hearing "whale", listener
infers `person`, not literally `whale`. Paper: P(c_p|u_whale) = 0.994.

By `L1_cat_fibre_lt_iff_inner_sum_lt`, reduces to comparing conditional
joint sums on the two cat-fibres. The 99× catPrior asymmetry dominates
the bounded speaker contribution. -/
theorem nonliteral :
    (vagueL1 .whale).toOuterMeasure {w | w.1 = .person} >
    (vagueL1 .whale).toOuterMeasure {w | w.1 = .whale} := by
  sorry

/-- **Finding 2 (Feature elevation: large)**: hearing "whale" raises P(large = T).
By `L1_feature_event_lt_iff_inner_sum_lt`, reduces to comparing conditional
joint sums over the two feature-event-fibres. Whale's featurePrior is
concentrated on `large = T`. -/
theorem feature_large :
    (vagueL1 .whale).toOuterMeasure {w | w.2.1 = true} >
    (vagueL1 .whale).toOuterMeasure {w | w.2.1 = false} := by
  sorry

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

/-- **Finding 5 (Context sensitivity)**: specific QUD raises P(large = T).
Cross-config comparison: same outer-measure target, different goalPrior. -/
theorem context_sensitivity :
    (specificL1 .whale).toOuterMeasure {w | w.2.1 = true} >
    (vagueL1 .whale).toOuterMeasure {w | w.2.1 = true} := by
  sorry

/-- **Finding 6 (Literal correctness)**: hearing "person", listener
correctly infers `person`. Both prior AND speaker preferences agree on
.person; the cleanest of the 6 findings.

Demonstrates the architectural-theorem usage: convert Set notation to
Finset.filter, apply `L1_cat_fibre_lt_iff_inner_sum_lt`, sorry the
remaining inner-sum inequality (the empirical-fit content). -/
theorem literal_correct :
    (vagueL1 .person).toOuterMeasure {w | w.1 = .person} >
    (vagueL1 .person).toOuterMeasure {w | w.1 = .whale} := by
  rw [gt_iff_lt, ← Finset.coe_filter_univ (fun w : World => w.1 = .whale),
      ← Finset.coe_filter_univ (fun w : World => w.1 = .person),
      L1_cat_fibre_lt_iff_inner_sum_lt]
  -- Goal reduced to:
  -- ∑ w ∈ filter (·.1 = .whale), worldPmf w * mixedS1 ... w.2 .person <
  -- ∑ w ∈ filter (·.1 = .person), worldPmf w * mixedS1 ... w.2 .person
  -- The empirical-fit content: 99x catPrior asymmetry + speaker positivity.
  sorry

/-! ## §10. Cross-paper engagement

[frank-goodman-2012] is the architectural ancestor — basic L0/S1/L1
without QUD inference. Kao's contribution is the joint inference over
goals, opening the door to nonliteral interpretations.

[goodman-stuhlmuller-2013] (`Studies/GoodmanStuhlmuller2013.lean`)
shares the hypergeometric-kernel architecture with Kao's L0 (both use
"P(features|category) if categories match"). The architectural difference:
G&S2013 is one-step Bayesian (no goal inference); Kao's L1 is two-stage
(joint goal-inference enables metaphorical readings).

[kao-etal-2014-hyperbole] (sister paper, same conference) uses the
identical RSA architecture for hyperbole (with `quantity` rather than
`category` as the literally-false dimension). Migration of the hyperbole
file would reuse most of this file's substrate.
-/

end KaoEtAl2014PMFMetaphor
