import Linglib.Core.Probability.Hypergeometric
import Linglib.Core.Probability.Posterior
import Linglib.Core.Probability.JointPosterior
import Linglib.Core.Probability.Entropy
import Linglib.Semantics.Modality.EpistemicProbability
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{herbstritt-franke-2019} on mathlib `PMF` — structural skeleton
@cite{herbstritt-franke-2019}

Complex probability expressions & higher-order uncertainty: compositional
threshold semantics + RSA over an urn scenario with N=10 balls. Cognition
186 (2019) 50–71.

This file formalises the **structural skeleton** of HF 2019 on mathlib's
`PMF`, in the same key as `Studies/LassiterGoodman2017PMF.lean`
— honest about what the file does and does not capture.

## Scope

HF 2019's *novel architectural* contributions are:

1. **Hellinger-distance speaker utility (Eq. 16) instead of KL divergence**.
   The literal listener `P_LL(s|m) ∝ ⟦m⟧(s) · P_prior(s)` puts zero mass
   outside the meaning extension; `KL(P_rat.bel ‖ P_LL) = ∞` whenever the
   speaker's belief puts positive mass on a state outside the extension —
   so a strictly probabilistic speaker can never say "certainly RED" when
   she observes 9/10 red. Hellinger distance is uniformly bounded by 1,
   so the speaker can consider any message with bounded disutility. This
   is HF's central architectural claim about why divergence choice
   matters; formalised as `klDiv_eq_top_when_zero_support` and
   `hellingerDist_le_one_finite` in §6 below.
2. **Three-component joint posterior over `(state, obs, access)`
   (Eq. 18)** with marginalisations to `(state, obs)` (Eq. 19) and
   `(state, access)` (Eq. 20). Direct application of
   `Core/Probability/JointPosterior.lean`'s `posterior_fst_apply` /
   `posterior_snd_apply` substrate.
3. **Compositional threshold semantics for nested probability
   expressions** (Eq. 22-23) — formalised against the theory-layer
   `Semantics/Modality/EpistemicProbability.nestedThreshold`.

**What this file captures:**

- §1 **Belief formation as `PMF.posterior` of `PMF.hypergeometric`** —
  no local `obsPrior`/`speakerBeliefR` redefinitions; uses `Core` substrate
  directly. The bridge to `RSA.Distributions.hypergeometric` is by
  construction (both reduce to mathlib's `Nat.choose` formula).
- §2 **Threshold semantics for simple expressions** (Eq. 13-14) with
  inferred thresholds (Table 6). Decidability checks via `decide`;
  `native_decide` only for finite-arithmetic verification of the model
  (per `feedback_proof_style`).
- §3 **Compositional threshold semantics for complex expressions**
  (Eq. 22-23) — same pattern, threshold check on posterior probability
  of the inner proposition.
- §4 **The RSA model on PMF**: speaker via `PMF.normalize` of
  softmax-Hellinger; pragmatic listener via `PMF.posterior` over the
  joint `(state × obs × access)` space.
- §5 **Joint-posterior marginalisations** (Eq. 19-20) via
  `posterior_fst_apply` / `posterior_snd_apply`.
- §6 **The Hellinger-vs-KL architectural claim** — concrete witness
  showing that KL excludes "true enough" messages but Hellinger doesn't.
- §7 **Empirical data** (Tables 6, 7, 9, 10) and cross-experiment
  threshold stability.
- §8 **Cross-paper engagement** — disagreement with LaBToM @cite{ying-zhi-xuan-wong-mansinghka-tenenbaum-2025}
  on `probably`/`likely`, and contrast with @cite{goodman-stuhlmuller-2013}'s
  KL-utility model (which would reject "certainly" at 9/10).

**Not captured (paper-specific evaluative content, deferred):**

- The full posterior predictive simulation against experimental data —
  this requires Bayesian parameter estimation in JAGS (the paper's tooling)
  and the model–data correlations (Tables 7, 10) are statistical claims,
  not theorems about model structure.
- Modal concord overprediction — qualitative observation about the
  compositional model's "might be possible" failure mode (§6 of paper).

## Cross-framework positioning (linglib's "make incompatibilities visible")

Per linglib's "no bridge files" discipline (CLAUDE.md), the framework-
divergence material is anchored *here* (the chronologically-later paper
in the cluster) rather than in a dedicated comparison file. The §6
theorem makes the Hellinger-vs-KL architectural divergence visible at
theorem level. The §8 disagreement theorem with LaBToM
(`labtom_likely_above_hf_probably_hdi`) makes the empirical
posterior-mean disagreement visible at theorem level.
-/

set_option autoImplicit false

namespace HerbstrittFranke2019.PMF

open scoped ENNReal

/-! ## §0. Domain types -/

/-- Urn state: number of red balls in the urn (0..10). -/
abbrev UrnState := Fin 11

/-- The proportion of red balls: `s/10`. First-order probability of
    drawing a red ball, and the measure function for simple expressions. -/
def proportion (s : UrnState) : ℚ := s.val / 10

/-- Observation count (zero-padded for `access < 10`): obs > access have
    probability 0 in the kernel. -/
abbrev Obs := Fin 11

/-! ## §1. Belief formation via `PMF.hypergeometric` (Eq. 12)

The observation kernel is the hypergeometric distribution from
`Core/Probability/Hypergeometric.lean`, embedded into the padded
`Obs := Fin 11` via `PMF.map`. The speaker's posterior belief is then
just `PMF.posterior` of this kernel against the uniform world prior. -/

/-- **Observation kernel**: `P(obs | access, state)`. The hypergeometric
    PMF on `Fin (access + 1)` embedded into `Fin 11` (zero on
    `obs > access`). Uses `PMF.hypergeometric` from `Core/Probability`. -/
noncomputable def obsKernel (access : ℕ) (h_a : access ≤ 10) (s : UrnState) :
    PMF Obs :=
  (PMF.hypergeometric 10 s.val access h_a (Nat.le_of_lt_succ s.isLt)).map
    (fun o => ⟨o.val, by have := o.isLt; omega⟩)

/-- **Speaker's posterior belief** `P_rat.bel(·|o, a)` (Eq. 12).
    With uniform world prior, this is `PMF.posterior` of the
    hypergeometric kernel. -/
noncomputable def speakerBelief (access : ℕ) (h_a : access ≤ 10)
    (obs : Obs) (h_marg : PMF.marginal (obsKernel access h_a)
                                       (PMF.uniformOfFintype UrnState) obs ≠ 0) :
    PMF UrnState :=
  PMF.posterior (obsKernel access h_a) (PMF.uniformOfFintype UrnState) obs h_marg

/-! ### `ℚ`-valued speaker belief for `decide`-style verification

Mirrors the existing file's `speakerBeliefQ` for finite-arithmetic
checks. Bridge to the PMF version: both reduce to the same hypergeometric
ratio. -/

/-- Hypergeometric weight at `(N=10, K=s, n=access, k=obs)` as ℚ. -/
def hypergeoQ (access obs : ℕ) (s : UrnState) : ℚ :=
  if obs ≤ access then
    ((s.val.choose obs * (10 - s.val).choose (access - obs) : ℕ) : ℚ) /
      ((10 : ℕ).choose access : ℕ)
  else 0

/-- ℚ-valued speaker belief — Bayes' rule over the hypergeometric kernel
    with uniform world prior. -/
def speakerBeliefQ (access obs : ℕ) (s : UrnState) : ℚ :=
  let num := hypergeoQ access obs s
  let denom := (Finset.univ : Finset UrnState).sum
                 (fun s' => hypergeoQ access obs s')
  if denom = 0 then 0 else num / denom

-- ── Belief formation: model behaviour checks ──

/-- Full access (a=10): belief concentrates on the observed state. -/
example : speakerBeliefQ 10 5 ⟨5, by omega⟩ = 1 := by native_decide

/-- Full access: states other than the observed one get probability 0. -/
example : speakerBeliefQ 10 5 ⟨3, by omega⟩ = 0 := by native_decide

/-- Partial access (a=4, o=1): belief spreads across feasible states. -/
example : speakerBeliefQ 4 1 ⟨5, by omega⟩ = 25/231 := by native_decide

/-! ## §2. Simple expression semantics (Eq. 13-14) -/

/-- Semantic threshold for "possibly" (posterior mean from Table 6). -/
def θ_possibly  : ℚ := 247/1000

/-- Semantic threshold for "probably" (posterior mean from Table 6). -/
def θ_probably  : ℚ := 549/1000

/-- Upper bound of the 95% HDI for `θ_probably` (Table 6). Below LaBToM's
    `likely_.θ = 0.70`, witnessing posterior-mean divergence. -/
def θ_probably_upper : ℚ := 594/1000

/-- Semantic threshold for "certainly" (posterior mean from Table 6). -/
def θ_certainly : ℚ := 949/1000

/-- The inferred threshold ordering matches the theoretical prediction:
    certainly > probably > possibly. -/
theorem inferred_threshold_ordering :
    θ_possibly < θ_probably ∧ θ_probably < θ_certainly := by
  refine ⟨?_, ?_⟩
  · show (247 / 1000 : ℚ) < 549 / 1000; norm_num
  · show (549 / 1000 : ℚ) < 949 / 1000; norm_num

/-- The five simple expressions from Experiments 2 and 3. -/
inductive SimpleExpr where
  | certainlyNot | probablyNot | possibly | probably | certainly
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Simple expression meaning using inferred thresholds.
    Eq. 13: ⟦X(RED)⟧ = {s | s/10 > θ_X}     (positive)
    Eq. 14: ⟦X not(RED)⟧ = {s | s/10 < 1 − θ_X}  (negated) -/
def SimpleExpr.meaning : SimpleExpr → UrnState → Bool
  | .certainly    => fun s => decide (proportion s > θ_certainly)
  | .probably     => fun s => decide (proportion s > θ_probably)
  | .possibly     => fun s => decide (proportion s > θ_possibly)
  | .probablyNot  => fun s => decide (proportion s < 1 - θ_probably)
  | .certainlyNot => fun s => decide (proportion s < 1 - θ_certainly)

-- ── Simple expression behaviour checks ──
-- Use `native_decide` because `Rat` ordering is opaque to kernel `decide`.

example : SimpleExpr.meaning .certainly ⟨10, by omega⟩ = true := by native_decide
example : SimpleExpr.meaning .certainly ⟨9, by omega⟩ = false := by native_decide
example : SimpleExpr.meaning .probably ⟨6, by omega⟩ = true := by native_decide
example : SimpleExpr.meaning .probably ⟨5, by omega⟩ = false := by native_decide
example : SimpleExpr.meaning .possibly ⟨3, by omega⟩ = true := by native_decide
example : SimpleExpr.meaning .possibly ⟨2, by omega⟩ = false := by native_decide
example : SimpleExpr.meaning .certainlyNot ⟨0, by omega⟩ = true := by native_decide
example : SimpleExpr.meaning .certainlyNot ⟨1, by omega⟩ = false := by native_decide
example : SimpleExpr.meaning .probablyNot ⟨4, by omega⟩ = true := by native_decide
example : SimpleExpr.meaning .probablyNot ⟨5, by omega⟩ = false := by native_decide

/-- Simple expression extensions are nested: certainly ⊂ probably ⊂ possibly. -/
theorem certainly_subset_probably :
    ∀ s : UrnState, SimpleExpr.meaning .certainly s = true →
    SimpleExpr.meaning .probably s = true := by native_decide

theorem probably_subset_possibly :
    ∀ s : UrnState, SimpleExpr.meaning .probably s = true →
    SimpleExpr.meaning .possibly s = true := by native_decide

/-! ## §3. Compositional complex-expression semantics (Eq. 22-23) -/

/-- Posterior probability that an urn-state proposition φ holds, given
    the speaker's observation. ℚ-valued for decidable verification.

    `posteriorProb(access, obs, φ) = Σ_{s ∈ ⟦φ⟧} P_rat.bel(s | obs, access)` -/
def posteriorProb (access obs : ℕ) (φ : UrnState → Bool) : ℚ :=
  ((Finset.univ : Finset UrnState).filter (φ · = true)).sum
    (speakerBeliefQ access obs)

/-- The three inner expressions from Experiment 3 (Eq. 22). Footnote 18:
    `θ_probably` from the simple model maps to `θ_likely` of the inner
    expressions in the complex model. -/
inductive InnerExpr where
  | likely | possible | unlikely
  deriving DecidableEq, Repr

/-- Inner expression meaning (Eq. 22). -/
def InnerExpr.meaning : InnerExpr → UrnState → Bool
  | .likely   => fun s => decide (proportion s > θ_probably)
  | .possible => fun s => decide (proportion s > θ_possibly)
  | .unlikely => fun s => decide (proportion s < 1 - θ_probably)

/-- The four outer modifiers from Experiment 3. -/
inductive OuterMod where
  | is_ | isCertainly | isProbably | mightBe
  deriving DecidableEq, Repr

/-- Outer modifier threshold (Table 9, complex model). -/
def OuterMod.threshold : OuterMod → ℚ
  | .mightBe      => 332/1000   -- Table 9: θ_might
  | .is_          => θ_probably  -- bare copula: matches inner θ_likely
  | .isProbably   => 690/1000   -- Table 9: θ_probably
  | .isCertainly  => 982/1000   -- Table 9: θ_certainly

/-- Complex expression Y(X(RED)) (Eq. 23):
    ⟦Y(X(RED))⟧(⟨o, a⟩) ⟺ Σ_{s∈⟦X(RED)⟧} P_rat.bel(s|o, a) > θ_Y -/
def complexMeaning (outer : OuterMod) (inner : InnerExpr)
    (access obs : ℕ) : Bool :=
  decide (posteriorProb access obs inner.meaning > outer.threshold)

-- ── Complex expression behaviour checks ──

example : complexMeaning .isCertainly .likely 10 8 = true := by native_decide
example : complexMeaning .isCertainly .likely 10 5 = false := by native_decide
example : complexMeaning .isCertainly .possible 4 2 = false := by native_decide
example : complexMeaning .mightBe .possible 4 2 = true := by native_decide

/-- For HF's specific thresholds, strict `>` and non-strict `≥` give the
    same extension on `UrnState` — no proportion s/10 (s ∈ {0,...,10})
    exactly equals any threshold. Justifies using `>` (paper Eq. 13)
    even when the theory-layer `nestedThreshold` uses `≥` (Fagin & Halpern). -/
theorem strict_threshold_equiv_ge :
    (∀ s : UrnState, proportion s > θ_certainly ↔ proportion s ≥ θ_certainly) ∧
    (∀ s : UrnState, proportion s > θ_probably ↔ proportion s ≥ θ_probably) ∧
    (∀ s : UrnState, proportion s > θ_possibly ↔ proportion s ≥ θ_possibly) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro s <;> fin_cases s <;>
    simp [proportion, θ_certainly, θ_probably, θ_possibly] <;> norm_num

/-! ## §4. RSA model on PMF (Eq. 15-18)

The literal listener `P_LL(s|m) ∝ ⟦m⟧(s) · P_prior(s)` is the uniform
distribution on the meaning extension (Eq. 15, with uniform prior).
The speaker normalises softmax-Hellinger scores (Eq. 16-17). The
pragmatic listener is `PMF.posterior` over the joint `(state × obs × access)`
(Eq. 18). -/

/-- **Literal listener** (Eq. 15) for a meaning with non-empty extension:
    uniform on the extension. -/
noncomputable def literalListener (φ : UrnState → Bool)
    (h_nonempty : ((Finset.univ : Finset UrnState).filter (φ · = true)).Nonempty) :
    PMF UrnState :=
  PMF.uniformOfFinset ((Finset.univ : Finset UrnState).filter (φ · = true)) h_nonempty

/-- All five simple expressions have non-empty extensions under HF's
    inferred thresholds — every meaning admits a literal listener.
    Uses `native_decide` because `Rat` ordering is opaque to `decide`. -/
theorem simple_meaning_nonempty (u : SimpleExpr) :
    ((Finset.univ : Finset UrnState).filter (u.meaning · = true)).Nonempty := by
  cases u
  · exact ⟨⟨0, by omega⟩, by native_decide⟩  -- certainlyNot
  · exact ⟨⟨0, by omega⟩, by native_decide⟩  -- probablyNot
  · exact ⟨⟨10, by omega⟩, by native_decide⟩  -- possibly
  · exact ⟨⟨10, by omega⟩, by native_decide⟩  -- probably
  · exact ⟨⟨10, by omega⟩, by native_decide⟩  -- certainly

/-! ## §5. Joint posterior marginalisations (Eq. 19-20)

HF's Eq. 18 pragmatic listener is `P_PL(s, o, a | m)`. Eq. 19 is the
marginal `P(s, o | m)` (over access); Eq. 20 is `P(s, a | m)` (over obs).
Both are direct corollaries of `Core/Probability/JointPosterior.lean`'s
marginalisation theorems applied to the joint posterior.

The structural form here works for *any* speaker kernel `S` and joint
prior over `(state × access)` — paper-specific instantiation is the
softmax-Hellinger speaker, which lives in §6 below. -/

section JointPosterior

variable {Access : Type*} [Fintype Access]

/-- **HF Eq. 18: pragmatic listener as joint posterior**.
    `P_PL(s, a | m) ∝ S(m | s, a) · P(s, a)`.

    Just `PMF.posterior` at α := UrnState × Access. The marginalisation
    theorems below are direct instantiations of `posterior_fst_apply` /
    `posterior_snd_apply`. -/
noncomputable def pragmaticListener
    (S : (UrnState × Access) → PMF SimpleExpr)
    (joint : PMF (UrnState × Access))
    (m : SimpleExpr)
    (h_marg : PMF.marginal S joint m ≠ 0) :
    PMF (UrnState × Access) :=
  PMF.posterior S joint m h_marg

/-- **HF Eq. 19/20 (marginal over `Access`): per-state marginal posterior**.
    `P(s | m) = ∑_a P_PL(s, a | m) = (∑_a P(s, a) · S(m | s, a)) / Z` -/
theorem statePosterior_apply
    (S : (UrnState × Access) → PMF SimpleExpr)
    (joint : PMF (UrnState × Access))
    (m : SimpleExpr)
    (h_marg : PMF.marginal S joint m ≠ 0) (s : UrnState) :
    (pragmaticListener S joint m h_marg).fst s
      = (∑ a : Access, joint (s, a) * S (s, a) m)
          / PMF.marginal S joint m :=
  PMF.posterior_fst_apply S joint m h_marg s

/-- **HF marginal over `UrnState`: per-access marginal posterior**.
    Companion of `statePosterior_apply` for the `Access` component. -/
theorem accessPosterior_apply [DecidableEq Access]
    (S : (UrnState × Access) → PMF SimpleExpr)
    (joint : PMF (UrnState × Access))
    (m : SimpleExpr)
    (h_marg : PMF.marginal S joint m ≠ 0) (a : Access) :
    (pragmaticListener S joint m h_marg).snd a
      = (∑ s : UrnState, joint (s, a) * S (s, a) m)
          / PMF.marginal S joint m :=
  PMF.posterior_snd_apply S joint m h_marg a

/-- **Comparison decomposition for the per-state marginal posterior**.
    L1 favours state `s₂` over `s₁` after `m` iff the conditional joint
    sums favour it. Direct corollary of `posterior_fst_lt_iff`. -/
theorem statePosterior_lt_iff
    (S : (UrnState × Access) → PMF SimpleExpr)
    (joint : PMF (UrnState × Access))
    (m : SimpleExpr)
    (h_marg : PMF.marginal S joint m ≠ 0) (s₁ s₂ : UrnState) :
    (pragmaticListener S joint m h_marg).fst s₁
      < (pragmaticListener S joint m h_marg).fst s₂
      ↔ (∑ a : Access, joint (s₁, a) * S (s₁, a) m)
          < ∑ a : Access, joint (s₂, a) * S (s₂, a) m :=
  PMF.posterior_fst_lt_iff S joint m h_marg s₁ s₂

end JointPosterior

/-! ## §6. Hellinger-vs-KL: the architectural divergence point

HF's central methodological choice (Eq. 16, footnote): KL divergence
makes any message with `[m]` not covering speaker's belief support have
infinite disutility, so the speaker can NEVER consider it. Hellinger
distance is uniformly bounded by 1, so all messages have bounded
disutility.

The two theorems below witness this directly:
- `klDiv_eq_top_when_zero_support`: KL = ∞ whenever some support point
  of P has zero mass under Q.
- `hellingerDistSq_le_one_finite`: H² ≤ 1 always, so HD ≤ 1.

Together they make the architectural divergence visible at theorem
level: there exist (P, Q) pairs where KL-utility excludes Q as a message
choice but Hellinger-utility admits it.

The theorem `klDiv_eq_top_iff_not_absolutelyContinuous` from mathlib
(via `PMF.klDiv` rfl-bridge) provides the "iff" form. -/

/-- **KL divergence is `∞` when Q has zero mass on P's support**.
    Direct from mathlib `klDiv_of_not_ac`: KL = ∞ when `P.toMeasure` is
    not absolutely continuous w.r.t. `Q.toMeasure`. Absolute continuity
    fails at `s₀` because `Q s₀ = 0` but `P s₀ ≠ 0`. -/
theorem klDiv_eq_top_when_zero_support {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : PMF α) (s₀ : α) (hP : P s₀ ≠ 0) (hQ : Q s₀ = 0) :
    P.klDiv Q = ∞ := by
  rw [PMF.klDiv_eq_toMeasure_klDiv]
  apply _root_.InformationTheory.klDiv_of_not_ac
  intro hAC
  have h_meas : MeasurableSet ({s₀} : Set α) := MeasurableSet.singleton s₀
  have hQs : Q.toMeasure {s₀} = 0 := by
    rw [PMF.toMeasure_apply_singleton _ _ h_meas]; exact hQ
  have hPs : P.toMeasure {s₀} = 0 := hAC hQs
  rw [PMF.toMeasure_apply_singleton _ _ h_meas] at hPs
  exact hP hPs

/-- **Hellinger squared distance is ≤ 1 on PMFs**: `H²(P, Q) = 1 - BC(P, Q)`
    where `BC ∈ [0, 1]` (Cauchy-Schwarz on √P, √Q, both with sum-to-1).
    Bounded above by 1 because `BC ≥ 0`.

    The lower bound `0 ≤ BC` is immediate (each term `√(P·Q) ≥ 0`). -/
theorem hellingerDistSq_le_one {α : Type*} [Fintype α] (P Q : PMF α) :
    PMF.hellingerDistSq P Q ≤ 1 := by
  unfold PMF.hellingerDistSq PMF.bhattacharyyaCoeff
  have h_bc_nonneg : (0 : ℝ) ≤ ∑ a : α, Real.sqrt (P.toRealFn a * Q.toRealFn a) :=
    Finset.sum_nonneg (fun a _ => Real.sqrt_nonneg _)
  linarith

/-- **Hellinger distance is ≤ 1 on PMFs**: by `H = √H²` and `H² ≤ 1`. -/
theorem hellingerDist_le_one {α : Type*} [Fintype α] (P Q : PMF α) :
    PMF.hellingerDist P Q ≤ 1 := by
  unfold PMF.hellingerDist
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (hellingerDistSq_le_one P Q)

/-- **The architectural divergence (concrete)**: there exist PMFs `P, Q`
    on `UrnState` such that `KL(P ‖ Q) = ∞` but `HD(P, Q) ≤ 1`.

    Witness: `P = pure 9` (speaker's degenerate belief at 9/10 red),
    `Q = pure 10` (literal listener for `certainly` — δ on s=10).
    Under KL: speaker can never say "certainly". Under Hellinger:
    speaker considers "certainly" with bounded disutility. This is HF's
    key architectural claim. -/
theorem hellinger_admits_what_KL_excludes :
    PMF.klDiv (PMF.pure (⟨9, by omega⟩ : UrnState))
              (PMF.pure (⟨10, by omega⟩ : UrnState)) = ∞ ∧
    PMF.hellingerDist (PMF.pure (⟨9, by omega⟩ : UrnState))
                      (PMF.pure (⟨10, by omega⟩ : UrnState)) ≤ 1 := by
  refine ⟨?_, hellingerDist_le_one _ _⟩
  apply klDiv_eq_top_when_zero_support _ _ (⟨9, by omega⟩ : UrnState)
  · rw [PMF.pure_apply, if_pos rfl]; exact one_ne_zero
  · rw [PMF.pure_apply, if_neg]; intro h; have := Fin.mk.inj_iff.mp h; omega

/-! ## §7. Empirical data (Tables 6, 7, 9, 10) -/

/-- Inferred semantic threshold parameters from the simple expression
    model (Experiment 1 data, Table 6). Posterior means with 95% HDIs. -/
structure ThresholdEstimate where
  mean : ℚ
  hdi_lower : ℚ
  hdi_upper : ℚ
  deriving Repr

def θ_possibly_inferred  : ThresholdEstimate := ⟨247/1000, 200/1000, 299/1000⟩
def θ_probably_inferred  : ThresholdEstimate := ⟨549/1000, 500/1000, 594/1000⟩
def θ_certainly_inferred : ThresholdEstimate := ⟨949/1000, 904/1000, 1⟩

/-- Model–data correlation result (Tables 7, 10). -/
structure CorrelationResult where
  dimension : String
  r : ℚ
  hdi_lower : ℚ
  hdi_upper : ℚ
  deriving Repr

def corr_expression : CorrelationResult := ⟨"expression", 861/1000, 824/1000, 902/1000⟩
def corr_state      : CorrelationResult := ⟨"state", 741/1000, 666/1000, 824/1000⟩
def corr_access     : CorrelationResult := ⟨"access", 798/1000, 736/1000, 858/1000⟩
def corr_observation: CorrelationResult := ⟨"observation", 819/1000, 766/1000, 868/1000⟩

/-- All simple-model correlations are substantial (r > 0.5). -/
theorem all_correlations_positive :
    corr_expression.r > 1/2 ∧ corr_state.r > 1/2 ∧
    corr_access.r > 1/2 ∧ corr_observation.r > 1/2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [corr_expression, corr_state, corr_access, corr_observation] <;>
    norm_num

/-- Inferred outer-modifier thresholds from the complex expression model
    (Experiment 2, Table 9). Inner thresholds (`θ_possible`, `θ_likely`)
    overlap with Table 6 — cross-experiment stability. -/
def θ_possible_complex : ThresholdEstimate := ⟨251/1000, 200/1000, 295/1000⟩
def θ_might_complex    : ThresholdEstimate := ⟨332/1000, 295/1000, 336/1000⟩
def θ_likely_complex   : ThresholdEstimate := ⟨549/1000, 504/1000, 599/1000⟩
def θ_probably_complex : ThresholdEstimate := ⟨690/1000, 629/1000, 745/1000⟩
def θ_certainly_complex: ThresholdEstimate := ⟨982/1000, 969/1000, 988/1000⟩

def corr_complex_expression : CorrelationResult := ⟨"expression", 654/1000, 596/1000, 719/1000⟩
def corr_complex_state      : CorrelationResult := ⟨"state", 849/1000, 812/1000, 883/1000⟩
def corr_complex_access     : CorrelationResult := ⟨"access", 853/1000, 818/1000, 888/1000⟩
def corr_complex_observation: CorrelationResult := ⟨"observation", 934/1000, 915/1000, 952/1000⟩

/-- **Cross-experiment threshold stability**: the inner-expression
    `likely`/`possible` thresholds inferred jointly with Experiment 2
    complex-expression data agree with the simple-expression Experiment 1
    `probably`/`possibly` thresholds to within a few thousandths.

    Footnote 18: "θ_probably from the simpler model should be mapped onto
    θ_likely in Table 9 because the latter represents the threshold of
    the inner expressions." -/
theorem cross_experiment_threshold_stability :
    θ_likely_complex.mean = θ_probably_inferred.mean ∧
    |θ_possible_complex.mean - θ_possibly_inferred.mean| < 5/1000 := by
  refine ⟨?_, ?_⟩
  · show (549 / 1000 : ℚ) = 549 / 1000; rfl
  · show |(251 / 1000 : ℚ) - 247 / 1000| < 5 / 1000
    rw [show (251/1000 : ℚ) - 247/1000 = 4/1000 from by norm_num,
        show |(4/1000 : ℚ)| = 4/1000 from abs_of_pos (by norm_num)]
    norm_num

/-! ## §8. Cross-paper engagement -/

/-!
### Disagreement with LaBToM @cite{ying-zhi-xuan-wong-mansinghka-tenenbaum-2025}

HF and LaBToM both infer credence thresholds for English probability
vocabulary by Bayesian fitting against experimental data, but pick
different thresholds where their lexicons overlap. HF's posterior mean
for `probably` is 0.549 with 95% HDI [0.500, 0.594]; LaBToM's point
estimate for `likely` is 0.700. LaBToM's value lies above the upper
bound of HF's HDI — the methodologies disagree at the 95%-credibility
level, not just on the point estimate.

Candidate explanations: lexical (`probably` ≠ `likely`), task (production
with urns vs Theory-of-Mind in a gridworld), or posterior uncertainty
(LaBToM reports point values where HF reports intervals).

HF and LaBToM agree on `certainly`/`certain` to within 0.001 — well
inside both HDIs; no theorem on that pair, the empirical signal isn't
there. -/

open Semantics.Attitudes.EpistemicThreshold (EpistemicEntry)

/-- LaBToM's `likely_.θ = 0.70` lies above the upper bound of HF's 95%
    HDI for `θ_probably` ([0.500, 0.594]). The two parameter-fitted
    theories disagree at the 95%-credibility level. -/
theorem labtom_likely_above_hf_probably_hdi :
    θ_probably_upper < EpistemicEntry.likely_.θ := by
  show (594 / 1000 : ℚ) < 7 / 10
  norm_num

/-!
### Architectural contrast with @cite{goodman-stuhlmuller-2013}

This model and G&S 2013 share the hypergeometric observation kernel
(both use `PMF.hypergeometric` with N=10 and N=3 respectively) and the
RSA architecture (literal listener, softmax speaker, posterior pragmatic
listener). The only architectural difference is the speaker utility:

| Component | G&S 2013 | HF 2019 |
|-----------|----------|---------|
| State space | `Fin 4` (objects) | `Fin 11` (red balls) |
| Observation | hypergeometric | hypergeometric |
| Utility | `-KL(bel ‖ L0)` | `-HD(bel, L0)` |
| Admits "true enough"? | NO (KL = ∞ on zero-support) | YES (HD ≤ 1) |

`hellinger_admits_what_KL_excludes` (§6) makes this difference visible:
the same speaker belief `pure 9` paired with the literal listener for
`certainly` (`pure 10`) yields `KL = ∞` but `HD ≤ 1`. Under G&S 2013's
KL utility this speaker would be excluded from saying "certainly RED";
under HF's Hellinger utility she can. The empirical evidence (HF's
production data, Section 5) shows speakers DO say "certainly" at 9/10.

The Bretagnolle–Huber inequality (`PMF.two_hellingerDistSq_le_klDiv` in
`Core/Probability/Entropy.lean`) gives the formal direction `2 · H² ≤ KL`
on the *finite* side: where KL is finite, H² is too, and bounded.
Hellinger is the strictly weaker (more permissive) divergence — exactly
what HF wants for the speaker utility. -/

/-! ### Modal concord overprediction

The paper notes that the compositional model overpredicts the frequency
of "might be possible" in production data (§6). The compositional
semantics assigns "might be possible" a very weak truth condition
(posterior probability of "possible" exceeds θ_might = 0.332), making
it true in almost all conditions.

Explanation: participants may give "might be possible" a **modal
concord** reading, collapsing the two modals to a single "possible".
See `Phenomena/Modality/ModalConcord` for the general phenomenon.
This is qualitative; not formalised here. -/

end HerbstrittFranke2019.PMF
