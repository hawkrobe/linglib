import Linglib.Core.Probability.Hypergeometric
import Linglib.Core.Probability.Posterior
import Linglib.Core.Probability.JointPosterior
import Linglib.Core.Probability.Entropy
import Linglib.Semantics.Modality.EpistemicProbability
import Mathlib.Probability.Distributions.Uniform

/-!
# [herbstritt-franke-2019]: complex probability expressions via RSA on `PMF`

Compositional threshold semantics plus an RSA model over an urn scenario
(`N = 10` balls), formalised on mathlib's `PMF` in the same key as
`Studies/LassiterGoodman2017PMF.lean`. Cognition 186 (2019) 50–71.

The architectural novelty is a Hellinger-distance speaker utility (Eq. 16) in
place of KL divergence. The literal listener `P_LL(s|m) ∝ ⟦m⟧(s) · P_prior(s)`
puts zero mass outside a meaning's extension, so `KL(P_rat.bel ‖ P_LL) = ∞`
whenever the speaker's belief has support outside it — a strictly probabilistic
speaker could never say "certainly RED" at 9/10. Hellinger distance is bounded
by 1, so the speaker can assert it with bounded disutility.

## Main definitions

* `obsKernel`, `speakerBelief` — belief formation (Eq. 12) as `PMF.posterior`
  of the hypergeometric observation kernel, with `ℚ`-valued mirrors
  `hypergeoQ` / `speakerBeliefQ` for finite-arithmetic checks.
* `SimpleExpr.meaning`, `complexMeaning` — threshold semantics for simple
  (Eq. 13-14) and nested (Eq. 22-23) probability expressions.
* `literalListener`, `pragmaticListener` — the RSA literal listener (uniform on
  a meaning extension, Eq. 15) and the pragmatic listener as a joint
  `PMF.posterior` (Eq. 18).

## Main results

* `hellinger_admits_what_KL_excludes` — on the witness pair `(pure 9, pure 10)`,
  `KL = ∞` but `HD ≤ 1`: the formal content of the Hellinger-vs-KL divergence,
  via `klDiv_eq_top_when_zero_support` and `hellingerDistSq_le_one`.
* `statePosterior_apply`, `accessPosterior_apply`, `statePosterior_lt_iff` —
  marginalisations (Eq. 19-20) of the joint posterior, direct corollaries of
  `Core/Probability/JointPosterior`.
* `certainly_subset_probably`, `probably_subset_possibly` — nesting of the
  inferred meaning extensions.

The cross-paper contrast with [goodman-stuhlmuller-2013] makes the
speaker-utility divergence (KL vs Hellinger) visible at theorem level. The paper's
posterior-predictive evaluation (JAGS fits, the model–data correlations of
Tables 6-10) is statistical, not structural, and is not formalised here.
-/

set_option autoImplicit false

namespace HerbstrittFranke2019

open scoped ENNReal

/-! ### Domain types -/

/-- Urn state: number of red balls in the urn (0..10). -/
abbrev UrnState := Fin 11

/-- The proportion of red balls: `s/10`. First-order probability of
    drawing a red ball, and the measure function for simple expressions. -/
def proportion (s : UrnState) : ℚ := s.val / 10

/-- Observation count (zero-padded for `access < 10`): obs > access have
    probability 0 in the kernel. -/
abbrev Obs := Fin 11

/-! ### Belief formation via the hypergeometric kernel

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

/-! ### `ℚ`-valued speaker belief for finite-arithmetic verification

Mirrors the existing file's `speakerBeliefQ` for `norm_num` checks. Bridge
to the PMF version: both reduce to the same hypergeometric ratio. -/

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
example : speakerBeliefQ 10 5 ⟨5, by omega⟩ = 1 := by
  simp only [speakerBeliefQ, hypergeoQ]
  norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Nat.choose]

/-- Full access: states other than the observed one get probability 0. -/
example : speakerBeliefQ 10 5 ⟨3, by omega⟩ = 0 := by
  simp only [speakerBeliefQ, hypergeoQ]
  norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Nat.choose]

/-- Partial access (a=4, o=1): belief spreads across feasible states. -/
example : speakerBeliefQ 4 1 ⟨5, by omega⟩ = 25/231 := by
  simp only [speakerBeliefQ, hypergeoQ]
  norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Nat.choose]

/-! ### Simple expression semantics -/

/-- Semantic threshold for "possibly" (posterior mean from Table 6). -/
def θ_possibly  : ℚ := 247/1000

/-- Semantic threshold for "probably" (posterior mean from Table 6). -/
def θ_probably  : ℚ := 549/1000

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

example : SimpleExpr.meaning .certainly ⟨10, by omega⟩ = true := by
  simp only [SimpleExpr.meaning, proportion, θ_certainly]; norm_num
example : SimpleExpr.meaning .certainly ⟨9, by omega⟩ = false := by
  simp only [SimpleExpr.meaning, proportion, θ_certainly]; norm_num
example : SimpleExpr.meaning .probably ⟨6, by omega⟩ = true := by
  simp only [SimpleExpr.meaning, proportion, θ_probably]; norm_num
example : SimpleExpr.meaning .probably ⟨5, by omega⟩ = false := by
  simp only [SimpleExpr.meaning, proportion, θ_probably]; norm_num
example : SimpleExpr.meaning .possibly ⟨3, by omega⟩ = true := by
  simp only [SimpleExpr.meaning, proportion, θ_possibly]; norm_num
example : SimpleExpr.meaning .possibly ⟨2, by omega⟩ = false := by
  simp only [SimpleExpr.meaning, proportion, θ_possibly]; norm_num
example : SimpleExpr.meaning .certainlyNot ⟨0, by omega⟩ = true := by
  simp only [SimpleExpr.meaning, proportion, θ_certainly]; norm_num
example : SimpleExpr.meaning .certainlyNot ⟨1, by omega⟩ = false := by
  simp only [SimpleExpr.meaning, proportion, θ_certainly]; norm_num
example : SimpleExpr.meaning .probablyNot ⟨4, by omega⟩ = true := by
  simp only [SimpleExpr.meaning, proportion, θ_probably]; norm_num
example : SimpleExpr.meaning .probablyNot ⟨5, by omega⟩ = false := by
  simp only [SimpleExpr.meaning, proportion, θ_probably]; norm_num

/-- Simple expression extensions are nested: certainly ⊂ probably ⊂ possibly. -/
theorem certainly_subset_probably :
    ∀ s : UrnState, SimpleExpr.meaning .certainly s = true →
    SimpleExpr.meaning .probably s = true := by
  intro s; fin_cases s <;>
    simp only [SimpleExpr.meaning, proportion, θ_certainly, θ_probably] <;> norm_num

theorem probably_subset_possibly :
    ∀ s : UrnState, SimpleExpr.meaning .probably s = true →
    SimpleExpr.meaning .possibly s = true := by
  intro s; fin_cases s <;>
    simp only [SimpleExpr.meaning, proportion, θ_probably, θ_possibly] <;> norm_num

/-! ### Compositional complex-expression semantics -/

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

example : complexMeaning .isCertainly .likely 10 8 = true := by
  simp only [complexMeaning, posteriorProb, InnerExpr.meaning, OuterMod.threshold,
    proportion, θ_probably, speakerBeliefQ, hypergeoQ]
  norm_num [Finset.sum_filter, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Nat.choose]
example : complexMeaning .isCertainly .likely 10 5 = false := by
  simp only [complexMeaning, posteriorProb, InnerExpr.meaning, OuterMod.threshold,
    proportion, θ_probably, speakerBeliefQ, hypergeoQ]
  norm_num [Finset.sum_filter, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Nat.choose]
example : complexMeaning .isCertainly .possible 4 2 = false := by
  simp only [complexMeaning, posteriorProb, InnerExpr.meaning, OuterMod.threshold,
    proportion, θ_possibly, speakerBeliefQ, hypergeoQ]
  norm_num [Finset.sum_filter, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Nat.choose]
example : complexMeaning .mightBe .possible 4 2 = true := by
  simp only [complexMeaning, posteriorProb, InnerExpr.meaning, OuterMod.threshold,
    proportion, θ_possibly, speakerBeliefQ, hypergeoQ]
  norm_num [Finset.sum_filter, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Nat.choose]

/-- For HF's specific thresholds, strict `>` and non-strict `≥` give the
    same extension on `UrnState` — no proportion s/10 (s ∈ {0,...,10})
    exactly equals any threshold. Justifies using `>` (paper Eq. 13) even
    when the theory-layer `nestedThreshold` uses `≥` (Fagin & Halpern). -/
theorem strict_threshold_equiv_ge :
    (∀ s : UrnState, proportion s > θ_certainly ↔ proportion s ≥ θ_certainly) ∧
    (∀ s : UrnState, proportion s > θ_probably ↔ proportion s ≥ θ_probably) ∧
    (∀ s : UrnState, proportion s > θ_possibly ↔ proportion s ≥ θ_possibly) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro s <;> fin_cases s <;>
    simp only [proportion, θ_certainly, θ_probably, θ_possibly] <;> norm_num

/-! ### RSA model on PMF

The literal listener `P_LL(s|m) ∝ ⟦m⟧(s) · P_prior(s)` is the uniform
distribution on the meaning extension (Eq. 15, with uniform prior). The
speaker normalises softmax-Hellinger scores (Eq. 16-17). The pragmatic
listener is `PMF.posterior` over the joint `(state × obs × access)` (Eq. 18). -/

/-- **Literal listener** (Eq. 15) for a meaning with non-empty extension:
    uniform on the extension. -/
noncomputable def literalListener (φ : UrnState → Bool)
    (h_nonempty : ((Finset.univ : Finset UrnState).filter (φ · = true)).Nonempty) :
    PMF UrnState :=
  PMF.uniformOfFinset ((Finset.univ : Finset UrnState).filter (φ · = true)) h_nonempty

/-- All five simple expressions have non-empty extensions under HF's
    inferred thresholds — every meaning admits a literal listener. -/
theorem simple_meaning_nonempty (u : SimpleExpr) :
    ((Finset.univ : Finset UrnState).filter (u.meaning · = true)).Nonempty := by
  cases u
  · exact ⟨⟨0, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleExpr.meaning, proportion, θ_certainly]; norm_num⟩  -- certainlyNot
  · exact ⟨⟨0, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleExpr.meaning, proportion, θ_probably]; norm_num⟩  -- probablyNot
  · exact ⟨⟨10, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleExpr.meaning, proportion, θ_possibly]; norm_num⟩  -- possibly
  · exact ⟨⟨10, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleExpr.meaning, proportion, θ_probably]; norm_num⟩  -- probably
  · exact ⟨⟨10, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleExpr.meaning, proportion, θ_certainly]; norm_num⟩  -- certainly

/-! ### Joint posterior marginalisations

The pragmatic listener is `P_PL(s, o, a | m)`; its marginals `P(s, o | m)`
(over access) and `P(s, a | m)` (over obs) are direct corollaries of
`Core/Probability/JointPosterior.lean`'s marginalisation theorems applied to
the joint posterior.

The structural form here works for *any* speaker kernel `S` and joint
prior over `(state × access)` — paper-specific instantiation is the
softmax-Hellinger speaker, which lives in the Hellinger-vs-KL section below. -/

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

/-! ### Hellinger vs KL: the architectural divergence point

HF's central methodological choice: KL divergence makes any message whose
extension fails to cover the speaker's belief support have infinite
disutility, so the speaker can never consider it. Hellinger distance is
uniformly bounded by 1, so all messages have bounded disutility.

The two theorems below witness this directly:
- `klDiv_eq_top_when_zero_support`: KL = ∞ whenever some support point of `P`
  has zero mass under `Q`.
- `hellingerDistSq_le_one`: H² ≤ 1 always, so HD ≤ 1.

Together they make the architectural divergence visible at theorem level:
there exist `(P, Q)` pairs where KL-utility excludes `Q` as a message choice
but Hellinger-utility admits it. -/

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

/-!
### Architectural contrast with [goodman-stuhlmuller-2013]

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

`hellinger_admits_what_KL_excludes` makes this difference visible:
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

/-! ### Modal concord and `might be possible`

The paper finds that the compositional model **underpredicts** how often
speakers choose "might be possible": although its truth condition is weak
(posterior probability of "possible" exceeds `θ_might = 0.332`), the pragmatic
speaker prefers logically stronger messages and so assigns the doubly-hedged
form a low choice rate — yet participants select it far more often than
predicted. A **modal concord** reading, collapsing the two modals to a single
"possible" [zeijlstra-2007], would close the gap. Qualitative; not formalised
here. -/

end HerbstrittFranke2019
