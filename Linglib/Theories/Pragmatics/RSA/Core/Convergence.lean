/-
# RSA Convergence Theory

Proves that RSA dynamics converge by showing G_α is monotonically increasing.

## Results

1. Concavity: G_α is concave in S (fixed L) and concave in L (fixed S)
2. Alternating maximization: RSA speaker/listener updates maximize G_α
3. Monotonicity: G_α(S_t, L_t) ≤ G_α(S_{t+1}, L_{t+1}) for all t
4. Convergence: RSA dynamics converge to a fixed point

These results guarantee that RSA predictions are well-defined: the iterative
reasoning process converges rather than oscillating or diverging.

## References

- Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of human
  pragmatic reasoning. Proposition 1.
- Csiszár, I. & Tusnády, G. (1984). Information geometry and alternating
  minimization procedures.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Basic
import Linglib.Theories.Pragmatics.RSA.Core.GibbsVariational
import Mathlib.Topology.Order.MonotoneConvergence

namespace RSA.Convergence

open Real Classical Finset


/--
RSA scenario with real-valued α for convergence proofs.

This is the mathematical version used for proving convergence.
For computation, use `RSAScenario` from Core.lean.
-/
structure RSAScenarioR where
  /-- Finite type of meanings/worlds -/
  M : Type*
  /-- Finite type of utterances -/
  U : Type*
  /-- Fintype instances -/
  [finM : Fintype M]
  [finU : Fintype U]
  /-- Prior over meanings -/
  prior : M → ℝ
  prior_nonneg : ∀ m, 0 ≤ prior m
  prior_pos : ∃ m, 0 < prior m
  prior_sum : ∑ m, prior m = 1
  /-- Lexicon: applicability of utterance to meaning -/
  lexicon : U → M → ℝ
  lexicon_nonneg : ∀ u m, 0 ≤ lexicon u m
  /-- Rationality parameter -/
  α : ℝ
  α_nonneg : 0 ≤ α

attribute [instance] RSAScenarioR.finM RSAScenarioR.finU


/-- Normalization constant (partition function). -/
noncomputable def Z {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  ∑ a, f a

/-- Normalized distribution. -/
noncomputable def normalize {α : Type*} [Fintype α] (f : α → ℝ) (a : α) : ℝ :=
  if Z f = 0 then 0 else f a / Z f

/-- Shannon entropy H(X) = -Σ p(x) log p(x). -/
noncomputable def entropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ a, if p a = 0 then 0 else p a * log (p a)

/-- Literal listener: L₀(m|u) ∝ lexicon(u,m) · prior(m) -/
noncomputable def L0 (S : RSAScenarioR) (u : S.U) (m : S.M) : ℝ :=
  S.lexicon u m * S.prior m

/-- Speaker utility: V_L(m,u) = log L(m|u) -/
noncomputable def utility {S : RSAScenarioR} (L : S.U → S.M → ℝ) (m : S.M) (u : S.U) : ℝ :=
  if L u m ≤ 0 then 0 else log (L u m)

/-- Pragmatic speaker: S(u|m) ∝ L(m|u)^α -/
noncomputable def speakerScore (S : RSAScenarioR) (L : S.U → S.M → ℝ)
    (m : S.M) (u : S.U) : ℝ :=
  if L u m ≤ 0 then 0 else (L u m).rpow S.α

-- Softmax-based speaker (inherits all softmax properties)

/-- Pragmatic speaker as softmax (normalized distribution).

  S(u|m) = softmax(utility(·, m), α)(u)

By defining RSA speaker via softmax, all softmax properties
(sum to 1, positivity, odds, limits) transfer directly.

The `utility` function is defined above as `log L(m|u)` when `L > 0`.
For full RSA with cost, use `utility - cost` as the score function.
-/
noncomputable def speakerSoftmax (S : RSAScenarioR) (L : S.U → S.M → ℝ) (m : S.M) : S.U → ℝ :=
  Softmax.softmax (λ u => utility L m u) S.α

/-- Speaker softmax sums to 1 (valid probability distribution). -/
theorem speakerSoftmax_sum_one (S : RSAScenarioR) [Nonempty S.U] (L : S.U → S.M → ℝ) (m : S.M) :
    ∑ u, speakerSoftmax S L m u = 1 :=
  Softmax.softmax_sum_eq_one _ S.α

/-- Speaker softmax is positive. -/
theorem speakerSoftmax_pos (S : RSAScenarioR) [Nonempty S.U] (L : S.U → S.M → ℝ) (m : S.M) (u : S.U) :
    0 < speakerSoftmax S L m u :=
  Softmax.softmax_pos _ S.α u

/-- Speaker softmax probability ratio from utility differences.

  S(u₁|m) / S(u₂|m) = exp(α · (utility(u₁, m) - utility(u₂, m)))

This is Fact 2 from Franke & Degen: odds determined by score differences.
-/
theorem speakerSoftmax_odds (S : RSAScenarioR) [Nonempty S.U] (L : S.U → S.M → ℝ) (m : S.M) (u₁ u₂ : S.U) :
    speakerSoftmax S L m u₁ / speakerSoftmax S L m u₂ =
    Real.exp (S.α * (utility L m u₁ - utility L m u₂)) :=
  Softmax.softmax_odds _ S.α u₁ u₂

/-- At α = 0, speaker is uniform (ignores utility entirely). -/
theorem speakerSoftmax_zero (S : RSAScenarioR) [Nonempty S.U] (L : S.U → S.M → ℝ) (m : S.M)
    (hα : S.α = 0) :
    speakerSoftmax S L m = λ _ => 1 / (Fintype.card S.U : ℝ) := by
  simp only [speakerSoftmax, hα]
  exact Softmax.softmax_zero _

/-- Higher utility → higher speaker probability (for α > 0). -/
theorem speakerSoftmax_mono (S : RSAScenarioR) [Nonempty S.U] (L : S.U → S.M → ℝ)
    (hα : 0 < S.α) (m : S.M) (u₁ u₂ : S.U)
    (h : utility L m u₁ ≤ utility L m u₂) :
    speakerSoftmax S L m u₁ ≤ speakerSoftmax S L m u₂ :=
  Softmax.softmax_mono _ hα u₁ u₂ h

/-- Pragmatic listener score: L_score(m, u) = P(m) · S(u|m).

    The speaker S(u|m) must already be a proper probability distribution
    (non-negative, sums to 1). The listener does NOT renormalize the speaker.
    This is correct because `speakerUpdate` returns `speakerSoftmax`, which is
    already normalized by construction. -/
noncomputable def listenerScore (S : RSAScenarioR) (Spk : S.M → S.U → ℝ)
    (u : S.U) (m : S.M) : ℝ :=
  S.prior m * Spk m u


/-!
## The RSA Objective Function G_α

RSA dynamics implicitly optimize an objective function G_α (Zaslavsky et al. 2020):

  G_α(S, L) = H_S(U|M) + α · E_S[V_L]

where:
- H_S(U|M) = Speaker's conditional entropy = Σₘ P(m) · H(S(·|m)).
  This measures the "cost" of the speaker's lexicon. Lower entropy means more
  deterministic (easier to produce) utterances.

- E_S[V_L] = Expected listener utility = Σₘ,ᵤ P(m) S(u|m) log L(m|u).
  This measures how well the listener can recover the intended meaning.

- α = Rationality parameter controlling the cost/informativity tradeoff.
  - α = 0: Maximum entropy (speaker ignores listener)
  - α = 1: Rate-distortion optimum (information-theoretic balance)
  - α → ∞: NeoGricean limit (maximum informativity)

## Why RSA Converges

G_α is concave in both S (for fixed L) and L (for fixed S). Since RSA
alternately maximizes over S and L, this is an instance of alternating
maximization which converges to a fixed point.

G_α balances two pressures:
1. Compression (H_S): Keep utterances simple/predictable
2. Communication (E_S[V_L]): Help the listener understand

The rationality parameter α controls which pressure dominates.
-/

/-- Speaker's conditional entropy H_S(U|M).

This measures the "cost" of the speaker's utterance distribution.
Lower entropy = more predictable (less costly) choices. -/
noncomputable def H_S (S : RSAScenarioR) (Spk : S.M → S.U → ℝ) : ℝ :=
  ∑ m, S.prior m * entropy (λ u => normalize (Spk m) u)

/-- Expected listener utility E_S[V_L].

This measures how well the listener recovers the speaker's intended meaning.
Higher utility = better communication. -/
noncomputable def E_VL (S : RSAScenarioR) (Spk : S.M → S.U → ℝ)
    (L : S.U → S.M → ℝ) : ℝ :=
  ∑ m, ∑ u, S.prior m * normalize (Spk m) u * utility L m u

/--
**The RSA Objective**: G_α(S,L) = H_S(U|M) + α · E_S[V_L]

This is the function that RSA dynamics maximize. RSA convergence follows from:
1. G_α is concave in S (for fixed L)
2. G_α is concave in L (for fixed S)
3. G_α is bounded above (by log |U|)
4. RSA alternately maximizes over S and L

Therefore G_α is monotonically non-decreasing and bounded, so it converges.
-/
noncomputable def G_α (S : RSAScenarioR) (Spk : S.M → S.U → ℝ)
    (L : S.U → S.M → ℝ) : ℝ :=
  H_S S Spk + S.α * E_VL S Spk L


/-- One step of RSA dynamics: given listener L, compute optimal speaker.

    Returns the softmax distribution (already normalized, sums to 1, positive).
    The speaker is responsible for normalizing its own output — the listener
    does NOT renormalize. -/
noncomputable def speakerUpdate (S : RSAScenarioR) [Nonempty S.U] (L : S.U → S.M → ℝ)
    (m : S.M) (u : S.U) : ℝ :=
  speakerSoftmax S L m u

/-- One step of RSA dynamics: given speaker S, compute optimal listener. -/
noncomputable def listenerUpdate (S : RSAScenarioR) (Spk : S.M → S.U → ℝ)
    (u : S.U) (m : S.M) : ℝ :=
  normalize (λ m' => listenerScore S Spk u m') m

/-- RSA state: a speaker-listener pair. -/
structure RSAState (S : RSAScenarioR) where
  speaker : S.M → S.U → ℝ
  listener : S.U → S.M → ℝ

/-- Initialize RSA from literal listener. -/
noncomputable def initRSA (S : RSAScenarioR) [Nonempty S.U] : RSAState S where
  speaker := speakerSoftmax S (L0 S)
  listener := λ u m => normalize (λ m' => L0 S u m') m

/-- One full step of RSA dynamics. -/
noncomputable def stepRSA (S : RSAScenarioR) [Nonempty S.U] (state : RSAState S) : RSAState S where
  speaker := speakerUpdate S state.listener
  listener := listenerUpdate S (speakerUpdate S state.listener)

/-- RSA dynamics after n iterations. -/
noncomputable def iterateRSA (S : RSAScenarioR) [Nonempty S.U] (n : ℕ) : RSAState S :=
  (stepRSA S)^[n] (initRSA S)


/-!
## G_α Concavity

The function `negMulLog x = -x * log x` is concave on [0, ∞) (Mathlib: `concaveOn_negMulLog`).
Since entropy H(p) = Σᵢ negMulLog(pᵢ), entropy is concave in p.

Therefore:
- G_α[S, L] = H_S(U|M) + α·E_S[V_L]
- H_S(U|M) = Σₘ P(m) · H(S(·|m)) is concave in S (sum of concave)
- E_S[V_L] is linear in S
- G_α is concave in S (for fixed L)

Similarly, log is concave, so G_α is concave in L (for fixed S).
-/

/-- negMulLog is concave on [0, ∞). -/
theorem negMulLog_concave : ConcaveOn ℝ (Set.Ici (0 : ℝ)) Real.negMulLog :=
  Real.concaveOn_negMulLog

/-- Log is concave on (0, ∞). -/
theorem log_concave : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
  strictConcaveOn_log_Ioi.concaveOn

/-- Projection is a linear map: p ↦ p(i) is linear. -/
def projLinearMap {α : Type*} (i : α) : (α → ℝ) →ₗ[ℝ] ℝ where
  toFun p := p i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- negMulLog composed with projection is concave. -/
theorem negMulLog_proj_concave {α : Type*} (i : α) :
    ConcaveOn ℝ {p : α → ℝ | 0 ≤ p i} (λ p => Real.negMulLog (p i)) := by
  have h1 : ConcaveOn ℝ (Set.Ici (0 : ℝ)) Real.negMulLog := Real.concaveOn_negMulLog
  have h2 := h1.comp_linearMap (projLinearMap i)
  have hset : {p : α → ℝ | 0 ≤ p i} = projLinearMap i ⁻¹' Set.Ici 0 := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
    rfl
  have hfun : (λ p => Real.negMulLog (p i)) = Real.negMulLog ∘ projLinearMap i := by
    ext p
    simp only [Function.comp_apply]
    rfl
  rw [hset, hfun]
  exact h2

/-- Helper: The constraint set {p | ∀ i, 0 ≤ p i} is convex. -/
theorem convex_nonneg_functions {α : Type*} :
    Convex ℝ {p : α → ℝ | ∀ i, 0 ≤ p i} := by
  intro x hx y hy a b ha hb _hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  intro i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : a * x i ≥ 0 := mul_nonneg ha (hx i)
  have h2 : b * y i ≥ 0 := mul_nonneg hb (hy i)
  linarith

/-- Helper: Finite sum of concave functions is concave (over a Finset). -/
theorem concaveOn_finset_sum' {α : Type*} {E : Type*}
    [AddCommGroup E] [Module ℝ E] {s : Set E} (hs : Convex ℝ s)
    (f : α → E → ℝ) (F : Finset α) (hf : ∀ i ∈ F, ConcaveOn ℝ s (f i)) :
    ConcaveOn ℝ s (λ x => ∑ i ∈ F, f i x) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact concaveOn_const 0 hs
  | @insert a F' ha ih =>
    simp only [Finset.sum_insert ha]
    have hfa : ConcaveOn ℝ s (f a) := hf a (Finset.mem_insert_self a F')
    have hrest : ConcaveOn ℝ s (λ x => ∑ i ∈ F', f i x) :=
      ih (λ i hi => hf i (Finset.mem_insert_of_mem hi))
    exact hfa.add hrest

/-- Helper: Finite sum of concave functions is concave (over a Fintype). -/
theorem concaveOn_finset_sum {α : Type*} [Fintype α] {E : Type*}
    [AddCommGroup E] [Module ℝ E] {s : Set E} (hs : Convex ℝ s)
    (f : α → E → ℝ) (hf : ∀ i, ConcaveOn ℝ s (f i)) :
    ConcaveOn ℝ s (λ x => ∑ i, f i x) := by
  apply concaveOn_finset_sum' hs f Finset.univ
  intro i _
  exact hf i

/-- Entropy is concave: H(p) = Σᵢ negMulLog(pᵢ) is concave in p. -/
theorem entropy_concave_on_simplex {α : Type*} [Fintype α] :
    ConcaveOn ℝ {p : α → ℝ | ∀ i, 0 ≤ p i}
      (λ p => ∑ i, Real.negMulLog (p i)) := by
  apply concaveOn_finset_sum convex_nonneg_functions
  intro i
  apply ConcaveOn.subset (negMulLog_proj_concave i)
  · intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    exact hp i
  · exact convex_nonneg_functions

/-- Weighted sum of concave functions is concave. -/
theorem weighted_sum_concave {α : Type*} [Fintype α] {E : Type*}
    [AddCommGroup E] [Module ℝ E] {s : Set E} (hs : Convex ℝ s)
    (f : α → E → ℝ) (w : α → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i, ConcaveOn ℝ s (f i)) :
    ConcaveOn ℝ s (λ x => ∑ i, w i * f i x) := by
  apply concaveOn_finset_sum hs
  intro i
  have h := (hf i).smul (hw i)
  have heq : (λ x => w i * f i x) = w i • f i := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact h


/--
Proposition 1, Part 1 (Zaslavsky et al.): G_α is concave in S for fixed L.

On the probability simplex (where Σ_u Spk m u = 1 and Spk m u ≥ 0):
- normalize(Spk m) = Spk m (no normalization needed)
- H_S = Σ_m P(m) · entropy(Spk m) is weighted sum of entropies → concave
- E_VL = Σ_m,u P(m) · Spk(m,u) · V(L,m,u) is linear in Spk → concave
- G_α = H_S + α·E_VL is sum of concave functions → concave
-/
theorem G_α_concave_in_S (S : RSAScenarioR) (L : S.U → S.M → ℝ) :
    ConcaveOn ℝ {Spk | (∀ m u, 0 ≤ Spk m u) ∧ (∀ m, ∑ u, Spk m u = 1)}
      (λ Spk => G_α S Spk L) := by
  -- Define the simplex domain
  let D := {Spk : S.M → S.U → ℝ | (∀ m u, 0 ≤ Spk m u) ∧ (∀ m, ∑ u, Spk m u = 1)}
  -- The simplex is convex
  have hD_convex : Convex ℝ D := by
    intro x hx y hy a b ha hb hab
    constructor
    · -- Non-negativity: a * x m u + b * y m u ≥ 0
      intro m u
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hx.1 m u)) (mul_nonneg hb (hy.1 m u))
    · -- Sum to 1: Σ_u (a * x m u + b * y m u) = 1
      intro m
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [hx.2 m, hy.2 m]
      linarith
  -- On the simplex, normalize(Spk m) = Spk m
  have hnorm_eq : ∀ Spk ∈ D, ∀ m u, normalize (Spk m) u = Spk m u := by
    intro Spk hSpk m u
    unfold normalize Z
    have hsum : ∑ v, Spk m v = 1 := hSpk.2 m
    have hne : ∑ a, Spk m a ≠ 0 := by rw [hsum]; exact one_ne_zero
    rw [if_neg hne, hsum, div_one]
  -- H_S on the simplex: H_S(Spk) = Σ_m P(m) · entropy(Spk m)
  -- This is a weighted sum of entropies, which is concave
  have hH_concave : ConcaveOn ℝ D (λ Spk => H_S S Spk) := by
    unfold H_S
    -- For each m, entropy(normalize(Spk m)) = entropy(Spk m) on simplex
    -- entropy(Spk m) is concave in Spk m
    -- Weighted sum with P(m) ≥ 0 preserves concavity
    apply weighted_sum_concave hD_convex
    · exact S.prior_nonneg
    · intro m
      -- Need: Spk ↦ entropy(normalize(Spk m)) is concave on D
      -- On D, this equals entropy(Spk m)
      -- First, show entropy equals ∑ negMulLog on non-negative inputs
      have hentropy_eq : ∀ p : S.U → ℝ, (∀ u, 0 ≤ p u) →
          entropy p = ∑ u, Real.negMulLog (p u) := by
        intro p hp
        unfold entropy Real.negMulLog
        simp only [neg_mul]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro u _
        by_cases hpu : p u = 0
        · simp only [hpu, Real.log_zero, mul_zero, neg_zero, ite_true]
        · simp only [hpu, ↓reduceIte]
      -- entropy is concave (via entropy_concave_on_simplex)
      have hentropy_concave : ConcaveOn ℝ {p : S.U → ℝ | ∀ u, 0 ≤ p u}
          (λ p => entropy p) := by
        apply ConcaveOn.congr entropy_concave_on_simplex
        intro p hp
        exact (hentropy_eq p hp).symm
      -- Now compose with projection Spk ↦ Spk m
      -- The projection is linear, and D projects into {p | ∀ u, 0 ≤ p u}
      let nonneg_fns := {q : S.U → ℝ | ∀ v, 0 ≤ q v}
      let proj_fn : (S.M → S.U → ℝ) → (S.U → ℝ) := λ spkFn => spkFn m
      have hD_proj : D ⊆ proj_fn ⁻¹' nonneg_fns := by
        intro spkFn hspkFn
        simp only [Set.mem_preimage]
        exact hspkFn.1 m
      -- On D, normalize(Spk m) = Spk m, so entropy(normalize(Spk m)) = entropy(Spk m)
      have heq_on_D : ∀ spkFn ∈ D, entropy (normalize (spkFn m)) = entropy (spkFn m) := by
        intro spkFn hspkFn
        congr 1
        ext v
        exact hnorm_eq spkFn hspkFn m v
      -- Compose: spkFn ↦ entropy(spkFn m) is concave
      have hcomp : ConcaveOn ℝ (proj_fn ⁻¹' nonneg_fns)
          (λ spkFn => entropy (spkFn m)) := by
        -- projection is linear
        let proj_m : (S.M → S.U → ℝ) →ₗ[ℝ] (S.U → ℝ) := {
          toFun := λ spkFn => spkFn m
          map_add' := λ _ _ => rfl
          map_smul' := λ _ _ => rfl
        }
        exact hentropy_concave.comp_linearMap proj_m
      -- Restrict to D and use heq_on_D
      have hrestrict : ConcaveOn ℝ D (λ spkFn => entropy (spkFn m)) :=
        hcomp.subset hD_proj hD_convex
      exact hrestrict.congr (λ spkFn hspkFn => (heq_on_D spkFn hspkFn).symm)
  -- E_VL on the simplex is linear in Spk (hence concave)
  have hE_concave : ConcaveOn ℝ D (λ Spk => E_VL S Spk L) := by
    unfold E_VL
    -- E_VL = Σ_m Σ_u P(m) · normalize(Spk m)(u) · utility(L, m, u)
    -- On D, normalize(Spk m)(u) = Spk m u, so:
    -- E_VL = Σ_m Σ_u P(m) · Spk m u · V(m,u)
    -- This is a linear function of Spk (weighted sum with fixed coefficients)
    -- Linear functions are concave
    have hlinear : ∀ Spk ∈ D, E_VL S Spk L =
        ∑ m, ∑ u, S.prior m * Spk m u * utility L m u := by
      intro Spk hSpk
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro u _
      rw [hnorm_eq Spk hSpk m u]
    -- A linear function is concave
    apply ConcaveOn.congr _ (λ Spk hSpk => (hlinear Spk hSpk).symm)
    -- The function Σ_m Σ_u c(m,u) * Spk m u is linear, hence concave
    apply concaveOn_finset_sum' hD_convex
    intro m _
    apply concaveOn_finset_sum' hD_convex
    intro u _
    -- Spk ↦ c * Spk m u is linear (concave) for c = P(m) * V(m,u)
    -- The coefficient could be negative (if V < 0), but linear is still concave
    have hlinear_comp : ConcaveOn ℝ D (λ Spk => S.prior m * Spk m u * utility L m u) := by
      -- This is: (const) * (linear projection) which is affine, hence concave
      constructor
      · exact hD_convex
      · intro x _hx y _hy a b _ha _hb _hab
        -- Need: a • f(x) + b • f(y) ≤ f(a • x + b • y)
        -- For linear f, we have equality
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        -- LHS = a * (prior * x m u * V) + b * (prior * y m u * V)
        -- RHS = prior * (a * x m u + b * y m u) * V
        -- These are equal by distributivity, so ≤ holds
        ring_nf
        exact le_refl _
    exact hlinear_comp
  -- G_α = H_S + α · E_VL
  unfold G_α
  have hα_nonneg : 0 ≤ S.α := S.α_nonneg
  exact hH_concave.add (hE_concave.smul hα_nonneg)

/--
Proposition 1, Part 2 (Zaslavsky et al.): G_α is concave in L for fixed S.

Proof:
- H_S(Spk) does not depend on L → constant → concave
- E_VL = Σ P(m)·S(u|m)·log(L(u,m)) is weighted sum of logs
- log is concave on (0,∞) by `strictConcaveOn_log_Ioi`
- Weighted sum of concave functions (with non-negative weights) is concave
- G_α = H_S + α·E_VL is sum of concave functions → concave
-/
theorem G_α_concave_in_L (S : RSAScenarioR) (Spk : S.M → S.U → ℝ)
    (hSpk_nonneg : ∀ m u, 0 ≤ Spk m u) :
    ConcaveOn ℝ {L | ∀ u m, 0 < L u m}
      (λ L => G_α S Spk L) := by
  -- The domain {L | ∀ u m, 0 < L u m} is convex
  have hD_convex : Convex ℝ {L : S.U → S.M → ℝ | ∀ u m, 0 < L u m} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    intro u m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : 0 ≤ a * x u m := mul_nonneg ha (le_of_lt (hx u m))
    have h2 : 0 ≤ b * y u m := mul_nonneg hb (le_of_lt (hy u m))
    -- At least one of a, b is positive (since a + b = 1)
    by_cases ha' : 0 < a
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hx u m)) h2
    · push_neg at ha'
      have ha_zero : a = 0 := le_antisymm ha' ha
      have hb_pos : 0 < b := by linarith
      rw [ha_zero, zero_mul, zero_add]
      exact mul_pos hb_pos (hy u m)
  -- Define the domain for clarity
  let D := {Lis : S.U → S.M → ℝ | ∀ u m, 0 < Lis u m}
  -- H_S is constant in L, hence concave
  have hH_concave : ConcaveOn ℝ D (λ _ => H_S S Spk) :=
    concaveOn_const (H_S S Spk) hD_convex
  -- For the E_VL term, we need log concavity
  -- utility Lis m u = log (Lis u m) when Lis u m > 0
  -- E_VL = Σ_m Σ_u P(m) · norm_Spk(m,u) · log(Lis u m)
  -- This is a weighted sum of logs, which is concave
  -- The full proof requires showing each log(Lis u m) is concave in Lis
  -- via composition with the projection Lis ↦ Lis u m
  have hE_concave : ConcaveOn ℝ D (λ Lis => E_VL S Spk Lis) := by
    -- E_VL = Σ_m Σ_u w(m,u) · utility(Lis, m, u)
    -- On D, utility(Lis, m, u) = log(Lis u m)
    -- Step 1: Show each (Lis ↦ utility Lis m u) is concave on D
    have h_utility_concave : ∀ m u, ConcaveOn ℝ D (λ Lis => utility Lis m u) := by
      intro m u
      -- On D, utility Lis m u = log (Lis u m)
      -- The evaluation map eval_{u,m} : Lis ↦ Lis u m is linear
      -- log is concave on (0, ∞)
      -- Therefore log ∘ eval is concave
      have hlog_concave : ConcaveOn ℝ (Set.Ioi 0) Real.log :=
        strictConcaveOn_log_Ioi.concaveOn
      -- Define the evaluation functional
      let eval_um : (S.U → S.M → ℝ) →ₗ[ℝ] ℝ := {
        toFun := λ Lis => Lis u m
        map_add' := λ _ _ => rfl
        map_smul' := λ _ _ => rfl
      }
      -- log ∘ eval is concave on eval⁻¹(Ioi 0)
      have hcomp : ConcaveOn ℝ (eval_um ⁻¹' Set.Ioi 0) (Real.log ∘ eval_um) :=
        hlog_concave.comp_linearMap eval_um
      -- D ⊆ eval⁻¹(Ioi 0) for all u, m
      have hsubset : D ⊆ eval_um ⁻¹' Set.Ioi 0 := by
        intro Lis hLis
        simp only [Set.mem_preimage, Set.mem_Ioi]
        exact hLis u m
      -- Restrict to D
      have hcomp_D : ConcaveOn ℝ D (Real.log ∘ eval_um) :=
        hcomp.subset hsubset hD_convex
      -- On D, utility Lis m u = log(Lis u m) = (log ∘ eval_um) Lis
      have heq : Set.EqOn (λ Lis => utility Lis m u) (Real.log ∘ eval_um) D := by
        intro Lis hLis
        simp only [Function.comp_apply, utility]
        rw [if_neg (not_le.mpr (hLis u m))]
        -- eval_um Lis = Lis u m by definition of eval_um
        rfl
      -- Transfer concavity via Set.EqOn
      exact hcomp_D.congr heq.symm
    -- Step 2: Weighted sum preserves concavity
    -- E_VL = Σ_m Σ_u (prior m * norm_Spk m u) * utility Lis m u
    unfold E_VL
    -- Rewrite as sum of weighted concave functions
    apply concaveOn_finset_sum' hD_convex
    intro m _
    apply concaveOn_finset_sum' hD_convex
    intro u _
    -- Weight is P(m) * normalize(Spk m)(u) ≥ 0
    have hw_nonneg : 0 ≤ S.prior m * normalize (Spk m) u := by
      apply mul_nonneg (S.prior_nonneg m)
      unfold normalize Z
      split_ifs with hZ
      · exact le_refl 0
      · -- Spk m u / Σ Spk m ≥ 0 when Spk m u ≥ 0 and sum ≥ 0
        apply div_nonneg (hSpk_nonneg m u)
        exact Finset.sum_nonneg (λ v _ => hSpk_nonneg m v)
    exact (h_utility_concave m u).smul hw_nonneg
  -- G_α = H_S + α · E_VL
  -- H_S is constant (concave), α · E_VL is concave (α ≥ 0)
  unfold G_α
  have hα_nonneg : 0 ≤ S.α := S.α_nonneg
  have hαE_concave : ConcaveOn ℝ D (λ Lis => S.α * E_VL S Spk Lis) :=
    hE_concave.smul hα_nonneg
  exact hH_concave.add hαE_concave


/-!
## KKT Conditions

For fixed L, the speaker optimization problem is:
  max_S  G_α(S, L) = Σ_m P(m) [Σ_u negMulLog(S(u|m)) + α · Σ_u S(u|m) · V_L(m,u)]
  s.t.   Σ_u S(u|m) = 1 for all m
         S(u|m) ≥ 0

The Lagrangian is:
  L(S, λ) = G_α(S, L) - Σ_m λ_m (Σ_u S(u|m) - 1)

First-order condition (for interior S(u|m) > 0):
  ∂L/∂S(u|m) = P(m) · (∂negMulLog/∂s + α · V_L(m,u)) - λ_m = 0
             = P(m) · (-log S(u|m) - 1 + α · log L(m|u)) - λ_m = 0

Solving for S(u|m):
  log S(u|m) = α · log L(m|u) - 1 - λ_m/P(m)
  S(u|m) = L(m|u)^α · exp(-1 - λ_m/P(m))
  S(u|m) ∝ L(m|u)^α

This is the RSA speaker update. By concavity of G_α in S,
this stationary point is the global maximum.

Mathlib lemmas used:
- `Real.hasDerivAt_negMulLog`: d/dx(negMulLog x) = -log x - 1
- `Real.deriv_negMulLog`: Same in deriv form
- Concavity from Part 6 ensures stationary point is maximum
-/

/--
The per-meaning objective for the speaker optimization.

For fixed meaning m and listener L, this is the function the speaker maximizes:
  f_m(s) = Σ_u [negMulLog(s_u) + α · s_u · log L(m|u)]
-/
noncomputable def speakerObjective (S : RSAScenarioR) (L : S.U → S.M → ℝ)
    (m : S.M) (s : S.U → ℝ) : ℝ :=
  ∑ u, (Real.negMulLog (s u) + S.α * s u * utility L m u)

/--
Derivative of the per-meaning speaker objective with respect to s_u.

Using Mathlib's `Real.deriv_negMulLog`:
  ∂/∂s_u [negMulLog(s_u) + α · s_u · V] = -log(s_u) - 1 + α · V
-/
theorem deriv_speakerObjective_component (S : RSAScenarioR) (L : S.U → S.M → ℝ)
    (m : S.M) (u : S.U) (s_u : ℝ) (hs : s_u ≠ 0) (_hs_pos : 0 < s_u)
    (_hL : 0 < L u m) :
    HasDerivAt (λ x => Real.negMulLog x + S.α * x * utility L m u)
               (-Real.log s_u - 1 + S.α * utility L m u)
               s_u := by
  -- negMulLog has derivative -log x - 1 by Real.hasDerivAt_negMulLog
  have h1 : HasDerivAt Real.negMulLog (-Real.log s_u - 1) s_u :=
    Real.hasDerivAt_negMulLog hs
  -- The linear term α * x * V has derivative α * V
  have h2 : HasDerivAt (λ x => S.α * x * utility L m u) (S.α * utility L m u) s_u := by
    have hid : HasDerivAt (λ x => x) 1 s_u := hasDerivAt_id s_u
    have hmul : HasDerivAt (λ x => S.α * x) S.α s_u := by
      simpa using hid.const_mul S.α
    exact hmul.mul_const (utility L m u)
  -- Sum of derivatives: (-log s_u - 1) + (α * V) = -log s_u - 1 + α * V
  exact h1.add h2

/--
The RSA speaker update satisfies the first-order optimality condition.

At s_u = L(m|u)^α (normalized), the derivative equals a constant across all u
(the Lagrange multiplier). This is the KKT stationarity condition.

For s_u ∝ L(m|u)^α, we have:
  -log s_u - 1 + α·log L(m|u) = -log(L(m|u)^α / Z) - 1 + α·log L(m|u)
                               = -α·log L(m|u) + log Z - 1 + α·log L(m|u)
                               = log Z - 1  (constant!)

So all components have the same derivative value, satisfying KKT.
-/
theorem rsa_speaker_satisfies_foc (S : RSAScenarioR) (L : S.U → S.M → ℝ)
    (m : S.M) (hL : ∀ u, 0 < L u m) :
    let s_rsa := λ u => speakerScore S L m u
    let Zsum := ∑ u, s_rsa u
    Zsum ≠ 0 →
    ∀ u, s_rsa u / Zsum > 0 →
         -- The derivative at s_norm: -log(s_norm) - 1 + α·V
         -- For RSA: s_norm = L(m|u)^α / Z, so -log(s_norm) = -α·log L(m|u) + log Z
         -- Therefore: -log(s_norm) - 1 + α·log L(m|u) = log Z - 1 (constant!)
         -Real.log (s_rsa u / Zsum) - 1 + S.α * utility L m u = Real.log Zsum - 1 := by
  intro s_rsa Zsum hZ u hs_pos
  -- Expand utility: V(u,m) = log L(m|u) when L > 0
  have hutil : utility L m u = Real.log (L u m) := by
    simp only [utility]
    rw [if_neg (not_le.mpr (hL u))]
  rw [hutil]
  -- s_rsa u = speakerScore = L(m|u)^α (when L(m|u) > 0)
  have hspk : s_rsa u = (L u m).rpow S.α := by
    -- s_rsa is definitionally speakerScore S L m, so we need to show
    -- speakerScore S L m u = (L u m).rpow S.α
    show speakerScore S L m u = (L u m).rpow S.α
    simp only [speakerScore]
    rw [if_neg (not_le.mpr (hL u))]
  rw [hspk]
  -- Positivity facts
  have hLpos : 0 < L u m := hL u
  have hrpow_pos : 0 < (L u m).rpow S.α := Real.rpow_pos_of_pos hLpos S.α
  have hZpos : 0 < Zsum := by
    by_contra h
    push_neg at h
    have hsum_nonneg : 0 ≤ Zsum := Finset.sum_nonneg (λ v _ => by
      show 0 ≤ speakerScore S L m v
      simp only [speakerScore]
      split_ifs with hv
      · exact le_refl 0
      · push_neg at hv
        exact le_of_lt (Real.rpow_pos_of_pos hv S.α))
    exact hZ (le_antisymm h hsum_nonneg)
  -- -log(L^α / Z) = -log(L^α) + log Z = -α·log L + log Z
  rw [Real.log_div (ne_of_gt hrpow_pos) (ne_of_gt hZpos)]
  -- log(x.rpow α) = α * log x for x > 0
  have hlog_rpow : Real.log ((L u m).rpow S.α) = S.α * Real.log (L u m) :=
    Real.log_rpow hLpos S.α
  rw [hlog_rpow]
  ring

/-!
### Replacing the KKT Axioms with Gibbs Variational Principle

The original formalization used KKT sufficiency axioms to establish that
RSA updates maximize G_α. We now prove these directly using the
Gibbs Variational Principle (proved in Softmax/Basic.lean):

- **Speaker**: softmax maximizes H(p) + α⟨p, s⟩ → gibbs_variational
- **Listener**: Bayesian posterior maximizes E[log L] → bayesian_maximizes_expected_log

This bypasses KKT entirely and gives constructive proofs.
-/

/-- Entropy equals sum of negMulLog for non-negative functions. -/
private theorem entropy_eq_sum_negMulLog' {β : Type*} [Fintype β] (p : β → ℝ)
    (_hp : ∀ i, 0 ≤ p i) : entropy p = ∑ i, Real.negMulLog (p i) := by
  unfold entropy Real.negMulLog
  simp only [neg_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hpi : p i = 0
  · simp only [hpi, Real.log_zero, mul_zero, neg_zero, ite_true]
  · simp only [hpi, ↓reduceIte]

/-- normalize is identity on distributions summing to 1. -/
private theorem normalize_of_sum_one' {β : Type*} [Fintype β] (f : β → ℝ)
    (hsum : ∑ i, f i = 1) (a : β) : normalize f a = f a := by
  unfold normalize Z
  rw [hsum, if_neg one_ne_zero, div_one]

/-- When L > 0, speakerScore = exp(α · utility). -/
private theorem speakerScore_eq_exp (S : RSAScenarioR) (L : S.U → S.M → ℝ)
    (hL : ∀ u m, 0 < L u m) (m : S.M) (u : S.U) :
    speakerScore S L m u = Real.exp (S.α * utility L m u) := by
  unfold speakerScore
  rw [if_neg (not_le.mpr (hL u m))]
  unfold utility
  rw [if_neg (not_le.mpr (hL u m))]
  change (L u m) ^ S.α = Real.exp (S.α * Real.log (L u m))
  rw [Real.rpow_def_of_pos (hL u m)]
  congr 1; ring

/-- When L > 0, normalize(speakerScore) = softmax(utility, α). -/
private theorem normalize_speakerScore_eq_softmax (S : RSAScenarioR) [Nonempty S.U]
    (L : S.U → S.M → ℝ) (hL : ∀ u m, 0 < L u m) (m : S.M) :
    (fun u => normalize (speakerScore S L m) u) = Softmax.softmax (utility L m) S.α := by
  ext u
  have hscore : ∀ v, speakerScore S L m v = Real.exp (S.α * utility L m v) :=
    fun v => speakerScore_eq_exp S L hL m v
  have hZ_pos : 0 < ∑ v, speakerScore S L m v :=
    Finset.sum_pos (fun v _ => hscore v ▸ Real.exp_pos _) Finset.univ_nonempty
  simp only [normalize, Z, Softmax.softmax]
  rw [if_neg (ne_of_gt hZ_pos)]
  congr 1
  · exact hscore u
  · exact Finset.sum_congr rfl (fun v _ => hscore v)

/-- G_α decomposes as a weighted sum of per-meaning objectives. -/
private theorem G_α_decompose (S : RSAScenarioR) (Spk : S.M → S.U → ℝ) (L : S.U → S.M → ℝ) :
    G_α S Spk L = ∑ m, S.prior m *
      (entropy (fun u => normalize (Spk m) u) +
       S.α * ∑ u, normalize (Spk m) u * utility L m u) := by
  unfold G_α H_S E_VL
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1; ext m
  rw [show ∑ u, S.prior m * normalize (Spk m) u * utility L m u =
        S.prior m * ∑ u, normalize (Spk m) u * utility L m u by
    simp only [mul_assoc]; rw [← Finset.mul_sum]]
  ring

/-- Sum of normalize equals 1 when Z > 0. -/
private theorem normalize_sum_eq_one {β : Type*} [Fintype β] (f : β → ℝ)
    (hZ : Z f ≠ 0) : ∑ i, normalize f i = 1 := by
  unfold normalize
  simp only [hZ, ↓reduceIte]
  rw [← Finset.sum_div]
  exact div_self hZ

/-
HISTORICAL NOTE: KKT sufficiency for concave functions on the simplex.

This was originally axiomatized as the key missing piece. We now prove
the RSA optimality results directly using the Gibbs Variational Principle
and Bayesian optimality, bypassing KKT entirely. The axioms have been
replaced with constructive proofs.

The standard KKT argument (Boyd & Vandenberghe 2004, §5.5.3):
1. Concavity: f(y) ≤ f(x*) + ∇f(x*)·(y - x*) for all y ∈ Δ
2. KKT on simplex: ∇f(x*) = λ·𝟙 (constant gradient when optimal)
3. Feasibility: 𝟙·(y - x*) = 1 - 1 = 0 for y, x* ∈ Δ
4. Therefore: f(y) ≤ f(x*) for all feasible y
-/
/--
RSA Speaker Update is G_α-Optimal (Zaslavsky et al. Eq. 7).

For fixed listener L, the normalized RSA speaker S(u|m) = softmax(utility(·,m), α)
maximizes G_α over all valid speaker distributions.

Proof: By the Gibbs Variational Principle (Softmax/Basic.lean), for each meaning m,
softmax maximizes H(p) + α⟨p, s⟩. Since G_α decomposes as a weighted sum of
per-meaning objectives, the pointwise maximum is also the global maximum.
-/
theorem rsa_speaker_maximizes_G_α (S : RSAScenarioR) [Nonempty S.U] (L : S.U → S.M → ℝ)
    (_hL : ∀ u m, 0 < L u m)
    (Spk' : S.M → S.U → ℝ)
    (hSpk'_sum : ∀ m, ∑ u, Spk' m u = 1)
    (hSpk'_nonneg : ∀ m u, 0 ≤ Spk' m u) :
    G_α S Spk' L ≤ G_α S (speakerUpdate S L) L := by
  rw [G_α_decompose, G_α_decompose]
  apply Finset.sum_le_sum
  intro m _
  apply mul_le_mul_of_nonneg_left _ (S.prior_nonneg m)
  -- LHS: normalize(Spk' m) = Spk' m (already on simplex)
  have hn : ∀ u, normalize (Spk' m) u = Spk' m u :=
    fun u => normalize_of_sum_one' _ (hSpk'_sum m) u
  -- RHS: speakerUpdate = speakerSoftmax = softmax, already sums to 1,
  -- so normalize is identity
  have hn_upd : ∀ u, normalize (speakerUpdate S L m) u =
      Softmax.softmax (utility L m) S.α u := by
    intro u
    exact normalize_of_sum_one' _ (speakerSoftmax_sum_one S L m) u
  simp_rw [hn, hn_upd]
  rw [entropy_eq_sum_negMulLog' _ (hSpk'_nonneg m),
      entropy_eq_sum_negMulLog' _ (fun u => le_of_lt (Softmax.softmax_pos _ _ u))]
  exact Softmax.gibbs_variational _ S.α _ (hSpk'_nonneg m) (hSpk'_sum m)

/--
RSA Listener Update is G_α-Optimal (Zaslavsky et al. Eq. 8).

For fixed normalized speaker Spk, the Bayesian listener L(m|u) ∝ P(m)·Spk(u|m)
maximizes G_α over all valid listener distributions.

Proof: Since H_S is fixed, we maximize E_VL = ∑_u ∑_m w_u(m)·log L(m|u)
where w_u(m) = P(m)·S(u|m). By bayesian_maximizes_expected_log, for each u,
the normalized w_u maximizes ∑_m (w/W)·log L. This normalized w_u equals
listenerUpdate, so E_VL is maximized at the Bayesian posterior.
-/
theorem rsa_listener_maximizes_G_α (S : RSAScenarioR) [Nonempty S.U] (Spk : S.M → S.U → ℝ)
    (hSpk_pos : ∀ m u, 0 < Spk m u)
    (hSpk_sum : ∀ m, ∑ u, Spk m u = 1)
    (L' : S.U → S.M → ℝ)
    (hL'_sum : ∀ u, ∑ m, L' u m = 1)
    (hL'_pos : ∀ u m, 0 < L' u m) :
    G_α S Spk L' ≤ G_α S Spk (listenerUpdate S Spk) := by
  -- H_S is fixed; suffices to show α * E_VL(L') ≤ α * E_VL(listenerUpdate)
  unfold G_α
  suffices h : E_VL S Spk L' ≤ E_VL S Spk (listenerUpdate S Spk) by
    linarith [S.α_nonneg, mul_le_mul_of_nonneg_left h S.α_nonneg]
  -- Since Spk is normalized, normalize(Spk m) = Spk m
  have hn_Spk : ∀ m u, normalize (Spk m) u = Spk m u :=
    fun m u => normalize_of_sum_one' _ (hSpk_sum m) u
  haveI : Nonempty S.M := by obtain ⟨m, _⟩ := S.prior_pos; exact ⟨m⟩
  -- Swap sums in E_VL to get per-utterance decomposition
  unfold E_VL
  simp_rw [hn_Spk]
  rw [Finset.sum_comm (f := fun m u => S.prior m * Spk m u * utility L' m u),
      Finset.sum_comm (f := fun m u => S.prior m * Spk m u * utility (listenerUpdate S Spk) m u)]
  apply Finset.sum_le_sum
  intro u _
  -- Weights for each u: w(m) = P(m) * Spk(m, u)
  set w := fun m => S.prior m * Spk m u
  have hw_nonneg : ∀ m, 0 ≤ w m :=
    fun m => mul_nonneg (S.prior_nonneg m) (le_of_lt (hSpk_pos m u))
  -- W = ∑ w > 0 (since ∃ m with P(m) > 0 and Spk > 0)
  have hW_pos : 0 < ∑ m, w m := by
    obtain ⟨m₀, hm₀⟩ := S.prior_pos
    exact Finset.sum_pos' (fun m _ => hw_nonneg m) ⟨m₀, Finset.mem_univ _, mul_pos hm₀ (hSpk_pos m₀ u)⟩
  -- listenerUpdate(u, m) = w(m) / W
  have hLU_eq : ∀ m, listenerUpdate S Spk u m = w m / ∑ m', w m' := by
    intro m
    simp only [listenerUpdate, listenerScore, normalize, Z]
    rw [if_neg (ne_of_gt hW_pos)]
  -- utility(L', m, u) = log(L' u m) since L' > 0
  have hutil_L' : ∀ m, utility L' m u = Real.log (L' u m) := by
    intro m; unfold utility; rw [if_neg (not_le.mpr (hL'_pos u m))]
  -- Per-term equality for listener utility, handling w m = 0
  have hutil_LU : ∀ m, w m * utility (listenerUpdate S Spk) m u =
      w m * Real.log (w m / ∑ m', w m') := by
    intro m
    by_cases hwm : w m = 0
    · simp only [hwm, zero_mul]
    · have hwm_pos : 0 < w m := lt_of_le_of_ne (hw_nonneg m) (Ne.symm hwm)
      have hLU_pos : 0 < w m / ∑ m', w m' := div_pos hwm_pos hW_pos
      congr 1
      unfold utility
      rw [if_neg (not_le.mpr (by rw [hLU_eq]; exact hLU_pos)), hLU_eq]
  -- Goal: ∑ m, w m * utility L' m u ≤ ∑ m, w m * utility (listenerUpdate S Spk) m u
  -- Transform to log form and apply bayesian_maximizes
  calc ∑ m, w m * utility L' m u
      = ∑ m, w m * Real.log (L' u m) := by congr 1; ext m; rw [hutil_L']
    _ ≤ ∑ m, w m * Real.log (w m / ∑ m', w m') :=
        RSA.GibbsVariational.bayesian_maximizes w hw_nonneg hW_pos
          (fun m => L' u m) (fun m => hL'_pos u m) (hL'_sum u)
    _ = ∑ m, w m * utility (listenerUpdate S Spk) m u := by
        congr 1; ext m; exact (hutil_LU m).symm

/--
The RSA speaker update maximizes G_α (Zaslavsky et al. Eq. 7).

For fixed listener L_{t-1}, the RSA speaker update S_t = argmax_S G_α[S, L_{t-1}].
Follows directly from `rsa_speaker_maximizes_G_α`.
-/
theorem speaker_update_maximizes_G (S : RSAScenarioR) [Nonempty S.U] (L : S.U → S.M → ℝ)
    (hL : ∀ u m, 0 < L u m) :
    ∀ Spk', (∀ m, ∑ u, Spk' m u = 1) → (∀ m u, 0 ≤ Spk' m u) →
      G_α S Spk' L ≤ G_α S (speakerUpdate S L) L := by
  intro Spk' hSpk'_sum hSpk'_nonneg
  exact rsa_speaker_maximizes_G_α S L hL Spk' hSpk'_sum hSpk'_nonneg

/--
The RSA listener update maximizes G_α (Zaslavsky et al. Eq. 8).

For fixed normalized speaker S_t, the RSA listener update L_t = argmax_L G_α[S_t, L].
Requires the speaker to be a valid distribution (sums to 1 per meaning).
-/
theorem listener_update_maximizes_G (S : RSAScenarioR) [Nonempty S.U] (Spk : S.M → S.U → ℝ)
    (hSpk_pos : ∀ m u, 0 < Spk m u) (hSpk_sum : ∀ m, ∑ u, Spk m u = 1) :
    ∀ L', (∀ u, ∑ m, L' u m = 1) → (∀ u m, 0 < L' u m) →
      G_α S Spk L' ≤ G_α S Spk (listenerUpdate S Spk) := by
  intro L' hL'_sum hL'_pos
  exact rsa_listener_maximizes_G_α S Spk hSpk_pos hSpk_sum L' hL'_sum hL'_pos


/--
G_α Monotonicity (Zaslavsky et al. Proposition 1, Eq. 9).

RSA dynamics implement alternating maximization of G_α.
For every t ≥ 1:
  G_α[S_t, L_{t-1}] ≤ G_α[S_t, L_t] ≤ G_α[S_{t+1}, L_t]

Proof: Chain speaker and listener optimality.
- Step 1: G_α[S_n, L_n] ≤ G_α[S_{n+1}, L_n] by speaker_update_maximizes_G
- Step 2: G_α[S_{n+1}, L_n] ≤ G_α[S_{n+1}, L_{n+1}] by listener_update_maximizes_G
-/
theorem G_α_monotone (S : RSAScenarioR) [Nonempty S.U] (n : ℕ)
    (h_pos : ∀ t u m, 0 < (iterateRSA S t).listener u m)
    (h_Spk_pos : ∀ t m u, 0 < (iterateRSA S t).speaker m u)
    (h_Spk_sum : ∀ t m, ∑ u, (iterateRSA S t).speaker m u = 1)
    (h_L_sum : ∀ t u, ∑ m, (iterateRSA S t).listener u m = 1) :
    G_α S (iterateRSA S n).speaker (iterateRSA S n).listener ≤
    G_α S (iterateRSA S (n+1)).speaker (iterateRSA S (n+1)).listener := by
  let state_n := iterateRSA S n
  let state_n1 := iterateRSA S (n+1)
  have hstep : state_n1 = stepRSA S state_n := Function.iterate_succ_apply' (stepRSA S) n _
  -- Step 1: G_α(S_n, L_n) ≤ G_α(S_{n+1}, L_n)  [speaker improved]
  have hSpk_nonneg : ∀ m u, 0 ≤ state_n.speaker m u :=
    λ m u => le_of_lt (h_Spk_pos n m u)
  have h_spk_eq : state_n1.speaker = speakerUpdate S state_n.listener := by
    simp only [hstep, stepRSA]
  have h1 : G_α S state_n.speaker state_n.listener ≤ G_α S state_n1.speaker state_n.listener := by
    rw [h_spk_eq]
    exact speaker_update_maximizes_G S state_n.listener (h_pos n)
      state_n.speaker (h_Spk_sum n) hSpk_nonneg
  -- Step 2: G_α(S_{n+1}, L_n) ≤ G_α(S_{n+1}, L_{n+1})  [listener improved]
  -- speakerUpdate = speakerSoftmax, which is positive by construction
  have hSpk'_pos : ∀ m u, 0 < state_n1.speaker m u := by
    intro m u; rw [h_spk_eq]; exact speakerSoftmax_pos S state_n.listener m u
  have h_lis_eq : state_n1.listener = listenerUpdate S state_n1.speaker := by
    simp only [hstep, stepRSA]
  have h2 : G_α S state_n1.speaker state_n.listener ≤ G_α S state_n1.speaker state_n1.listener := by
    rw [h_lis_eq]
    exact listener_update_maximizes_G S state_n1.speaker hSpk'_pos (h_Spk_sum (n+1))
      state_n.listener (h_L_sum n) (h_pos n)
  exact le_trans h1 h2

/-- Utility is non-positive when L is a probability distribution. -/
private theorem utility_nonpos {S : RSAScenarioR} (L : S.U → S.M → ℝ)
    (hL_sum : ∀ u, ∑ m, L u m = 1) (hL_pos : ∀ u m, 0 ≤ L u m)
    (m : S.M) (u : S.U) : utility L m u ≤ 0 := by
  unfold utility
  split_ifs with h
  · exact le_refl 0
  · push_neg at h
    exact Real.log_nonpos (le_of_lt h) (by
      calc L u m ≤ ∑ m', L u m' :=
            Finset.single_le_sum (fun m' _ => hL_pos u m') (Finset.mem_univ m)
        _ = 1 := hL_sum u)

/-- E_VL is non-positive when L is a probability distribution. -/
private theorem E_VL_nonpos (S : RSAScenarioR) (Spk : S.M → S.U → ℝ)
    (L : S.U → S.M → ℝ)
    (hSpk : ∀ m, ∑ u, Spk m u = 1) (hSpk_pos : ∀ m u, 0 ≤ Spk m u)
    (hL_sum : ∀ u, ∑ m, L u m = 1) (hL_pos : ∀ u m, 0 ≤ L u m) :
    E_VL S Spk L ≤ 0 := by
  unfold E_VL
  apply Finset.sum_nonpos; intro m _
  apply Finset.sum_nonpos; intro u _
  have hn : normalize (Spk m) u = Spk m u := normalize_of_sum_one' _ (hSpk m) u
  rw [hn]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (S.prior_nonneg m) (hSpk_pos m u))
    (utility_nonpos L hL_sum hL_pos m u)

/-- Entropy of a probability distribution is at most log of the support size.
    Proof via KL(p ‖ uniform) ≥ 0. -/
private theorem entropy_le_log_card {β : Type*} [Fintype β] [Nonempty β]
    (p : β → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    entropy p ≤ Real.log (Fintype.card β) := by
  have hn_pos : (0 : ℝ) < Fintype.card β := Nat.cast_pos.mpr Fintype.card_pos
  -- KL(p ‖ uniform) ≥ 0
  let q : β → ℝ := fun _ => 1 / Fintype.card β
  have hq_pos : ∀ i, 0 < q i := fun _ => div_pos one_pos hn_pos
  have hq_sum : ∑ i, q i = 1 := by
    simp only [q, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_div_cancel₀ 1 (ne_of_gt hn_pos)
  have hkl := RSA.GibbsVariational.kl_finite_nonneg p q hq_pos hp (by rw [hsum, hq_sum])
  -- Show klFinite p q = -entropy p + log |β|
  suffices hsuff : RSA.GibbsVariational.klFinite p q = -entropy p + Real.log (Fintype.card β) by
    linarith
  unfold RSA.GibbsVariational.klFinite entropy
  simp only [neg_neg]
  have hterm : ∀ i, (if p i = 0 then (0 : ℝ) else p i * log (p i / q i)) =
      (if p i = 0 then 0 else p i * log (p i)) + p i * log (Fintype.card β) := by
    intro i
    by_cases hi : p i = 0
    · simp [hi]
    · simp only [hi, ↓reduceIte]
      have hpi_pos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hi)
      rw [Real.log_div (ne_of_gt hpi_pos) (ne_of_gt (hq_pos i))]
      have hlog_q : log (q i) = -log (Fintype.card β : ℝ) := by
        simp only [q, one_div, Real.log_inv]
      rw [hlog_q]; ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_mul, hsum, one_mul]

/-- G_α is bounded above by log |U| when L is a probability distribution.

The bound requires L to be a valid distribution (non-negative, sums to 1)
because the utility function `log(L u m)` is non-positive when L u m ∈ (0, 1],
making E_VL ≤ 0 and thus G_α ≤ H_S ≤ log |U|.

Without hypotheses on L, the bound fails: if L u m > 1 for some u, m,
then utility = log(L u m) > 0, and E_VL can be arbitrarily large. -/
theorem G_α_bounded_above (S : RSAScenarioR) (Spk : S.M → S.U → ℝ)
    (L : S.U → S.M → ℝ)
    (hSpk : ∀ m, ∑ u, Spk m u = 1) (hSpk_pos : ∀ m u, 0 ≤ Spk m u)
    (hL_sum : ∀ u, ∑ m, L u m = 1) (hL_pos : ∀ u m, 0 ≤ L u m)
    (hα_pos : 0 ≤ S.α) :
    G_α S Spk L ≤ log (Fintype.card S.U) + S.α * 0 := by
  simp only [mul_zero, add_zero]
  -- Derive Nonempty S.U from the fact that ∑ u, Spk m u = 1 ≠ 0
  haveI : Nonempty S.U := by
    obtain ⟨m, _⟩ := S.prior_pos
    by_contra h; rw [not_nonempty_iff] at h
    have := hSpk m; simp [Finset.eq_empty_of_isEmpty] at this
  unfold G_α
  -- E_VL ≤ 0, so α * E_VL ≤ 0
  have hEVL : E_VL S Spk L ≤ 0 := E_VL_nonpos S Spk L hSpk hSpk_pos hL_sum hL_pos
  have hαEVL : S.α * E_VL S Spk L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα_pos hEVL
  -- H_S ≤ log |U|
  have hHS : H_S S Spk ≤ log (Fintype.card S.U) := by
    unfold H_S
    calc ∑ m, S.prior m * entropy (fun u => normalize (Spk m) u)
        ≤ ∑ m, S.prior m * log (Fintype.card S.U) := by
          apply Finset.sum_le_sum; intro m _
          apply mul_le_mul_of_nonneg_left _ (S.prior_nonneg m)
          have hn : ∀ u, normalize (Spk m) u = Spk m u :=
            fun u => normalize_of_sum_one' _ (hSpk m) u
          simp_rw [hn]
          exact entropy_le_log_card _ (hSpk_pos m) (hSpk m)
      _ = log (Fintype.card S.U) := by
          rw [← Finset.sum_mul, S.prior_sum, one_mul]
  linarith

/--
Corollary: RSA Converges (Zaslavsky et al. Footnote 1).

From the paper: "Because Gα is bounded from above, it follows that RSA iterations
are guaranteed to converge."

Proof by the Monotone Convergence Theorem:
- G_α is monotonically non-decreasing (by `G_α_monotone`)
- G_α is bounded above by log |U| (max entropy)
- Therefore the sequence G_α(S_t, L_t) converges
-/
theorem RSA_converges (S : RSAScenarioR) [Nonempty S.U]
    (h_pos : ∀ t u m, 0 < (iterateRSA S t).listener u m)
    (h_Spk_pos : ∀ t m u, 0 < (iterateRSA S t).speaker m u)
    (h_Spk_sum : ∀ t m, ∑ u, (iterateRSA S t).speaker m u = 1)
    (h_L_sum : ∀ t u, ∑ m, (iterateRSA S t).listener u m = 1) :
    ∃ L : ℝ, Filter.Tendsto
      (λ n => G_α S (iterateRSA S n).speaker (iterateRSA S n).listener)
      Filter.atTop
      (nhds L) := by
  set f := fun n => G_α S (iterateRSA S n).speaker (iterateRSA S n).listener
  -- Monotonicity: f n ≤ f (n+1) from G_α_monotone
  have hmono : Monotone f := monotone_nat_of_le_succ fun n =>
    G_α_monotone S n h_pos h_Spk_pos h_Spk_sum h_L_sum
  -- Bounded above by log |U|
  have hbdd : BddAbove (Set.range f) := by
    use log (Fintype.card S.U)
    rintro _ ⟨n, rfl⟩
    have := G_α_bounded_above S _ _ (h_Spk_sum n)
      (fun m u => le_of_lt (h_Spk_pos n m u)) (h_L_sum n)
      (fun u m => le_of_lt (h_pos n u m)) S.α_nonneg
    linarith
  exact ⟨⨆ n, f n, tendsto_atTop_ciSup hmono hbdd⟩

/-- Check if RSA has ε-converged. -/
def εConverged (S : RSAScenarioR) [Nonempty S.U] (t : ℕ) (ε : ℝ) : Prop :=
  |G_α S (iterateRSA S (t+1)).speaker (iterateRSA S (t+1)).listener -
   G_α S (iterateRSA S t).speaker (iterateRSA S t).listener| < ε

/-- Eventually ε-converged: For any ε > 0, RSA is eventually ε-converged. -/
theorem eventually_εConverged (S : RSAScenarioR) [Nonempty S.U] (ε : ℝ) (hε : 0 < ε)
    (h_pos : ∀ t u m, 0 < (iterateRSA S t).listener u m)
    (h_Spk_pos : ∀ t m u, 0 < (iterateRSA S t).speaker m u)
    (h_Spk_sum : ∀ t m, ∑ u, (iterateRSA S t).speaker m u = 1)
    (h_L_sum : ∀ t u, ∑ m, (iterateRSA S t).listener u m = 1) :
    ∃ T, ∀ t, T ≤ t → εConverged S t ε := by
  obtain ⟨L_val, hL⟩ := RSA_converges S h_pos h_Spk_pos h_Spk_sum h_L_sum
  set f := fun n => G_α S (iterateRSA S n).speaker (iterateRSA S n).listener
  -- f(n+1) → L_val
  have hL1 : Filter.Tendsto (fun n => f (n + 1)) Filter.atTop (nhds L_val) :=
    hL.comp (Filter.tendsto_add_atTop_nat 1)
  -- f(n+1) - f(n) → 0
  have hdiff : Filter.Tendsto (fun n => f (n + 1) - f n) Filter.atTop (nhds 0) := by
    have := hL1.sub hL; simp only [sub_self] at this; exact this
  -- ε-δ: ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (f(n+1) - f(n)) 0 < ε
  rw [Metric.tendsto_atTop] at hdiff
  obtain ⟨T, hT⟩ := hdiff ε hε
  exact ⟨T, fun t ht => by
    have := hT t ht
    simp only [Real.dist_eq, sub_zero] at this
    exact this⟩

end RSA.Convergence
