module

public import Linglib.Core.Probability.Choice.RationalAction
public import Linglib.Core.Probability.Distributions.Gaussian
public import Linglib.Core.Probability.Choice.RandomUtility
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Luce (1959): Individual Choice Behavior

This file formalizes four parts of [luce-1959]. From the first chapter it takes the just
noticeable difference: a threshold splits pairwise choice into discriminable preference and
indistinguishability, which form a semiorder, and the induced trace is the weak order of the
ratio scale. From the second chapter it takes the psychophysical scales. The power law of
Stevens is the ratio scale of the choice axiom in the coordinates of raw intensity, where
Fechner's law is the same scale in log intensity, and it yields the linear generalization of
Weber's law; independent stimulus continua multiply. Thurstone's Case V model of discriminal
processes is strongly stochastically transitive, and its extension to three alternatives is
incompatible with the choice axiom (`theorem7`). The ranking postulate
makes the probability of a rank ordering the product of successive first choices from the
shrinking set of alternatives, now the Plackett–Luce model; these probabilities sum to one,
marginalize to the choice probabilities, and order expected rank by scale value. From the
third chapter it takes the theory of choices among gambles: a decomposable preference
structure couples a choice function over gambles with one over chance events, the events
fall into at most three classes of subjective likelihood, exactly three under the
complementation axioms, and the choice function over events is constant across classes.

## Implementation notes

Luce's `P` and `Q` are families of probability measures on subsets of size at most three;
here both are total `ChoiceFn`s, for which `binary x x = 1`, so the second axiom needs its
`a ≠ b` guard (`axiom2_unguarded_false`) and the third its two guards
(`complementation_unguarded_false`). Ratio scales enter as `ChoiceFn.BinaryRatioScaleOn`,
local to the gamble set under discussion, because the third chapter mixes imperfect
discrimination among gambles with perfect discrimination among pure alternatives, which a
globally positive scale cannot represent. The first axiom lives in the structure; the further
axioms of the third chapter and the nondegeneracy of the three-class theorem are hypotheses
of the theorems that use them, as in the book. The three-class theorems are stated on
representatives, without a quotient. Luce offers the factoring `v(aρb) = w(a,b)·φ(ρ)` as a
hypothesis, not a theorem, and so does `gam_of_factored`.

## References

* [R. D. Luce, *Individual Choice Behavior*][luce-1959]
* [thurstone-1927]
* [plackett-1975]
-/

@[expose] public section

namespace Luce1959

open Core

/-!
### §1.G: Just noticeable differences and the trace (pp. 34–37)

A jnd threshold `π ∈ (1/2, 1)` splits pairwise choice into a
discriminable-preference relation `L(π)` and an indistinguishability relation
`I(π)` (Definition 3, p. 34). Given the positive ratio scale delivered by
Theorem 4, the pair satisfies Luce's semiorder axioms (Theorem 5, p. 35) —
trichotomy, I-reflexivity, the interval condition, and no-sandwiching — and
the trace ordering (Definition 4, p. 37) is a weak order coinciding with the
ratio-scale order (Theorem 6, p. 37).
-/

section JustNoticeableDifferences

variable {A : Type*}

/-- The `L(π)` relation (Definition 3, p. 34): `x L(π) y` iff
    `P(x, {x,y}) > π` — `x` is **discriminably preferred** to `y` at
    threshold `π`, for `1/2 < π < 1`. -/
def jndL (v : A → ℝ) (thr : ℝ) (x y : A) : Prop :=
  thr < pairwiseProb v x y

/-- The `I(π)` relation (Definition 3, p. 34): `x I(π) y` iff
    `1 - π ≤ P(x, {x,y}) ≤ π` — `x` and `y` are **indistinguishable** at
    threshold `π`. -/
def jndI (v : A → ℝ) (thr : ℝ) (x y : A) : Prop :=
  1 - thr ≤ pairwiseProb v x y ∧ pairwiseProb v x y ≤ thr

/-- I(π) is symmetric: if `x` and `y` are indistinguishable, so are `y` and
    `x`. -/
theorem jndI_symm (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ) (x y : A)
    (h : jndI v thr x y) : jndI v thr y x := by
  simp only [jndI] at *
  have hc := pairwiseProb_complement (hv x) (hv y)
  constructor <;> linarith [h.1, h.2]

/-- **I-reflexivity**: `x I(π) x`. -/
theorem jndI_refl (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x : A) :
    jndI v thr x x := by
  simp only [jndI, pairwiseProb_self (hv x)]
  constructor <;> linarith

/-- **Trichotomy**: for any `x, y`, exactly one of `xLy`, `yLx`, or `xIy`
    holds. -/
theorem jnd_trichotomy (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x y : A) :
    (jndL v thr x y ∧ ¬jndL v thr y x ∧ ¬jndI v thr x y) ∨
    (jndL v thr y x ∧ ¬jndL v thr x y ∧ ¬jndI v thr x y) ∨
    (jndI v thr x y ∧ ¬jndL v thr x y ∧ ¬jndL v thr y x) := by
  have hc := pairwiseProb_complement (hv x) (hv y)
  unfold jndL jndI
  by_cases h₁ : thr < pairwiseProb v x y
  · left; exact ⟨h₁, fun h => by linarith, fun ⟨_, h⟩ => by linarith⟩
  · push Not at h₁
    by_cases h₂ : thr < pairwiseProb v y x
    · right; left; exact ⟨h₂, fun h => by linarith, fun ⟨h, _⟩ => by linarith⟩
    · push Not at h₂
      right; right; exact ⟨⟨by linarith, h₁⟩, fun h => by linarith, fun h => by linarith⟩

/-- **Interval condition**: `xLy ∧ yIz ∧ zLw → xLw`. -/
theorem jndL_interval (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (_hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x y z w : A)
    (hxy : jndL v thr x y) (hyz : jndI v thr y z) (hzw : jndL v thr z w) :
    jndL v thr x w := by
  simp only [jndL, jndI, pairwiseProb] at *
  have hvx := hv x; have hvy := hv y; have hvz := hv z; have hvw := hv w
  rw [lt_div_iff₀ (add_pos hvx hvy)] at hxy
  obtain ⟨hyz_lo, _⟩ := hyz
  rw [le_div_iff₀ (add_pos hvy hvz)] at hyz_lo
  rw [lt_div_iff₀ (add_pos hvz hvw)] at hzw
  rw [lt_div_iff₀ (add_pos hvx hvw)]
  -- hxy: thr * v(y) < (1-thr) * v(x)
  -- hyz_lo: (1-thr) * v(z) ≤ thr * v(y)
  -- hzw: thr * v(w) < (1-thr) * v(z)
  -- Chain: thr * v(w) < (1-thr) * v(z) ≤ thr * v(y) < (1-thr) * v(x)
  linarith

/-- **No sandwiching**: `xLy ∧ yLz → ¬(xIw ∧ wIz)` — no `w` can be
    indistinguishable from both endpoints of a discriminable chain. -/
theorem jndL_no_sandwich (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1) (x y z w : A)
    (hxy : jndL v thr x y) (hyz : jndL v thr y z) :
    ¬(jndI v thr x w ∧ jndI v thr w z) := by
  intro ⟨hxw, hwz⟩
  simp only [jndL, jndI, pairwiseProb] at *
  have hvx := hv x; have hvy := hv y; have hvz := hv z; have hvw := hv w
  rw [lt_div_iff₀ (add_pos hvx hvy)] at hxy
  rw [lt_div_iff₀ (add_pos hvy hvz)] at hyz
  obtain ⟨hxw_lo, hxw_hi⟩ := hxw
  rw [le_div_iff₀ (add_pos hvx hvw)] at hxw_lo
  rw [div_le_iff₀ (add_pos hvx hvw)] at hxw_hi
  obtain ⟨hwz_lo, hwz_hi⟩ := hwz
  rw [le_div_iff₀ (add_pos hvw hvz)] at hwz_lo
  rw [div_le_iff₀ (add_pos hvw hvz)] at hwz_hi
  nlinarith [mul_le_mul_of_nonneg_right hxw_hi (le_of_lt hvw),
             mul_le_mul_of_nonneg_right hwz_hi (le_of_lt hvx),
             mul_lt_mul_of_pos_right hxy (hv z),
             mul_lt_mul_of_pos_right hyz (hv x)]

/-- **L-transitivity**: `xLy ∧ yLz → xLz`. Not one of the semiorder axioms —
    it follows from the interval condition instantiated at `z := y`, via
    I-reflexivity. -/
theorem jndL_trans (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1) (x y z : A)
    (hxy : jndL v thr x y) (hyz : jndL v thr y z) :
    jndL v thr x z :=
  jndL_interval v hv thr hthr_lower hthr_upper x y y z hxy
    (jndI_refl v hv thr hthr_lower hthr_upper y) hyz

/-- The trace relation (Definition 4, p. 37): `x ≥_T y` iff
    `P(x, z) ≥ P(y, z)` for all `z` — dominance in every pairwise comparison
    against a common reference. -/
def traceGe (v : A → ℝ) (x y : A) : Prop :=
  ∀ z : A, pairwiseProb v y z ≤ pairwiseProb v x z

/-- **Theorem 6**: the trace relation is equivalent to the scale ordering
    `v(y) ≤ v(x)`. -/
theorem trace_iff_scale_ge (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    traceGe v x y ↔ v y ≤ v x := by
  simp only [traceGe]
  constructor
  · intro h
    have := h y
    rwa [pairwiseProb_mono_iff (hv x) (hv y) (hv y)] at this
  · intro hle z
    rwa [pairwiseProb_mono_iff (hv x) (hv y) (hv z)]

/-- Corollary: `x ≥_T y` iff `P(x, y) ≥ 1/2`. -/
theorem trace_iff_pairwiseProb_ge_half (v : A → ℝ) (hv : ∀ a : A, 0 < v a)
    (x y : A) :
    traceGe v x y ↔ 1 / 2 ≤ pairwiseProb v x y := by
  rw [trace_iff_scale_ge v hv, pairwiseProb_ge_half_iff (hv x) (hv y)]

/-- The trace is reflexive: `x ≥_T x`. -/
theorem traceGe_refl (v : A → ℝ) (x : A) : traceGe v x x :=
  fun _ => le_refl _

/-- The trace is transitive: `x ≥_T y ∧ y ≥_T z → x ≥_T z`. -/
theorem traceGe_trans (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y z : A)
    (hxy : traceGe v x y) (hyz : traceGe v y z) :
    traceGe v x z := by
  rw [trace_iff_scale_ge v hv] at *
  linarith

/-- The trace is total: for any `x, y`, either `x ≥_T y` or `y ≥_T x`.
    With `traceGe_refl` and `traceGe_trans`, the trace is a **weak order**
    (total preorder). -/
theorem traceGe_total (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    traceGe v x y ∨ traceGe v y x := by
  rw [trace_iff_scale_ge v hv, trace_iff_scale_ge v hv]
  exact le_total (v y) (v x)

/-- The trace agrees with L: if `xLy` for any `π`, then `x ≥_T y`. -/
theorem traceGe_of_jndL (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr : 1 / 2 < thr) (x y : A) (h : jndL v thr x y) :
    traceGe v x y := by
  rw [trace_iff_scale_ge v hv]
  rw [jndL, pairwiseProb] at h
  have hD := add_pos (hv x) (hv y)
  have := (lt_div_iff₀ hD).mp h
  nlinarith

end JustNoticeableDifferences


section PowerLaw

open Real BigOperators Finset

/-! ### §2.B: Stevens' Power Law -/

/-- A Stevens power-law scale: ψ(s) = k · sⁿ.

The exponent `n` characterizes the sensory modality. The coefficient `k` is a unit
constant that depends on the choice of measurement units.

This is the ratio-scale representation of psychophysical magnitude.
Under change of variables `u = log s`, it becomes the exponential form
`v = k · exp(n · u)` — exactly the Fechnerian characterization. -/
structure StevensScale where
  /-- Power-law exponent (sensory modality parameter). -/
  n : ℝ
  /-- Scale coefficient (unit-dependent constant). -/
  k : ℝ
  /-- Exponent is positive (higher intensity → higher magnitude). -/
  hn_pos : 0 < n
  /-- Coefficient is positive (magnitudes are positive). -/
  hk_pos : 0 < k

/-- The Stevens power function: ψ(s) = k · sⁿ.
    Requires s > 0 (stimulus intensities are positive reals). -/
noncomputable def StevensScale.psi (σ : StevensScale) (s : ℝ) : ℝ :=
  σ.k * s ^ σ.n

/-- Stevens scale values are positive for positive stimuli. -/
theorem StevensScale.psi_pos (σ : StevensScale) {s : ℝ} (hs : 0 < s) :
    0 < σ.psi s :=
  mul_pos σ.hk_pos (rpow_pos_of_pos hs σ.n)

/-- Pairwise choice probability under Stevens' power law:
    P(s₁, s₂) = s₁ⁿ / (s₁ⁿ + s₂ⁿ).

    This is the Luce choice rule with score function `score(s) = sⁿ`.
    The coefficient `k` cancels in the ratio. -/
noncomputable def StevensScale.choiceProb (σ : StevensScale) (s₁ s₂ : ℝ) : ℝ :=
  s₁ ^ σ.n / (s₁ ^ σ.n + s₂ ^ σ.n)

/-- Choice probabilities sum to 1 for positive stimuli. -/
theorem StevensScale.choiceProb_complement (σ : StevensScale) {s₁ s₂ : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    σ.choiceProb s₁ s₂ + σ.choiceProb s₂ s₁ = 1 := by
  simp only [choiceProb]
  have hd₁ : 0 < s₁ ^ σ.n := rpow_pos_of_pos h₁ σ.n
  have hd₂ : 0 < s₂ ^ σ.n := rpow_pos_of_pos h₂ σ.n
  have hne : s₁ ^ σ.n + s₂ ^ σ.n ≠ 0 := ne_of_gt (add_pos hd₁ hd₂)
  rw [add_comm (s₂ ^ σ.n) (s₁ ^ σ.n), ← add_div, div_self hne]

/-- Choice probability is between 0 and 1 for positive stimuli. -/
theorem StevensScale.choiceProb_nonneg (σ : StevensScale) {s₁ s₂ : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    0 ≤ σ.choiceProb s₁ s₂ := by
  simp only [choiceProb]
  exact div_nonneg (le_of_lt (rpow_pos_of_pos h₁ σ.n))
    (le_of_lt (add_pos (rpow_pos_of_pos h₁ σ.n) (rpow_pos_of_pos h₂ σ.n)))

/-- Equal stimuli give probability 1/2 (indifference). -/
theorem StevensScale.choiceProb_eq (σ : StevensScale) {s : ℝ} (hs : 0 < s) :
    σ.choiceProb s s = 1 / 2 := by
  simp only [choiceProb]
  have hpos : 0 < s ^ σ.n := rpow_pos_of_pos hs σ.n
  have hne : s ^ σ.n ≠ 0 := ne_of_gt hpos
  field_simp
  ring

/-- Monotonicity: higher stimulus → higher choice probability.
    Follows from `rpow_le_rpow` and monotonicity of `x / (x + c)`. -/
theorem StevensScale.choiceProb_mono (σ : StevensScale) {s₁ s₂ s₃ : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (h₃ : 0 < s₃)
    (hle : s₁ ≤ s₂) :
    σ.choiceProb s₁ s₃ ≤ σ.choiceProb s₂ s₃ := by
  simp only [choiceProb]
  have hp₁ : 0 < s₁ ^ σ.n := rpow_pos_of_pos h₁ σ.n
  have hp₂ : 0 < s₂ ^ σ.n := rpow_pos_of_pos h₂ σ.n
  have hp₃ : 0 < s₃ ^ σ.n := rpow_pos_of_pos h₃ σ.n
  have hd₁ : 0 < s₁ ^ σ.n + s₃ ^ σ.n := add_pos hp₁ hp₃
  have hd₂ : 0 < s₂ ^ σ.n + s₃ ^ σ.n := add_pos hp₂ hp₃
  rw [div_le_div_iff₀ hd₁ hd₂]
  have hrpow : s₁ ^ σ.n ≤ s₂ ^ σ.n :=
    rpow_le_rpow (le_of_lt h₁) hle (le_of_lt σ.hn_pos)
  nlinarith [mul_le_mul_of_nonneg_right hrpow (le_of_lt hp₃)]

/-- Stevens' power law choice probabilities satisfy the Luce model.

Given a finite set of stimuli with positive intensities, the choice rule
`score(s) = sⁿ` defines a valid `RationalAction`. The coefficient `k`
drops out of the normalized policy. -/
noncomputable def stevens_is_luce {Stimulus : Type*} [Fintype Stimulus]
    (σ : StevensScale) (intensity : Stimulus → ℝ) (h_pos : ∀ s, 0 < intensity s) :
    RationalAction Unit Stimulus where
  score _ s := (intensity s) ^ σ.n
  score_nonneg _ s := le_of_lt (rpow_pos_of_pos (h_pos s) σ.n)

/-- The Luce model from Stevens' power law recovers the pairwise choice
    probability as a special case (for a two-element choice set). -/
theorem stevens_luce_pairwise {σ : StevensScale} {s₁ s₂ : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    let ra := stevens_is_luce σ (![s₁, s₂]) (fun i => by
      fin_cases i <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one])
    ra.policy () (0 : Fin 2) = σ.choiceProb s₁ s₂ := by
  intro ra
  have hp₁ : 0 < s₁ ^ σ.n := rpow_pos_of_pos h₁ σ.n
  have hp₂ : 0 < s₂ ^ σ.n := rpow_pos_of_pos h₂ σ.n
  have hts : ra.totalScore () = s₁ ^ σ.n + s₂ ^ σ.n := by
    simp [RationalAction.totalScore, ra, stevens_is_luce, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have hts_ne : ra.totalScore () ≠ 0 := by
    rw [hts]; exact ne_of_gt (add_pos hp₁ hp₂)
  simp only [RationalAction.policy, hts_ne, ↓reduceIte]
  change ra.score () 0 / ra.totalScore () = _
  rw [hts]
  simp [ra, stevens_is_luce, StevensScale.choiceProb, Matrix.cons_val_zero]

/-- Stevens' power-law choice probability is the pairwise Luce kernel
    `pairwiseProb` on the power scale `s ↦ sⁿ`. -/
theorem StevensScale.choiceProb_eq_pairwiseProb (σ : StevensScale) (s₁ s₂ : ℝ) :
    σ.choiceProb s₁ s₂ = pairwiseProb (· ^ σ.n) s₁ s₂ := by
  simp only [choiceProb, pairwiseProb]

/-- Choice probability orders stimuli by intensity: against any positive
    reference stimulus, `choiceProb` compares as the intensities do. -/
theorem StevensScale.choiceProb_le_iff (σ : StevensScale) {s₁ s₂ z : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hz : 0 < z) :
    σ.choiceProb s₁ z ≤ σ.choiceProb s₂ z ↔ s₁ ≤ s₂ := by
  have hp₁ : 0 < s₁ ^ σ.n := rpow_pos_of_pos h₁ σ.n
  have hp₂ : 0 < s₂ ^ σ.n := rpow_pos_of_pos h₂ σ.n
  have hpz : 0 < z ^ σ.n := rpow_pos_of_pos hz σ.n
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hpow := rpow_lt_rpow h₂.le hlt σ.hn_pos
    have : σ.choiceProb s₂ z < σ.choiceProb s₁ z := by
      simp only [choiceProb]
      rw [div_lt_div_iff₀ (add_pos hp₂ hpz) (add_pos hp₁ hpz)]
      nlinarith
    linarith
  · exact fun hle => σ.choiceProb_mono h₁ h₂ hz hle

/-- **Stevens–Fechner equivalence** ([luce-1959], §2.B):
    Stevens' power law on raw intensity is equivalent to Fechner's
    exponential law on log-intensity.

    If `v(s) = k · sⁿ` (Stevens), define `u(s) = log s`. Then:
    `v(s) = k · exp(n · u(s))`
    which is exactly the Fechnerian form from `luce_fechnerian_exp`.

    This shows the two "laws" are the same mathematical structure viewed
    in different coordinates: Stevens works on the multiplicative scale
    of physical intensity, Fechner on the additive scale of log-intensity. -/
theorem stevens_fechner_equivalence (σ : StevensScale) {s : ℝ} (hs : 0 < s) :
    σ.psi s = σ.k * exp (σ.n * log s) := by
  simp only [StevensScale.psi]
  rw [rpow_def_of_pos hs, mul_comm (log s) σ.n]

/-- The ratio of Stevens scale values depends only on the intensity ratio,
    confirming it is a ratio scale. -/
theorem StevensScale.ratio_depends_on_ratio (σ : StevensScale) {s₁ s₂ : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    σ.psi s₁ / σ.psi s₂ = (s₁ / s₂) ^ σ.n := by
  simp only [psi]
  rw [mul_div_mul_left _ _ (ne_of_gt σ.hk_pos)]
  rw [div_rpow (le_of_lt h₁) (le_of_lt h₂)]

/-- Stevens' power law satisfies the Cauchy multiplicative equation
    on log-intensity: `g(u₁ + u₂) = g(u₁) · g(u₂)` where `g(u) = exp(n · u)`.

    This is the bridge to `cauchy_mul_exp`: the function mapping
    log-intensity differences to scale ratios is the exponential. -/
theorem stevens_cauchy (σ : StevensScale) (u₁ u₂ : ℝ) :
    exp (σ.n * (u₁ + u₂)) = exp (σ.n * u₁) * exp (σ.n * u₂) := by
  rw [mul_add, exp_add]

/-! ### §2.C: Interaction of Stimulus Continua -/

/-- A multi-dimensional stimulus has components along each dimension.
    Each dimension has its own psychophysical scale function.

    Example: a stimulus varying in both loudness (dim 1) and brightness
    (dim 2) is represented as a pair `(a₁, a₂)` with independent
    scale functions `v₁` and `v₂`. -/
structure MultidimStimulus (D : Type*) (S : D → Type*) where
  /-- Scale function for each dimension. -/
  scale : (d : D) → S d → ℝ
  /-- Scale values are positive. -/
  scale_pos : ∀ (d : D) (s : S d), 0 < scale d s

/-- Independence axiom for multi-dimensional stimuli ([luce-1959], §2.C):
    the relative discriminability along one dimension does not depend
    on the value along the other dimensions.

    Formally: for a two-dimensional stimulus, the ratio `v(a₁, a₂) / v(b₁, a₂)`
    depends only on `a₁` and `b₁`, not on `a₂`. This forces the overall
    scale to decompose as a product: `v(a₁, a₂) = v₁(a₁) · v₂(a₂)`.

    We state this for an arbitrary (finite) number of dimensions. -/
structure DimensionIndependence {D : Type*} [Fintype D] [DecidableEq D] {S : D → Type*}
    (v : ((d : D) → S d) → ℝ)
    (ms : MultidimStimulus D S) where
  /-- Overall scale is positive. -/
  v_pos : ∀ (a : (d : D) → S d), 0 < v a
  /-- Independence: replacing the value along dimension `d` scales `v`
      by a factor depending only on `d` and the old/new values, not
      on the values along other dimensions.

      For all stimuli `a`, if we change dimension `d` from `a d` to `s`,
      the ratio `v(a[d↦s]) / v(a)` depends only on `a d` and `s`. -/
  ratio_indep : ∀ (d : D) (a : (d : D) → S d) (s : S d),
    v (Function.update a d s) / v a = ms.scale d s / ms.scale d (a d)

/-- **Multidimensional decomposition** ([luce-1959], §2.C, Theorem):
    Under dimension independence, the overall scale function factors
    as a product of per-dimension scales (up to a global constant).

    `v(a) = C · ∏ d, scale d (a d)`

    where `C` absorbs the normalization. -/
theorem multidimensional_decomposition {D : Type*} [Fintype D] [DecidableEq D]
    {S : D → Type*} (v : ((d : D) → S d) → ℝ)
    (ms : MultidimStimulus D S) (ind : DimensionIndependence v ms)
    (a₀ : (d : D) → S d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (a : (d : D) → S d),
      v a = C * ∏ d : D, ms.scale d (a d) := by
  set P₀ := ∏ d : D, ms.scale d (a₀ d) with hP₀_def
  have hP₀_pos : 0 < P₀ := Finset.prod_pos (fun d _ => ms.scale_pos d (a₀ d))
  refine ⟨v a₀ / P₀, div_pos (ind.v_pos a₀) hP₀_pos, ?_⟩
  intro a
  set mix : Finset D → ((d : D) → S d) := fun T d => if d ∈ T then a d else a₀ d
  suffices key : ∀ T : Finset D,
      v (mix T) = v a₀ * ∏ d ∈ T, (ms.scale d (a d) / ms.scale d (a₀ d)) by
    have hfull := key Finset.univ
    have hmix_univ : mix Finset.univ = a :=
      funext fun d => ite_eq_left (Finset.mem_univ d)
    rw [hmix_univ] at hfull
    rw [hfull, Finset.prod_div_distrib, ← hP₀_def, ← mul_div_assoc, mul_div_right_comm]
  intro T
  induction T using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, mul_one]
    congr 1
  | @insert d₀ T' hd₀ ih =>
    rw [Finset.prod_insert hd₀]
    have hmix_ins : mix (insert d₀ T') = Function.update (mix T') d₀ (a d₀) := by
      ext d'
      by_cases h : d' = d₀
      · subst h; simp [mix, Function.update_self]
      · simp [mix, Finset.mem_insert, h]
    rw [hmix_ins]
    have hri := ind.ratio_indep d₀ (mix T') (a d₀)
    have hv_ne : v (mix T') ≠ 0 := ne_of_gt (ind.v_pos _)
    rw [div_eq_iff hv_ne] at hri
    have hmix_d₀ : (mix T') d₀ = a₀ d₀ := ite_eq_right hd₀
    rw [hmix_d₀] at hri
    rw [hri, ih]
    ring

/-- For two dimensions, decomposition gives the explicit product form:
    `v(a₁, a₂) = C · v₁(a₁) · v₂(a₂)`.

    The original `h_factor` hypothesis (per-pair C) was too weak — different
    pairs could have different constants. The correct hypothesis is
    ratio-independence: the ratio `v(s₁, s₂)/v(s₁', s₂)` depends only on
    `s₁, s₁'` (not on `s₂`), and symmetrically for dimension 2. This is
    the two-dimensional specialization of `DimensionIndependence.ratio_indep`. -/
theorem multidim_two_decomposition
    {S₁ S₂ : Type*} [Nonempty S₁] [Nonempty S₂]
    (v : S₁ × S₂ → ℝ)
    (v₁ : S₁ → ℝ) (v₂ : S₂ → ℝ)
    (hv_pos : ∀ a, 0 < v a)
    (hv₁_pos : ∀ s, 0 < v₁ s) (hv₂_pos : ∀ s, 0 < v₂ s)
    (h_indep₁ : ∀ s₁ s₁' s₂, v (s₁, s₂) / v (s₁', s₂) = v₁ s₁ / v₁ s₁')
    (h_indep₂ : ∀ s₁ s₂ s₂', v (s₁, s₂) / v (s₁, s₂') = v₂ s₂ / v₂ s₂') :
    ∃ C : ℝ, 0 < C ∧ ∀ a₁ a₂, v (a₁, a₂) = C * v₁ a₁ * v₂ a₂ := by
  obtain ⟨a₀⟩ := ‹Nonempty S₁›; obtain ⟨b₀⟩ := ‹Nonempty S₂›
  refine ⟨v (a₀, b₀) / (v₁ a₀ * v₂ b₀),
          div_pos (hv_pos _) (mul_pos (hv₁_pos _) (hv₂_pos _)), ?_⟩
  intro a₁ a₂
  have hv₁_ne : v₁ a₀ ≠ 0 := ne_of_gt (hv₁_pos a₀)
  have hv₂_ne : v₂ b₀ ≠ 0 := ne_of_gt (hv₂_pos b₀)
  have eq₁ : v (a₁, a₂) * v₁ a₀ = v₁ a₁ * v (a₀, a₂) :=
    (div_eq_div_iff (ne_of_gt (hv_pos _)) hv₁_ne).mp (h_indep₁ a₁ a₀ a₂)
  have eq₂ : v (a₀, a₂) * v₂ b₀ = v₂ a₂ * v (a₀, b₀) :=
    (div_eq_div_iff (ne_of_gt (hv_pos _)) hv₂_ne).mp (h_indep₂ a₀ a₂ b₀)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hv₁_ne hv₂_ne)]
  calc v (a₁, a₂) * (v₁ a₀ * v₂ b₀)
      = v (a₁, a₂) * v₁ a₀ * v₂ b₀ := by ring
    _ = v₁ a₁ * v (a₀, a₂) * v₂ b₀ := by rw [eq₁]
    _ = v₁ a₁ * (v (a₀, a₂) * v₂ b₀) := by ring
    _ = v₁ a₁ * (v₂ a₂ * v (a₀, b₀)) := by rw [eq₂]
    _ = v (a₀, b₀) * v₁ a₁ * v₂ a₂ := by ring

/-- The Luce choice rule for multi-dimensional stimuli with independent
    dimensions decomposes into a product of per-dimension contributions.

    For a choice between multi-dimensional alternatives, the choice
    probability factors:
    `P(a, T) ∝ ∏ d, scale d (a d)` -/
noncomputable def multidim_luce {D : Type*} [Fintype D] [DecidableEq D]
    {S : D → Type*} {Alt : Type*} [Fintype Alt]
    (ms : MultidimStimulus D S)
    (stimulus : Alt → (d : D) → S d) :
    RationalAction Unit Alt where
  score _ a := ∏ d : D, ms.scale d (stimulus a d)
  score_nonneg _ a := Finset.prod_nonneg
    (fun d _ => le_of_lt (ms.scale_pos d (stimulus a d)))

/-- Independence implies that the multi-dimensional Luce model
    recovers the single-dimension choice probability when all other
    dimensions are held constant. -/
theorem multidim_marginal_recovery {S₁ S₂ : Type*}
    (v₁ : S₁ → ℝ) (v₂ : S₂ → ℝ)
    {a b : S₁} {c : S₂}
    (_ha : 0 < v₁ a) (_hb : 0 < v₁ b) (hc : 0 < v₂ c) :
    v₁ a * v₂ c / (v₁ a * v₂ c + v₁ b * v₂ c) = v₁ a / (v₁ a + v₁ b) := by
  have hvc_ne : v₂ c ≠ 0 := ne_of_gt hc
  rw [show v₁ a * v₂ c + v₁ b * v₂ c = (v₁ a + v₁ b) * v₂ c from by ring]
  rw [mul_div_mul_right _ _ hvc_ne]

end PowerLaw

/-!
### §2.B: The power law and Weber's law (pp. 42–47)

For the power scale `v(s) = sⁿ`, [luce-1959] derives the linear
generalization of Weber's law: the just-noticeable intensity ratio at
threshold `π` is `(π/(1−π))^(1/n)`. `stevens_jndL_intensity_ratio` is the
`C = 0` inequality form, stated over `StevensScale`.
-/

section PowerLawWeber

open Real

/-- **Weber ratio from the jnd** (§2.B): if `s₁` is discriminably preferred
    to `s₂` at threshold `π` under a power scale with exponent `n`, the
    intensity ratio `s₁/s₂` exceeds `(π/(1-π))^(1/n)`. -/
theorem stevens_jndL_intensity_ratio (σ : StevensScale) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1)
    {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (hL : jndL (· ^ σ.n) thr s₁ s₂) :
    (thr / (1 - thr)) ^ (1 / σ.n) < s₁ / s₂ := by
  simp only [jndL, pairwiseProb] at hL
  have hp₁ : 0 < s₁ ^ σ.n := rpow_pos_of_pos h₁ σ.n
  have hp₂ : 0 < s₂ ^ σ.n := rpow_pos_of_pos h₂ σ.n
  have hd : 0 < s₁ ^ σ.n + s₂ ^ σ.n := add_pos hp₁ hp₂
  rw [lt_div_iff₀ hd] at hL
  have h1mt : 0 < 1 - thr := by linarith
  have hthr_ratio_pos : 0 < thr / (1 - thr) := div_pos (by linarith) h1mt
  have h_ratio : thr / (1 - thr) < (s₁ / s₂) ^ σ.n := by
    rw [div_rpow (le_of_lt h₁) (le_of_lt h₂), div_lt_div_iff₀ h1mt hp₂]; nlinarith
  have h5 := rpow_lt_rpow (le_of_lt hthr_ratio_pos) h_ratio (div_pos one_pos σ.hn_pos)
  rw [← rpow_mul (le_of_lt (div_pos h₁ h₂)), mul_one_div_cancel (ne_of_gt σ.hn_pos),
    rpow_one] at h5
  exact h5

end PowerLawWeber


section Thurstone

open Real MeasureTheory ProbabilityTheory BigOperators Set

/-! ### §2.D: Discriminal processes (pp. 54–58) -/

/-- Thurstone's Case V model ([thurstone-1927]; [luce-1959], §2.D).

    Each stimulus has a scale value `scale(a)` and all stimuli share a common
    discriminal dispersion `sigma > 0`. The choice probability is determined
    by the normal CDF applied to the standardized scale difference. -/
structure ThurstoneCaseV (Stimulus : Type*) where
  /-- The scale value (mean of the discriminal process) for each stimulus. -/
  scale : Stimulus → ℝ
  /-- The common discriminal dispersion (standard deviation). -/
  sigma : ℝ
  /-- The dispersion is strictly positive. -/
  sigma_pos : 0 < sigma

variable {Stimulus : Type*}

/-- Choice probability under Thurstone Case V:
    `P(a,b) = Φ((u(a) - u(b)) / (σ√2))`.

    This is the probability that the discriminal process for `a` exceeds
    that for `b`, when both are independent Gaussians with means `u(a)`, `u(b)`
    and common variance `σ²`. The difference is Gaussian with mean
    `u(a) - u(b)` and variance `2σ²`, hence standard deviation `σ√2`. -/
noncomputable def ThurstoneCaseV.choiceProb (m : ThurstoneCaseV Stimulus)
    (a b : Stimulus) : ℝ :=
  gaussianChoiceProb (m.scale a - m.scale b) (m.sigma * Real.sqrt 2)

/-- The Case V choice probability is derived and not stipulated: when the discriminal processes of
    `a` and `b` are independent Gaussians with means `u(a)`, `u(b)` and common variance `σ²`, the
    probability that the process of `a` exceeds that of `b` is `choiceProb a b`. -/
theorem ThurstoneCaseV.rumChoiceProb_eq (m : ThurstoneCaseV Stimulus) (a b : Stimulus) :
    rumChoiceProb (fun j ↦ gaussianReal (![m.scale a, m.scale b] j)
      (.mk (m.sigma ^ 2) (sq_nonneg _))) 0 = ENNReal.ofReal (m.choiceProb a b) :=
  rumChoiceProb_gaussianReal_sq _ m.sigma_pos

/-- When `u(a) = u(b)`, the choice probability is `1/2` (indifference). -/
theorem ThurstoneCaseV.choiceProb_eq (m : ThurstoneCaseV Stimulus)
    (a b : Stimulus) (h : m.scale a = m.scale b) :
    m.choiceProb a b = 2⁻¹ := by
  rw [choiceProb, h, sub_self, gaussianChoiceProb_zero]

/-- Complementarity: `P(a,b) + P(b,a) = 1`. -/
theorem ThurstoneCaseV.choiceProb_complement (m : ThurstoneCaseV Stimulus)
    (a b : Stimulus) :
    m.choiceProb a b + m.choiceProb b a = 1 := by
  simp only [choiceProb]
  rw [show m.scale b - m.scale a = -(m.scale a - m.scale b) from by ring]
  exact gaussianChoiceProb_complement _ _

/-- If `u(a) > u(b)`, then `P(a,b) > 1/2` — the higher-scale stimulus
    is chosen more often than chance. -/
theorem ThurstoneCaseV.choiceProb_gt_half (m : ThurstoneCaseV Stimulus)
    (a b : Stimulus) (h : m.scale b < m.scale a) :
    2⁻¹ < m.choiceProb a b :=
  inv_two_lt_gaussianChoiceProb (sub_pos.mpr h) (mul_pos m.sigma_pos (Real.sqrt_pos.mpr two_pos))

/-! ### Strong stochastic transitivity -/

/-- **Strong stochastic transitivity** (Thurstone Case V).

    If `u(a) > u(b) > u(c)`, then `P(a,c) > P(a,b)` — the "big gap" comparison
    is easier than either "small gap" comparison.

    Proof: `u(a) - u(c) > u(a) - u(b)`, so after dividing by `σ√2 > 0`,
    the argument to `Φ` is larger, and `Φ` is strictly monotone. -/
theorem ThurstoneCaseV.transitivity_left (m : ThurstoneCaseV Stimulus)
    (a b c : Stimulus)
    (_hab : m.scale b < m.scale a) (hbc : m.scale c < m.scale b) :
    m.choiceProb a b < m.choiceProb a c := by
  simp only [choiceProb]
  apply gaussianChoiceProb_strictMono
    (mul_pos m.sigma_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  linarith

/-- The right half of strong stochastic transitivity:
    if `u(a) > u(b) > u(c)`, then `P(a,c) > P(b,c)`. -/
theorem ThurstoneCaseV.transitivity_right (m : ThurstoneCaseV Stimulus)
    (a b c : Stimulus)
    (hab : m.scale b < m.scale a) (_hbc : m.scale c < m.scale b) :
    m.choiceProb b c < m.choiceProb a c := by
  simp only [choiceProb]
  apply gaussianChoiceProb_strictMono
    (mul_pos m.sigma_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  linarith

/-! ### §2.D.2: Relation of the choice axiom to Case V

On pairs the choice axiom gives the logistic function of the scale difference and Case V the
normal distribution function. The two are logically distinct, and Luce compares them
numerically: tabulating the `P(x, z)` each predicts from given `P(x, y)` and `P(y, z)`, the
largest discrepancy is under two parts in a hundred (his Table 3). That comparison is a
computation and is not formalized. -/

/-! ### §2.D.3: Three or more alternatives

Extended to three alternatives with independent discriminal processes of arbitrary density,
Thurstone's model gives the probability `P_T(x)` that `x` is judged largest and `P*_T(x)` that
it is judged smallest, and expanding the product of distribution functions yields
`P_T(x) - P*_T(x) = P(x, y) + P(x, z) - 1`. Under the choice axiom for both `P` and `P*`, with
`P*(x, y) = P(y, x)`, the left side is `v x / (v x + v y + v z)` minus the same expression in
the reciprocal scale. Theorem 7 (p. 57) is that the two cannot agree when the pairwise
probabilities are nondegenerate and `P(x, y) + P(x, z) ≠ 1`. The integral identity is taken as
the hypothesis `h`; the theorem is the algebraic contradiction. -/

/-- Theorem 7 (p. 57): for positive scale values `x`, `y`, `z` with `P(x, y) + P(x, z) ≠ 1`,
the difference between the largest-choice and smallest-choice probabilities of `x` under the
choice axiom is not the `P(x, y) + P(x, z) - 1` that independent discriminal processes
require. -/
theorem theorem7 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hne : x / (x + y) + x / (x + z) ≠ 1) :
    x / (x + y + z) - y * z / (x * y + x * z + y * z) ≠ x / (x + y) + x / (x + z) - 1 := by
  intro h
  have hq : 0 < x * y + x * z + y * z := by positivity
  have hrhs : x / (x + y) + x / (x + z) - 1 = (x ^ 2 - y * z) / ((x + y) * (x + z)) := by
    field_simp; ring
  have hlhs : x / (x + y + z) - y * z / (x * y + x * z + y * z) =
      (x ^ 2 - y * z) * (y + z) / ((x + y + z) * (x * y + x * z + y * z)) := by
    field_simp; ring
  have hsq : x ^ 2 - y * z ≠ 0 := fun h0 => hne (by
    have : x / (x + y) + x / (x + z) - 1 = 0 := by rw [hrhs, h0, zero_div]
    linarith)
  rw [hlhs, hrhs, div_eq_div_iff (by positivity) (by positivity)] at h
  have h5 : (y + z) * ((x + y) * (x + z)) = (x + y + z) * (x * y + x * z + y * z) :=
    mul_left_cancel₀ hsq (by linarith)
  nlinarith [mul_pos (mul_pos hx hy) hz]

end Thurstone

section Ranking

open BigOperators Finset Real

variable {S A : Type*} [Fintype A] [DecidableEq A]

/-! ### Ranking probability ([luce-1959], §2.F, pp. 68–74) -/

/-- The tail suffix of a list starting at position `i` (0-indexed).
    Used to represent the shrinking alternative set at each step of ranking. -/
def tailSuffix (ranking : List A) (i : Nat) : Finset A :=
  (ranking.drop i).toFinset

/-- Probability of a single step in the ranking: choosing `ranking[i]` from
    the remaining alternatives `{ranking[i], ranking[i+1],...}`. -/
noncomputable def rankStepProb (ra : RationalAction S A) (s : S)
    (ranking : List A) (i : Nat) : ℝ :=
  match ranking[i]? with
  | none => 1
  | some a => ra.pChoice s (tailSuffix ranking i) a

/-- **Ranking probability** ([luce-1959]'s ranking postulate, p. 72):
    The probability of observing the complete rank ordering `a₁ > a₂ >... > aₙ`
    is the product of successive top-choices from shrinking sets:

    `P(a₁ > a₂ >... > aₙ) =
      P(a₁ | {a₁,...,aₙ}) · P(a₂ | {a₂,...,aₙ}) ·... · P(aₙ₋₁ | {aₙ₋₁, aₙ})`

    Under the Luce model with ratio scale `v`, this becomes:
    `P(a₁ >... > aₙ) = ∏ᵢ v(aᵢ) / ∑ⱼ≥ᵢ v(aⱼ)` -/
noncomputable def rankProb (ra : RationalAction S A) (s : S) (ranking : List A) : ℝ :=
  (List.range ranking.length).foldl (fun acc i => acc * rankStepProb ra s ranking i) 1

/-- Recursive characterization of ranking probability: the first-choice probability
    times the ranking probability of the remaining alternatives. -/
noncomputable def rankProbRec (ra : RationalAction S A) (s : S) : List A → ℝ
  | [] => 1
  | a :: rest => ra.pChoice s (a :: rest).toFinset a * rankProbRec ra s rest

/-- Foldl with multiplication factors out the initial value:
    `foldl (· * f ·) c xs = c * foldl (· * f ·) 1 xs`. -/
private theorem foldl_mul_comm_init (f : Nat → ℝ) (c : ℝ) :
    ∀ xs : List Nat, xs.foldl (fun acc i => acc * f i) c =
      c * xs.foldl (fun acc i => acc * f i) 1
  | [] => by simp
  | x :: xs => by
    simp only [List.foldl]
    rw [foldl_mul_comm_init f (c * f x) xs, foldl_mul_comm_init f (1 * f x) xs]
    ring

/-- Decompose foldl on range(n+1): peel off index 0 and shift the rest.
    Uses `List.range_succ_eq_map` and `List.foldl_map` from mathlib. -/
private theorem foldl_range_succ (f : Nat → ℝ) (n : Nat) :
    (List.range (n + 1)).foldl (fun acc i => acc * f i) 1 =
    f 0 * (List.range n).foldl (fun acc i => acc * f (i + 1)) 1 := by
  rw [List.range_succ_eq_map]
  show (List.map Nat.succ (List.range n)).foldl (fun acc i => acc * f i) (1 * f 0) =
    f 0 * (List.range n).foldl (fun acc i => acc * f (i + 1)) 1
  rw [one_mul, List.foldl_map, foldl_mul_comm_init]

/-- `rankProbRec` agrees with the explicit `rankProb` definition.

    Proof by list induction. The key steps use:
    - `List.range_succ_eq_map` to decompose `range(n+1) = 0 :: map succ (range n)`
    - `List.foldl_map` to shift indices through the map
    - `foldl_mul_comm_init` to factor out the first-choice probability
    - Definitional equalities: `rankStepProb (a::rest) 0 = pChoice` and
      `rankStepProb (a::rest) (i+1) = rankStepProb rest i` -/
theorem rankProbRec_eq_rankProb (ra : RationalAction S A) (s : S) (ranking : List A) :
    rankProbRec ra s ranking = rankProb ra s ranking := by
  induction ranking with
  | nil => rfl
  | cons a rest ih =>
    show ra.pChoice s (a :: rest).toFinset a * rankProbRec ra s rest =
      (List.range (rest.length + 1)).foldl
        (fun acc i => acc * rankStepProb ra s (a :: rest) i) 1
    rw [ih, rankProb, foldl_range_succ]
    -- Both sides now match by definitional equalities:
    -- rankStepProb (a::rest) 0 = pChoice (since (a::rest)[0]? = some a
    --   and tailSuffix (a::rest) 0 = (a::rest).toFinset)
    -- rankStepProb (a::rest) (i+1) = rankStepProb rest i (since
    --   (a::rest)[i+1]? = rest[i]? and tailSuffix (a::rest) (i+1) = tailSuffix rest i)
    congr 1

/-- Each `rankStepProb` is non-negative: either 1 (out of range) or `pChoice`. -/
private theorem rankStepProb_nonneg (ra : RationalAction S A) (s : S)
    (ranking : List A) (i : Nat) :
    0 ≤ rankStepProb ra s ranking i := by
  simp only [rankStepProb]
  cases ranking[i]? with
  | none => linarith
  | some a => exact ra.pChoice_nonneg s _ a

private theorem foldl_mul_nonneg {f : Nat → ℝ} {init : ℝ}
    (hinit : 0 ≤ init) (hf : ∀ i, 0 ≤ f i) :
    ∀ l : List Nat, 0 ≤ l.foldl (fun acc i => acc * f i) init
  | [] => by simpa using hinit
  | x :: xs => foldl_mul_nonneg (mul_nonneg hinit (hf x)) hf xs

/-- Ranking probability is non-negative: each factor is a `pChoice` value,
    hence non-negative. -/
theorem rankProb_nonneg (ra : RationalAction S A) (s : S) (ranking : List A) :
    0 ≤ rankProb ra s ranking :=
  foldl_mul_nonneg one_pos.le (rankStepProb_nonneg ra s ranking) _

/-- `rankProbRec` is positive when all scores are positive. -/
theorem rankProbRec_pos (ra : RationalAction S A) (s : S) (ranking : List A)
    (hpos : ∀ b, 0 < ra.score s b) : 0 < rankProbRec ra s ranking := by
  induction ranking with
  | nil => simp [rankProbRec]
  | cons a rest ih =>
    show 0 < ra.pChoice s (a :: rest).toFinset a * rankProbRec ra s rest
    exact mul_pos
      (RationalAction.pChoice_pos (by simp [List.toFinset_cons]) fun b _ => hpos b) ih

/-- Ranking probability is positive when all scores are positive. -/
theorem rankProb_pos (ra : RationalAction S A) (s : S) (ranking : List A)
    (hpos : ∀ b, 0 < ra.score s b) : 0 < rankProb ra s ranking :=
  rankProbRec_eq_rankProb ra s ranking ▸ rankProbRec_pos ra s ranking hpos

/-! ### Score-ratio form -/

/-- The score-ratio factor at position `i`: `v(aᵢ) / ∑ⱼ≥ᵢ v(aⱼ)`.
    This is the `i`-th factor in the score-product form of ranking probability. -/
noncomputable def scoreRatio (ra : RationalAction S A) (s : S)
    (ranking : List A) (i : Nat) : ℝ :=
  match ranking[i]? with
  | none => 1
  | some a =>
    let tailSum := ∑ b ∈ tailSuffix ranking i, ra.score s b
    if tailSum = 0 then 0 else ra.score s a / tailSum

/-- The score-product form of ranking probability:
    `∏ᵢ v(aᵢ) / ∑ⱼ≥ᵢ v(aⱼ)`. -/
noncomputable def rankProbScoreProd (ra : RationalAction S A) (s : S)
    (ranking : List A) : ℝ :=
  (List.range ranking.length).foldl (fun acc i => acc * scoreRatio ra s ranking i) 1

omit [Fintype A] in
/-- If `ranking[i]? = some a`, then `a` is in the tail suffix at position `i`.
    This is because `a = ranking[i]` is the head of `ranking.drop i`. -/
private theorem mem_tailSuffix_of_getElem?
    {ranking : List A} {i : Nat} {a : A}
    (h : ranking[i]? = some a) :
    a ∈ tailSuffix ranking i := by
  simp only [tailSuffix, List.mem_toFinset]
  have hi : i < ranking.length := by
    by_contra hc; push Not at hc
    simp [List.getElem?_eq_none hc] at h
  rw [List.drop_eq_getElem_cons hi]
  have hval : ranking[i] = a := by
    have := List.getElem?_eq_getElem hi
    rw [h] at this; exact Option.some.inj this.symm
  rw [hval]; exact List.Mem.head _

/-- `rankStepProb` equals `scoreRatio` at every position: the `pChoice`
    formulation and the explicit score/sum formulation agree because
    `ranking[i]` is always in the tail suffix at position `i`. -/
private theorem rankStepProb_eq_scoreRatio (ra : RationalAction S A) (s : S)
    (ranking : List A) (i : Nat) :
    rankStepProb ra s ranking i = scoreRatio ra s ranking i := by
  simp only [rankStepProb, scoreRatio]
  cases h : ranking[i]? with
  | none => rfl
  | some a =>
    have hmem : a ∈ tailSuffix ranking i := mem_tailSuffix_of_getElem? h
    simp only [RationalAction.pChoice, hmem, ↓reduceIte]

/-- **Score form**: ranking probability equals the product of score ratios. -/
theorem rankProb_eq_score_prod (ra : RationalAction S A) (s : S) (ranking : List A)
    (_hnd : ranking.Nodup) :
    rankProb ra s ranking = rankProbScoreProd ra s ranking := by
  simp only [rankProb, rankProbScoreProd]
  congr 1
  ext acc i
  exact congrArg (acc * ·) (rankStepProb_eq_scoreRatio ra s ranking i)

/-! ### Summation over permutations -/

/-- All permutations of a finset, as lists. -/
noncomputable def allRankings (T : Finset A) : Finset (List A) :=
  T.val.toList.permutations.toFinset

omit [Fintype A] in
/-- Every ranking in `allRankings T` is a permutation of `T`.

    Uses `List.mem_permutations`, `List.perm_ext_iff_of_nodup`, and
    `Multiset.mem_toList` from mathlib to connect the List-level
    permutation API with Finset membership. -/
theorem mem_allRankings_iff (T : Finset A) (ranking : List A) :
    ranking ∈ allRankings T ↔ ranking.toFinset = T ∧ ranking.Nodup := by
  simp only [allRankings, List.mem_toFinset, List.mem_permutations]
  have hT_nodup : T.val.toList.Nodup := by
    rw [← Multiset.coe_nodup, Multiset.coe_toList]; exact T.nodup
  constructor
  · intro hperm
    constructor
    · ext x
      simp only [List.mem_toFinset]
      rw [hperm.mem_iff, Multiset.mem_toList]; exact Iff.rfl
    · exact hperm.nodup_iff.mpr hT_nodup
  · intro ⟨hfs, hnd⟩
    rw [List.perm_ext_iff_of_nodup hnd hT_nodup]
    intro x
    rw [← List.mem_toFinset (l := ranking), hfs,
        Multiset.mem_toList, Finset.mem_val]

/-! ### Decomposition of `allRankings` by first element -/

omit [Fintype A] in
/-- Cons into allRankings: if `rest ∈ allRankings (T.erase a)` and `a ∈ T`,
    then `a :: rest ∈ allRankings T`. -/
private theorem cons_mem_allRankings {T : Finset A} {a : A} {rest : List A}
    (ha : a ∈ T) (hrest : rest ∈ allRankings (T.erase a)) :
    a :: rest ∈ allRankings T := by
  rw [mem_allRankings_iff] at hrest ⊢
  obtain ⟨hfs, hnd⟩ := hrest
  constructor
  · simp only [List.toFinset_cons, hfs, Finset.insert_erase ha]
  · rw [List.nodup_cons]
    refine ⟨fun h => ?_, hnd⟩
    exact (Finset.mem_erase.mp (hfs ▸ List.mem_toFinset.mpr h)).1 rfl

omit [Fintype A] in
/-- Extract first element: if `a :: rest ∈ allRankings T`,
    then `a ∈ T` and `rest ∈ allRankings (T.erase a)`. -/
private theorem of_cons_mem_allRankings {T : Finset A} {a : A} {rest : List A}
    (h : a :: rest ∈ allRankings T) :
    a ∈ T ∧ rest ∈ allRankings (T.erase a) := by
  rw [mem_allRankings_iff] at h
  obtain ⟨hfs, hnd⟩ := h
  rw [List.nodup_cons] at hnd
  constructor
  · have : a ∈ (a :: rest).toFinset := by simp
    rw [hfs] at this; exact this
  · rw [mem_allRankings_iff]
    constructor
    · rw [List.toFinset_cons] at hfs
      have ha_nin : a ∉ rest.toFinset := by rw [List.mem_toFinset]; exact hnd.1
      rw [← hfs, Finset.erase_insert ha_nin]
    · exact hnd.2

omit [Fintype A] in
/-- Rankings of a nonempty set are nonempty lists. -/
private theorem allRankings_ne_nil {T : Finset A} (hT : T.Nonempty)
    {r : List A} (hr : r ∈ allRankings T) : r ≠ [] := by
  intro heq; subst heq
  rw [mem_allRankings_iff] at hr
  simp at hr
  exact Finset.Nonempty.ne_empty hT hr.symm

omit [Fintype A] in
/-- `allRankings T = ⋃_{a ∈ T} image (cons a) (allRankings (T.erase a))`. -/
private theorem allRankings_eq_biUnion (T : Finset A) (hT : T.Nonempty) :
    allRankings T = T.biUnion (fun a => (allRankings (T.erase a)).image (List.cons a)) := by
  ext r
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · intro hr
    have hne := allRankings_ne_nil hT hr
    obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨ha, hrest⟩ := of_cons_mem_allRankings hr
    exact ⟨a, ha, rest, hrest, rfl⟩
  · rintro ⟨a, ha, rest, hrest, rfl⟩
    exact cons_mem_allRankings ha hrest

omit [Fintype A] in
/-- Cons-images for distinct first elements are disjoint. -/
private theorem cons_image_pairwise_disjoint (T : Finset A) :
    (T : Set A).PairwiseDisjoint
      (fun a => (allRankings (T.erase a)).image (List.cons a)) := by
  intro a _ b _ hab
  simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
  rintro r ⟨_, _, rfl⟩ ⟨_, _, h⟩
  exact hab (List.cons.inj h).1.symm

omit [Fintype A] in
/-- Decompose a sum over `allRankings T` by first element. -/
private theorem sum_allRankings_by_first (T : Finset A) (hT : T.Nonempty)
    (f : List A → ℝ) :
    ∑ r ∈ allRankings T, f r =
    ∑ a ∈ T, ∑ rest ∈ allRankings (T.erase a), f (a :: rest) := by
  rw [allRankings_eq_biUnion T hT, Finset.sum_biUnion (cons_image_pairwise_disjoint T)]
  congr 1; ext a
  rw [Finset.sum_image]
  intro r₁ _ r₂ _ h
  exact List.cons.inj h |>.2

/-- `rankProb (a :: rest)` factors as `pChoice s T a * rankProb rest`
    when `(a :: rest).toFinset = T`. -/
private theorem rankProb_cons_eq (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (rest : List A)
    (hfs : (a :: rest).toFinset = T) :
    rankProb ra s (a :: rest) = ra.pChoice s T a * rankProb ra s rest := by
  rw [← rankProbRec_eq_rankProb, ← rankProbRec_eq_rankProb]
  show ra.pChoice s (a :: rest).toFinset a * rankProbRec ra s rest =
    ra.pChoice s T a * rankProbRec ra s rest
  rw [hfs]

/-! ### Ranking probabilities sum to 1 -/

/-- Score positivity propagates to erased subsets. -/
private theorem score_pos_erase {ra : RationalAction S A} {s : S}
    {T : Finset A} (hpos : ∀ a ∈ T, 0 < ra.score s a)
    (a : A) : ∀ b ∈ T.erase a, 0 < ra.score s b :=
  fun b hb => hpos b (Finset.mem_of_mem_erase hb)

omit [DecidableEq A] in
/-- Score positivity implies nonzero sum over nonempty sets. -/
private theorem score_sum_ne_zero {ra : RationalAction S A} {s : S}
    {T : Finset A} (hT : T.Nonempty) (hpos : ∀ a ∈ T, 0 < ra.score s a) :
    ∑ b ∈ T, ra.score s b ≠ 0 := by
  obtain ⟨a, ha⟩ := hT
  exact ne_of_gt (Finset.sum_pos (fun b hb => hpos b hb) ⟨a, ha⟩)

/-- Core induction: ranking probabilities sum to 1 for any finset
    with strictly positive scores. -/
private theorem rankProb_sum_eq_one_aux (ra : RationalAction S A) (s : S) :
    ∀ (n : ℕ) (T : Finset A), T.card = n → (∀ a ∈ T, 0 < ra.score s a) →
    ∑ r ∈ allRankings T, rankProb ra s r = 1 := by
  intro n
  induction n with
  | zero =>
    intro T hcard _
    have hT_empty : T = ∅ := Finset.card_eq_zero.mp hcard
    subst hT_empty
    simp only [allRankings, Finset.empty_val, Multiset.toList_zero, List.permutations_nil,
               List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
    simp [rankProb]
  | succ n ih =>
    intro T hcard hpos
    have hT : T.Nonempty := Finset.card_pos.mp (by omega)
    rw [sum_allRankings_by_first T hT]
    have step : ∀ a ∈ T,
        ∑ rest ∈ allRankings (T.erase a), rankProb ra s (a :: rest) =
        ra.pChoice s T a := by
      intro a ha
      have hcard_erase : (T.erase a).card = n := by
        rw [Finset.card_erase_of_mem ha, hcard]; omega
      have hpos_erase := score_pos_erase hpos a
      have : ∀ rest ∈ allRankings (T.erase a),
          rankProb ra s (a :: rest) = ra.pChoice s T a * rankProb ra s rest := by
        intro rest hrest
        apply rankProb_cons_eq
        rw [mem_allRankings_iff] at hrest
        simp [List.toFinset_cons, hrest.1, Finset.insert_erase ha]
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
      rw [ih (T.erase a) hcard_erase hpos_erase, mul_one]
    rw [Finset.sum_congr rfl step]
    exact ra.pChoice_sum_eq_one s T (score_sum_ne_zero hT hpos)

/-- **Ranking probabilities sum to 1**: over all `n!` permutations of the
    alternative set, ranking probabilities form a proper distribution.
    Requires strictly positive scores (Luce's ratio scale assumption). -/
theorem rankProb_sum_eq_one (ra : RationalAction S A) (s : S)
    (T : Finset A) (hpos : ∀ a ∈ T, 0 < ra.score s a) :
    ∑ r ∈ allRankings T, rankProb ra s r = 1 :=
  rankProb_sum_eq_one_aux ra s T.card T rfl hpos

/-! ### Marginalization: recovering `pChoice` -/

/-- Rankings starting with a given element `a`. -/
noncomputable def rankingsStartingWith (T : Finset A) (a : A) : Finset (List A) :=
  (allRankings T).filter (fun r => r.head? = some a)

omit [Fintype A] in
/-- Rankings starting with `a` biject with `allRankings (T.erase a)` via cons. -/
private theorem rankingsStartingWith_eq (T : Finset A) (a : A) (ha : a ∈ T) :
    rankingsStartingWith T a = (allRankings (T.erase a)).image (List.cons a) := by
  ext r
  simp only [rankingsStartingWith, Finset.mem_filter, Finset.mem_image]
  constructor
  · intro ⟨hr, hhead⟩
    obtain ⟨a', rest, rfl⟩ : ∃ a' rest, r = a' :: rest := by
      cases r with
      | nil => simp at hhead
      | cons a' rest => exact ⟨a', rest, rfl⟩
    simp at hhead; subst hhead
    obtain ⟨_, hrest⟩ := of_cons_mem_allRankings hr
    exact ⟨rest, hrest, rfl⟩
  · rintro ⟨rest, hrest, rfl⟩
    exact ⟨cons_mem_allRankings ha hrest, by simp⟩

/-- **Marginal first-choice**: summing the ranking probability over all
    rankings that start with `a` recovers the choice probability
    `pChoice(a, T)`. ([luce-1959]'s own Theorem 9, p. 72, is the pairwise
    analogue: `P(x,y)` is recovered by summing over rankings placing `x`
    above `y`.) -/
theorem rankProb_marginal_first (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (ha : a ∈ T)
    (hpos : ∀ b ∈ T, 0 < ra.score s b) :
    ∑ r ∈ rankingsStartingWith T a, rankProb ra s r = ra.pChoice s T a := by
  rw [rankingsStartingWith_eq T a ha]
  rw [Finset.sum_image (fun r₁ _ r₂ _ h => (List.cons.inj h).2)]
  have hrw : ∀ rest ∈ allRankings (T.erase a),
      rankProb ra s (a :: rest) = ra.pChoice s T a * rankProb ra s rest := by
    intro rest hrest
    apply rankProb_cons_eq
    rw [mem_allRankings_iff] at hrest
    simp [List.toFinset_cons, hrest.1, Finset.insert_erase ha]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  have hcard_pos : 0 < (T.erase a).card ∨ (T.erase a).card = 0 := by omega
  rcases hcard_pos with hcp | hcp
  · rw [rankProb_sum_eq_one_aux ra s (T.erase a).card (T.erase a) rfl
          (score_pos_erase hpos a), mul_one]
  · have : T.erase a = ∅ := Finset.card_eq_zero.mp hcp
    simp only [this, allRankings, Finset.empty_val, Multiset.toList_zero,
               List.permutations_nil, List.toFinset_cons, List.toFinset_nil,
               Finset.insert_empty, Finset.sum_singleton, rankProb]
    simp [mul_one]

/-! ### Adjacent transpositions -/

/-- One step of `rankProbRec` in score form, for a head not repeated in the
    tail. -/
theorem rankProbRec_cons (ra : RationalAction S A) (s : S) {a : A} {l : List A}
    (ha : a ∉ l) (hpos : ∀ b, 0 < ra.score s b) :
    rankProbRec ra s (a :: l) =
      ra.score s a / (ra.score s a + ∑ b ∈ l.toFinset, ra.score s b) *
        rankProbRec ra s l := by
  have hnot : a ∉ l.toFinset := by rwa [List.mem_toFinset]
  have hsum : ra.score s a + ∑ b ∈ l.toFinset, ra.score s b ≠ 0 :=
    (add_pos_of_pos_of_nonneg (hpos a) (Finset.sum_nonneg fun b _ => (hpos b).le)).ne'
  show ra.pChoice s (a :: l).toFinset a * rankProbRec ra s l = _
  rw [List.toFinset_cons,
    ra.pChoice_eq_div s _ a (Finset.mem_insert_self a l.toFinset)
      (by rwa [Finset.sum_insert hnot]),
    Finset.sum_insert hnot]

/-- Swapping two adjacent elements scales the ranking probability by
    `(v x + S) / (v y + S)`, where `S` sums the scores of the remaining
    alternatives — not by the naive `v x / v y`: the second step of each
    ranking draws from a different set. -/
theorem rankProb_swap_div (ra : RationalAction S A) (s : S) (x y : A)
    (rest : List A) (hx : x ∉ rest) (hy : y ∉ rest)
    (hpos : ∀ b, 0 < ra.score s b) :
    rankProb ra s (x :: y :: rest) / rankProb ra s (y :: x :: rest) =
      (ra.score s x + ∑ b ∈ rest.toFinset, ra.score s b) /
        (ra.score s y + ∑ b ∈ rest.toFinset, ra.score s b) := by
  rw [← rankProbRec_eq_rankProb, ← rankProbRec_eq_rankProb]
  have hS : 0 ≤ ∑ b ∈ rest.toFinset, ra.score s b :=
    Finset.sum_nonneg fun b _ => (hpos b).le
  have hvx := (hpos x).ne'
  have hvy := (hpos y).ne'
  have htail := (rankProbRec_pos ra s rest hpos).ne'
  have hxS := (add_pos_of_pos_of_nonneg (hpos x) hS).ne'
  have hyS := (add_pos_of_pos_of_nonneg (hpos y) hS).ne'
  have hT : (0:ℝ) < ∑ b ∈ (x :: y :: rest).toFinset, ra.score s b :=
    Finset.sum_pos (fun b _ => hpos b) ⟨x, by simp⟩
  have hT_eq : (y :: x :: rest).toFinset = (x :: y :: rest).toFinset := by
    simp only [List.toFinset_cons]
    exact Finset.insert_comm y x rest.toFinset
  show ra.pChoice s (x :: y :: rest).toFinset x * rankProbRec ra s (y :: rest) /
      (ra.pChoice s (y :: x :: rest).toFinset y * rankProbRec ra s (x :: rest)) = _
  rw [hT_eq, rankProbRec_cons ra s hy hpos, rankProbRec_cons ra s hx hpos,
    ra.pChoice_eq_div s _ x (by simp) hT.ne', ra.pChoice_eq_div s _ y (by simp) hT.ne']
  field_simp

/-- Swapping adjacent elements into score order strictly increases ranking
    probability: if `v y < v x`, then `x` before `y` is the more probable
    order. -/
theorem rankProb_swap_lt_of_score_lt (ra : RationalAction S A) (s : S) {x y : A}
    (rest : List A) (hx : x ∉ rest) (hy : y ∉ rest)
    (hpos : ∀ b, 0 < ra.score s b) (hlt : ra.score s y < ra.score s x) :
    rankProb ra s (y :: x :: rest) < rankProb ra s (x :: y :: rest) := by
  have hden := rankProb_pos ra s (y :: x :: rest) hpos
  have hS : 0 ≤ ∑ b ∈ rest.toFinset, ra.score s b :=
    Finset.sum_nonneg fun b _ => (hpos b).le
  have h1 : 1 < rankProb ra s (x :: y :: rest) / rankProb ra s (y :: x :: rest) := by
    rw [rankProb_swap_div ra s x y rest hx hy hpos,
      one_lt_div (add_pos_of_pos_of_nonneg (hpos y) hS)]
    linarith
  exact (one_lt_div hden).mp h1

/-! ### Expected rank -/

/-- The rank of element `a` in a ranking (1-indexed, so rank 1 = best).
    Returns 0 if `a` is not in the ranking. -/
def rankOf (ranking : List A) (a : A) : Nat :=
  if a ∈ ranking then ranking.findIdx (· == a) + 1 else 0

/-- Expected rank of alternative `a` under the ranking distribution.

    `E[rank(a)] = ∑_σ P(σ) · rank(a, σ)`

    The monotonicity theorem `expectedRank_lt_of_score_gt` shows that
    alternatives with higher `v(a)` have lower (better) expected rank. -/
noncomputable def expectedRank (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) : ℝ :=
  ∑ r ∈ allRankings T, rankProb ra s r * (rankOf r a : ℝ)

/-! ### Expected rank monotonicity: infrastructure -/

omit [Fintype A] in
/-- `rankOf (a :: rest) a = 1`: the first element has rank 1. -/
private theorem rankOf_cons_self (a : A) (rest : List A) :
    rankOf (a :: rest) a = 1 := by
  simp [rankOf, List.findIdx_cons]

omit [Fintype A] in
/-- `rankOf (b :: rest) a = rankOf rest a + 1` when `b ≠ a` and `a ∈ rest`. -/
private theorem rankOf_cons_ne {b a : A} {rest : List A}
    (hne : b ≠ a) (ha : a ∈ rest) :
    rankOf (b :: rest) a = rankOf rest a + 1 := by
  have hmem : a ∈ b :: rest := List.mem_cons_of_mem b ha
  simp only [rankOf, hmem, ha, ↓reduceIte, List.findIdx_cons]
  simp [show (b == a) = false from by simp [hne]]

/-! ### Expected rank decomposition:
`E[rank(a,T)] = 1 + ∑_{b≠a} pChoice(b) · E[rank(a,T\{b})]` -/

/-- Inner sum when the first element equals `a`: contributes `pChoice(a, T)`. -/
private theorem expectedRank_first_self (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (ha : a ∈ T)
    (hpos : ∀ b ∈ T, 0 < ra.score s b) :
    ∑ rest ∈ allRankings (T.erase a),
      rankProb ra s (a :: rest) * (rankOf (a :: rest) a : ℝ) =
    ra.pChoice s T a := by
  have hsub : ∀ rest ∈ allRankings (T.erase a),
      rankProb ra s (a :: rest) * (rankOf (a :: rest) a : ℝ) =
      ra.pChoice s T a * rankProb ra s rest := by
    intro rest hrest
    rw [show (rankOf (a :: rest) a : ℝ) = 1 from by simp [rankOf_cons_self]]
    rw [mul_one]
    apply rankProb_cons_eq
    rw [mem_allRankings_iff] at hrest
    simp [List.toFinset_cons, hrest.1, Finset.insert_erase ha]
  rw [Finset.sum_congr rfl hsub, ← Finset.mul_sum,
      rankProb_sum_eq_one_aux ra s _ _ rfl (score_pos_erase hpos a), mul_one]

/-- Inner sum when first element is `b ≠ a`:
    contributes `pChoice(b, T) · (1 + E[rank(a, T\{b})])`. -/
private theorem expectedRank_first_ne (ra : RationalAction S A) (s : S)
    (T : Finset A) (a b : A) (ha : a ∈ T) (hb : b ∈ T) (hne : b ≠ a)
    (hpos : ∀ c ∈ T, 0 < ra.score s c) :
    ∑ rest ∈ allRankings (T.erase b),
      rankProb ra s (b :: rest) * (rankOf (b :: rest) a : ℝ) =
    ra.pChoice s T b * (1 + expectedRank ra s (T.erase b) a) := by
  have ha_erase : a ∈ T.erase b := Finset.mem_erase.mpr ⟨hne.symm, ha⟩
  have ha_rest : ∀ rest ∈ allRankings (T.erase b), a ∈ rest := by
    intro rest hrest
    rw [mem_allRankings_iff] at hrest
    exact List.mem_toFinset.mp (hrest.1 ▸ ha_erase)
  have hsub : ∀ rest ∈ allRankings (T.erase b),
      rankProb ra s (b :: rest) * (rankOf (b :: rest) a : ℝ) =
      ra.pChoice s T b * (rankProb ra s rest * (rankOf rest a : ℝ) +
        rankProb ra s rest) := by
    intro rest hrest
    have hfact : rankProb ra s (b :: rest) = ra.pChoice s T b * rankProb ra s rest := by
      apply rankProb_cons_eq
      rw [mem_allRankings_iff] at hrest
      simp [List.toFinset_cons, hrest.1, Finset.insert_erase hb]
    have hrk : (rankOf (b :: rest) a : ℝ) = (rankOf rest a : ℝ) + 1 := by
      rw [rankOf_cons_ne hne (ha_rest rest hrest)]; push_cast; ring
    rw [hfact, hrk]; ring
  rw [Finset.sum_congr rfl hsub, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [rankProb_sum_eq_one_aux ra s _ _ rfl (score_pos_erase hpos b)]
  unfold expectedRank; congr 1; ring

/-- **Expected rank decomposition**: conditioning on the first element.
    `E[rank(a, T)] = 1 + ∑_{b ∈ T\{a}} pChoice(b, T) · E[rank(a, T\{b})]` -/
private theorem expectedRank_decomp (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (ha : a ∈ T)
    (hpos : ∀ b ∈ T, 0 < ra.score s b) :
    expectedRank ra s T a =
    1 + ∑ b ∈ T.erase a, ra.pChoice s T b * expectedRank ra s (T.erase b) a := by
  have hT : T.Nonempty := ⟨a, ha⟩
  show ∑ r ∈ allRankings T, rankProb ra s r * (rankOf r a : ℝ) =
    1 + ∑ b ∈ T.erase a, ra.pChoice s T b * expectedRank ra s (T.erase b) a
  rw [sum_allRankings_by_first T hT]
  -- Split: ∑_{b ∈ T} = f(a) + ∑_{b ∈ T.erase a}
  rw [← Finset.add_sum_erase T _ ha]
  rw [expectedRank_first_self ra s T a ha hpos]
  -- Rewrite each b ≠ a term
  have h_ne : ∀ b ∈ T.erase a,
      (∑ rest ∈ allRankings (T.erase b),
        rankProb ra s (b :: rest) * (rankOf (b :: rest) a : ℝ)) =
      ra.pChoice s T b * (1 + expectedRank ra s (T.erase b) a) := by
    intro b hb
    exact expectedRank_first_ne ra s T a b ha (Finset.mem_of_mem_erase hb)
      (ne_of_mem_erase hb) hpos
  rw [Finset.sum_congr rfl h_ne]
  -- pChoice(a) + ∑ pChoice(b) * (1 + E[...]) = 1 + ∑ pChoice(b) * E[...]
  have hexpand : ∀ b ∈ T.erase a,
      ra.pChoice s T b * (1 + expectedRank ra s (T.erase b) a) =
      ra.pChoice s T b + ra.pChoice s T b * expectedRank ra s (T.erase b) a :=
    fun _ _ => by ring
  rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib]
  have h1 : ra.pChoice s T a + ∑ b ∈ T.erase a, ra.pChoice s T b = 1 := by
    rw [Finset.add_sum_erase T _ ha]
    exact ra.pChoice_sum_eq_one s T (score_sum_ne_zero hT hpos)
  linarith

omit [Fintype A] in
/-- For `a ∈ T`, `rankOf r a ≥ 1` for any ranking `r ∈ allRankings T`. -/
private theorem rankOf_ge_one_of_mem {T : Finset A} {a : A} (ha : a ∈ T)
    {r : List A} (hr : r ∈ allRankings T) : 1 ≤ rankOf r a := by
  rw [mem_allRankings_iff] at hr
  have : a ∈ r := List.mem_toFinset.mp (hr.1 ▸ ha)
  simp [rankOf, this]

/-- Expected rank is at least 1 for any element in the set. -/
private theorem expectedRank_ge_one (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (ha : a ∈ T)
    (hpos : ∀ b ∈ T, 0 < ra.score s b) :
    1 ≤ expectedRank ra s T a := by
  have hT : T.Nonempty := ⟨a, ha⟩
  -- E[rank(a)] = ∑ P(r) * rank(r,a) ≥ ∑ P(r) * 1 = 1
  calc expectedRank ra s T a
      = ∑ r ∈ allRankings T, rankProb ra s r * (rankOf r a : ℝ) := rfl
    _ ≥ ∑ r ∈ allRankings T, rankProb ra s r * 1 := by
        apply Finset.sum_le_sum; intro r hr
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast rankOf_ge_one_of_mem ha hr)
          (rankProb_nonneg ra s r)
    _ = 1 := by simp [rankProb_sum_eq_one ra s T hpos]

/-! ### Cross-set monotonicity -/

/-- Singleton expected rank: `E[rank(a, {a})] = 1`. -/
private theorem expectedRank_singleton (ra : RationalAction S A) (s : S) (a : A)
    (hpos : 0 < ra.score s a) :
    expectedRank ra s {a} a = 1 := by
  have hpos' : ∀ b ∈ ({a} : Finset A), 0 < ra.score s b := by simp; exact hpos
  rw [expectedRank_decomp ra s {a} a (Finset.mem_singleton_self a) hpos']
  simp [Finset.erase_singleton]

/-- `pChoice(c, S₁) ≤ pChoice(c, S₂)` when `S₁` has a higher-scored element than `S₂`.
    `S₁ = insert a₁ C`, `S₂ = insert a₂ C`, `v(a₁) ≥ v(a₂)`, `c ∈ C`. -/
private theorem pChoice_cross_le {ra : RationalAction S A} {s : S}
    {S₁ S₂ : Finset A} {c : A} (hc₁ : c ∈ S₁) (hc₂ : c ∈ S₂)
    (hpos₁ : ∀ b ∈ S₁, 0 < ra.score s b)
    (hpos₂ : ∀ b ∈ S₂, 0 < ra.score s b)
    (hsum_le : ∑ b ∈ S₂, ra.score s b ≤ ∑ b ∈ S₁, ra.score s b) :
    ra.pChoice s S₁ c ≤ ra.pChoice s S₂ c := by
  have hsum₁_pos : 0 < ∑ b ∈ S₁, ra.score s b :=
    Finset.sum_pos (fun b hb => hpos₁ b hb) ⟨c, hc₁⟩
  have hsum₂_pos : 0 < ∑ b ∈ S₂, ra.score s b :=
    Finset.sum_pos (fun b hb => hpos₂ b hb) ⟨c, hc₂⟩
  simp only [RationalAction.pChoice, hc₁, hc₂, ne_of_gt hsum₁_pos, ne_of_gt hsum₂_pos,
    ↓reduceIte]
  exact div_le_div_of_nonneg_left (le_of_lt (hpos₁ c hc₁)) hsum₂_pos hsum_le

/-- **Cross-set monotonicity**: a higher-scored element gets a better expected rank
    when competing against the same field.

    If `S₁ = insert a₁ C` and `S₂ = insert a₂ C` with `v(a₁) ≥ v(a₂)`, then
    `E[rank(a₁, S₁)] ≤ E[rank(a₂, S₂)]`.

    Proof by induction on `|C|`. The decomposition
    `E[rank(aᵢ, Sᵢ)] = 1 + ∑_{c∈C} pChoice(c, Sᵢ) · E[rank(aᵢ, Sᵢ\{c})]`
    gives a term-by-term comparison: `pChoice(c, S₂) ≥ pChoice(c, S₁)` (larger
    denominator for S₁) and `E[rank(a₂, S₂\{c})] ≥ E[rank(a₁, S₁\{c})]` (by IH). -/
private theorem expectedRank_cross_le_aux (ra : RationalAction S A) (s : S) :
    ∀ (n : ℕ) (C : Finset A) (a₁ a₂ : A),
    C.card = n → (ha₁ : a₁ ∉ C) → (ha₂ : a₂ ∉ C) →
    (∀ b ∈ insert a₁ C, 0 < ra.score s b) →
    (∀ b ∈ insert a₂ C, 0 < ra.score s b) →
    ra.score s a₁ ≥ ra.score s a₂ →
    expectedRank ra s (insert a₁ C) a₁ ≤
    expectedRank ra s (insert a₂ C) a₂ := by
  intro n
  induction n with
  | zero =>
    intro C a₁ a₂ hcard ha₁ ha₂ hpos₁ hpos₂ _
    have hC : C = ∅ := Finset.card_eq_zero.mp hcard
    subst hC
    simp only [Finset.insert_empty]
    have h₁ := expectedRank_singleton ra s a₁ (hpos₁ a₁ (Finset.mem_singleton_self a₁))
    have h₂ := expectedRank_singleton ra s a₂ (hpos₂ a₂ (Finset.mem_singleton_self a₂))
    linarith
  | succ n ih =>
    intro C a₁ a₂ hcard ha₁ ha₂ hpos₁ hpos₂ hge
    -- Decompose: E[rank(aᵢ, Sᵢ)] = 1 + ∑_{c ∈ C} pChoice(c, Sᵢ) * E[rank(aᵢ, Sᵢ\{c})]
    -- where Sᵢ = insert aᵢ C, Sᵢ.erase aᵢ = C
    rw [expectedRank_decomp ra s _ a₁ (Finset.mem_insert_self a₁ C) hpos₁,
        expectedRank_decomp ra s _ a₂ (Finset.mem_insert_self a₂ C) hpos₂,
        Finset.erase_insert ha₁, Finset.erase_insert ha₂]
    -- Goal: 1 + ∑_{c∈C} p(c,S₁)·E₁(c) ≤ 1 + ∑_{c∈C} p(c,S₂)·E₂(c)
    suffices h : ∑ c ∈ C, ra.pChoice s (insert a₁ C) c *
          expectedRank ra s ((insert a₁ C).erase c) a₁ ≤
        ∑ c ∈ C, ra.pChoice s (insert a₂ C) c *
          expectedRank ra s ((insert a₂ C).erase c) a₂ by linarith
    -- Two-step inequality: ∑ p₁·E₁ ≤ ∑ p₁·E₂ ≤ ∑ p₂·E₂
    -- where E_i(c) = expectedRank(aᵢ, Sᵢ\{c}) and Sᵢ\{c} = insert aᵢ (C\{c})
    have hS₁_erase : ∀ c ∈ C, (insert a₁ C).erase c = insert a₁ (C.erase c) :=
      fun c hc => Finset.erase_insert_of_ne (fun h => ha₁ (h ▸ hc))
    have hS₂_erase : ∀ c ∈ C, (insert a₂ C).erase c = insert a₂ (C.erase c) :=
      fun c hc => Finset.erase_insert_of_ne (fun h => ha₂ (h ▸ hc))
    -- Sum over S₂ ≤ sum over S₁ (for pChoice_cross_le)
    have hsum_le :
        ∑ b ∈ insert a₂ C, ra.score s b ≤ ∑ b ∈ insert a₁ C, ra.score s b := by
      rw [Finset.sum_insert ha₁, Finset.sum_insert ha₂]; linarith
    calc ∑ c ∈ C, ra.pChoice s (insert a₁ C) c *
              expectedRank ra s ((insert a₁ C).erase c) a₁
        ≤ ∑ c ∈ C, ra.pChoice s (insert a₁ C) c *
              expectedRank ra s ((insert a₂ C).erase c) a₂ := by
          apply Finset.sum_le_sum; intro c hc
          apply mul_le_mul_of_nonneg_left _ (ra.pChoice_nonneg s _ c)
          rw [hS₁_erase c hc, hS₂_erase c hc]
          have hcard_c : (C.erase c).card = n := by
            rw [Finset.card_erase_of_mem hc, hcard]; omega
          have hsub₁ : insert a₁ (C.erase c) ⊆ insert a₁ C :=
            Finset.insert_subset_insert a₁ (Finset.erase_subset c C)
          have hsub₂ : insert a₂ (C.erase c) ⊆ insert a₂ C :=
            Finset.insert_subset_insert a₂ (Finset.erase_subset c C)
          exact ih (C.erase c) a₁ a₂ hcard_c
            (fun h => ha₁ (Finset.mem_of_mem_erase h))
            (fun h => ha₂ (Finset.mem_of_mem_erase h))
            (fun b hb => hpos₁ b (hsub₁ hb))
            (fun b hb => hpos₂ b (hsub₂ hb))
            hge
      _ ≤ ∑ c ∈ C, ra.pChoice s (insert a₂ C) c *
              expectedRank ra s ((insert a₂ C).erase c) a₂ := by
          apply Finset.sum_le_sum; intro c hc
          apply mul_le_mul_of_nonneg_right
          · exact pChoice_cross_le (Finset.mem_insert_of_mem hc) (Finset.mem_insert_of_mem hc)
              hpos₁ hpos₂ hsum_le
          · have hc_ne₂ : c ≠ a₂ := fun h => ha₂ (h ▸ hc)
            have ha₂_mem_erase : a₂ ∈ (insert a₂ C).erase c :=
              Finset.mem_erase.mpr ⟨hc_ne₂.symm, Finset.mem_insert_self a₂ C⟩
            linarith [expectedRank_ge_one ra s ((insert a₂ C).erase c) a₂ ha₂_mem_erase
              (fun b hb => hpos₂ b (Finset.mem_of_mem_erase hb))]

/-- **Expected rank monotonicity**: higher score implies lower expected rank.

    If `v(a₁) > v(a₂)` then `E[rank(a₁)] < E[rank(a₂)]`: the alternative
    with higher ratio-scale value is expected to be ranked higher (closer to 1).

    This is a natural property of the Plackett–Luce model ([luce-1959],
    [plackett-1975]) but does not appear as a formal theorem in either
    source. [luce-1959] adopts the product decomposition as his ranking
    postulate and [marden-1995] covers estimation, but neither states the
    expected rank monotonicity result explicitly. -/
theorem expectedRank_lt_of_score_gt (ra : RationalAction S A) (s : S)
    (T : Finset A) (a₁ a₂ : A) (ha₁ : a₁ ∈ T) (ha₂ : a₂ ∈ T)
    (hne : a₁ ≠ a₂)
    (hpos : ∀ a ∈ T, 0 < ra.score s a)
    (hgt : ra.score s a₁ > ra.score s a₂) :
    expectedRank ra s T a₁ < expectedRank ra s T a₂ := by
  -- Induction on |T|
  suffices h : ∀ (n : ℕ) (T : Finset A), T.card = n → a₁ ∈ T → a₂ ∈ T →
      (∀ a ∈ T, 0 < ra.score s a) →
      expectedRank ra s T a₁ < expectedRank ra s T a₂ from
    h T.card T rfl ha₁ ha₂ hpos
  intro n; induction n with
  | zero => intro T hcard h₁; simp [Finset.card_eq_zero.mp hcard] at h₁
  | succ m ih =>
    intro T hcard ha₁' ha₂' hpos'
    -- Decompose both expected ranks
    rw [expectedRank_decomp ra s T a₁ ha₁' hpos',
        expectedRank_decomp ra s T a₂ ha₂' hpos']
    -- Split off the special terms: a₂ from T\{a₁}, a₁ from T\{a₂}
    have ha₂_e₁ : a₂ ∈ T.erase a₁ := Finset.mem_erase.mpr ⟨hne.symm, ha₂'⟩
    have ha₁_e₂ : a₁ ∈ T.erase a₂ := Finset.mem_erase.mpr ⟨hne, ha₁'⟩
    rw [← Finset.add_sum_erase _ _ ha₂_e₁, ← Finset.add_sum_erase _ _ ha₁_e₂]
    -- Unify the common field: (T\{a₁})\{a₂} = (T\{a₂})\{a₁}
    rw [show (T.erase a₂).erase a₁ = (T.erase a₁).erase a₂ from Finset.erase_right_comm]
    -- Goal: 1 + (p₂*E₁' + Σ₁) < 1 + (p₁*E₂' + Σ₂) where both sums are over R
    -- Fact 1: common terms satisfy Σ₁ ≤ Σ₂ (by IH giving < hence ≤)
    have h_sums : ∀ c ∈ (T.erase a₁).erase a₂,
        ra.pChoice s T c * expectedRank ra s (T.erase c) a₁ ≤
        ra.pChoice s T c * expectedRank ra s (T.erase c) a₂ := by
      intro c hc
      apply mul_le_mul_of_nonneg_left _ (ra.pChoice_nonneg s T c)
      have hc_mem : c ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
      have ha₁_ec : a₁ ∈ T.erase c :=
        Finset.mem_erase.mpr
          ⟨((Finset.mem_erase.mp (Finset.mem_of_mem_erase hc)).1).symm, ha₁'⟩
      have ha₂_ec : a₂ ∈ T.erase c :=
        Finset.mem_erase.mpr ⟨((Finset.mem_erase.mp hc).1).symm, ha₂'⟩
      have hcard_ec : (T.erase c).card = m := by
        rw [Finset.card_erase_of_mem hc_mem, hcard]; omega
      exact le_of_lt (ih (T.erase c) hcard_ec ha₁_ec ha₂_ec (score_pos_erase hpos' c))
    -- Fact 2: cross term satisfies p₂*E₁' < p₁*E₂'
    have h_cross : ra.pChoice s T a₂ * expectedRank ra s (T.erase a₂) a₁ <
        ra.pChoice s T a₁ * expectedRank ra s (T.erase a₁) a₂ := by
      have hp_gt := RationalAction.pChoice_lt_of_score_lt ha₁' ha₂' hpos' hgt
      have hE₁'_ge :=
        expectedRank_ge_one ra s (T.erase a₂) a₁ ha₁_e₂ (score_pos_erase hpos' a₂)
      -- Cross-set comparison: E₁' ≤ E₂'
      have hE_cross : expectedRank ra s (T.erase a₂) a₁ ≤
          expectedRank ra s (T.erase a₁) a₂ := by
        conv_lhs => rw [show T.erase a₂ = insert a₁ ((T.erase a₁).erase a₂) from by
          rw [← Finset.erase_right_comm]; exact (Finset.insert_erase ha₁_e₂).symm]
        conv_rhs => rw [show T.erase a₁ = insert a₂ ((T.erase a₁).erase a₂) from
          (Finset.insert_erase ha₂_e₁).symm]
        exact expectedRank_cross_le_aux ra s _ _ a₁ a₂ rfl
          (mt Finset.mem_of_mem_erase (Finset.notMem_erase a₁ T))
          (Finset.notMem_erase a₂ _)
          (fun b hb => hpos' b (by
            rcases Finset.mem_insert.mp hb with rfl | hb'
            · assumption
            · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb')))
          (fun b hb => hpos' b (by
            rcases Finset.mem_insert.mp hb with rfl | hb'
            · assumption
            · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb')))
          (le_of_lt hgt)
      -- p₁*E₂' ≥ p₁*E₁' > p₂*E₁'
      calc ra.pChoice s T a₂ * expectedRank ra s (T.erase a₂) a₁
          < ra.pChoice s T a₁ * expectedRank ra s (T.erase a₂) a₁ :=
            mul_lt_mul_of_pos_right hp_gt (by linarith)
        _ ≤ ra.pChoice s T a₁ * expectedRank ra s (T.erase a₁) a₂ :=
            mul_le_mul_of_nonneg_left hE_cross
              (le_of_lt (RationalAction.pChoice_pos ha₁' hpos'))
    -- Combine: 1 + p₂*E₁' + Σ₁ < 1 + p₁*E₂' + Σ₂
    linarith [Finset.sum_le_sum h_sums]

/-- **Equal scores imply equal expected ranks**: if `score(a₁) = score(a₂)`,
    then `E[rank(a₁, T)] = E[rank(a₂, T)]`.

    The proof uses the conditional expectation decomposition and antisymmetry:
    decompose both expected ranks by first element, show the common terms are
    equal by induction, and show the cross terms are equal by applying
    `expectedRank_cross_le_aux` in both directions (since `v(a₁) ≥ v(a₂)` and
    `v(a₂) ≥ v(a₁)` both hold). -/
theorem expectedRank_eq_of_score_eq (ra : RationalAction S A) (s : S)
    (T : Finset A) (a₁ a₂ : A) (ha₁ : a₁ ∈ T) (ha₂ : a₂ ∈ T)
    (hne : a₁ ≠ a₂)
    (hpos : ∀ a ∈ T, 0 < ra.score s a)
    (heq : ra.score s a₁ = ra.score s a₂) :
    expectedRank ra s T a₁ = expectedRank ra s T a₂ := by
  suffices h : ∀ (n : ℕ) (T : Finset A), T.card = n → a₁ ∈ T → a₂ ∈ T →
      (∀ a ∈ T, 0 < ra.score s a) →
      expectedRank ra s T a₁ = expectedRank ra s T a₂ from
    h T.card T rfl ha₁ ha₂ hpos
  intro n; induction n with
  | zero => intro T hcard h₁; simp [Finset.card_eq_zero.mp hcard] at h₁
  | succ m ih =>
    intro T hcard ha₁' ha₂' hpos'
    -- Decompose both expected ranks
    rw [expectedRank_decomp ra s T a₁ ha₁' hpos',
        expectedRank_decomp ra s T a₂ ha₂' hpos']
    -- Split sums to isolate cross terms
    have ha₂_e₁ : a₂ ∈ T.erase a₁ := Finset.mem_erase.mpr ⟨hne.symm, ha₂'⟩
    have ha₁_e₂ : a₁ ∈ T.erase a₂ := Finset.mem_erase.mpr ⟨hne, ha₁'⟩
    rw [← Finset.add_sum_erase _ _ ha₂_e₁, ← Finset.add_sum_erase _ _ ha₁_e₂]
    rw [show (T.erase a₂).erase a₁ = (T.erase a₁).erase a₂ from Finset.erase_right_comm]
    -- Common terms equal by IH
    have h_common : ∀ b ∈ (T.erase a₁).erase a₂,
        ra.pChoice s T b * expectedRank ra s (T.erase b) a₁ =
        ra.pChoice s T b * expectedRank ra s (T.erase b) a₂ := by
      intro b hb
      congr 1
      have hb_mem : b ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)
      have hb_ne₁ : b ≠ a₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hb)).1
      have hb_ne₂ : b ≠ a₂ := (Finset.mem_erase.mp hb).1
      exact ih (T.erase b)
        (by rw [Finset.card_erase_of_mem hb_mem, hcard]; omega)
        (Finset.mem_erase.mpr ⟨hb_ne₁.symm, ha₁'⟩)
        (Finset.mem_erase.mpr ⟨hb_ne₂.symm, ha₂'⟩)
        (score_pos_erase hpos' b)
    -- pChoice equality: pChoice(a₁,T) = pChoice(a₂,T) since scores are equal
    have hp_eq : ra.pChoice s T a₁ = ra.pChoice s T a₂ := by
      have hratio := ra.pChoice_ratio s T a₁ a₂ ha₁' ha₂'
      rw [heq] at hratio
      exact mul_right_cancel₀ (ne_of_gt (hpos' a₂ ha₂')) hratio
    -- Cross-set equality by antisymmetry
    have h_cross : expectedRank ra s (T.erase a₂) a₁ =
        expectedRank ra s (T.erase a₁) a₂ := by
      apply le_antisymm
      · conv_lhs => rw [show T.erase a₂ = insert a₁ ((T.erase a₁).erase a₂) from by
          rw [← Finset.erase_right_comm]; exact (Finset.insert_erase ha₁_e₂).symm]
        conv_rhs => rw [show T.erase a₁ = insert a₂ ((T.erase a₁).erase a₂) from
          (Finset.insert_erase ha₂_e₁).symm]
        exact expectedRank_cross_le_aux ra s _ _ a₁ a₂ rfl
          (mt Finset.mem_of_mem_erase (Finset.notMem_erase a₁ T))
          (Finset.notMem_erase a₂ _)
          (fun b hb => hpos' b (by
            rcases Finset.mem_insert.mp hb with rfl | hb'
            · assumption
            · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb')))
          (fun b hb => hpos' b (by
            rcases Finset.mem_insert.mp hb with rfl | hb'
            · assumption
            · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb')))
          (le_of_eq heq.symm)
      · conv_lhs => rw [show T.erase a₁ = insert a₂ ((T.erase a₁).erase a₂) from
          (Finset.insert_erase ha₂_e₁).symm]
        conv_rhs => rw [show T.erase a₂ = insert a₁ ((T.erase a₁).erase a₂) from by
          rw [← Finset.erase_right_comm]; exact (Finset.insert_erase ha₁_e₂).symm]
        exact expectedRank_cross_le_aux ra s _ _ a₂ a₁ rfl
          (Finset.notMem_erase a₂ _)
          (mt Finset.mem_of_mem_erase (Finset.notMem_erase a₁ T))
          (fun b hb => hpos' b (by
            rcases Finset.mem_insert.mp hb with rfl | hb'
            · assumption
            · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb')))
          (fun b hb => hpos' b (by
            rcases Finset.mem_insert.mp hb with rfl | hb'
            · assumption
            · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb')))
          (le_of_eq heq)
    -- Combine: rewrite common sums, cross terms, and pChoice
    have h_sum_eq := Finset.sum_congr rfl h_common
    rw [h_sum_eq, hp_eq, h_cross]


end Ranking

section Utility

variable {A E : Type*} [DecidableEq A] [DecidableEq E]

/-- A gamble `aρb` (p. 78): outcome `win` if the chance event `event` occurs,
    else `lose`. -/
structure Gamble (A E : Type*) where
  /-- Outcome if the event occurs. -/
  win : A
  /-- The conditioning chance event. -/
  event : E
  /-- Outcome if the event does not occur. -/
  lose : A
  deriving DecidableEq

/-- Luce's total alternative set `S(A,E) = (A × E × A) ∪ A` (p. 78): gambles
    together with the pure alternatives. -/
abbrev Alternative (A E : Type*) := Gamble A E ⊕ A

/-- A decomposable preference structure `⟨A, E, P, Q⟩` (Definition 5, p. 78):
    choice over gambles and pure alternatives (`P`), choice over events by
    subjective likelihood (`Q`), coupled by **Axiom 2**:
    `P(aρb, aσb) = P(a,b)·Q(ρ,σ) + P(b,a)·Q(σ,ρ)`.

    Deviations from Luce: `P` and `Q` are total `ChoiceFn`s rather than
    families on ≤3-element subsets (Axiom 1 enters as the `axiom1P`/`axiom1Q`
    fields, in `ChoiceFn.HasChoiceAxiom`'s two-clause form), and
    Axiom 2 carries an `a ≠ b` guard — at `a = b` it is unsatisfiable for a
    total `P` (`axiom2_unguarded_false`), and Luce's own uses all have
    `P(a,b) ∉ {0, 1}` or `P(a,b) = 1` with `a`, `b` a genuine pair. -/
structure DecomposablePreference (A E : Type*) [DecidableEq A] [DecidableEq E] where
  /-- Choice over `S(A,E)`. -/
  P : ChoiceFn (Alternative A E)
  /-- Choice over events by subjective likelihood. -/
  Q : ChoiceFn E
  /-- **Axiom 2** (p. 78), in Luce's full mixture form. -/
  axiom2 : ∀ a b : A, a ≠ b → ∀ ρ σ : E,
    P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨a, σ, b⟩) =
      P.binary (.inr a) (.inr b) * Q.binary ρ σ +
      P.binary (.inr b) (.inr a) * Q.binary σ ρ
  /-- `P` satisfies Luce's Axiom 1, per Definition 5. -/
  axiom1P : P.HasChoiceAxiom
  /-- `Q` satisfies Luce's Axiom 1, per Definition 5. -/
  axiom1Q : Q.HasChoiceAxiom

/-- Without its `a ≠ b` guard, Axiom 2 is unsatisfiable for a total choice
    function: at `a = b` it forces `P(aρa, aσa) = Q(ρ,σ) + Q(σ,ρ) = 1` in both
    argument orders, contradicting binary complementarity. In Luce's system
    `P(a, a)` is the degenerate singleton choice. -/
theorem axiom2_unguarded_false [Nontrivial E] [Inhabited A]
    (P : ChoiceFn (Alternative A E)) (Q : ChoiceFn E)
    (h : ∀ (a b : A) (ρ σ : E),
      P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨a, σ, b⟩) =
        P.binary (.inr a) (.inr b) * Q.binary ρ σ +
        P.binary (.inr b) (.inr a) * Q.binary σ ρ) : False := by
  obtain ⟨ρ, σ, hρσ⟩ := exists_pair_ne E
  set a := (default : A)
  have hself := P.binary_self (Sum.inr a)
  have hQc := Q.binary_complement hρσ
  have hne : (Sum.inl ⟨a, ρ, a⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, a⟩ := by
    simpa using hρσ
  have hPc := P.binary_complement hne
  have h1 := h a a ρ σ
  have h2 := h a a σ ρ
  rw [hself] at h1 h2
  linarith

namespace DecomposablePreference

variable (dp : DecomposablePreference A E)

/-- Luce's `P(a, b)` for pure alternatives. -/
def alt (a b : A) : ℝ := dp.P.binary (.inr a) (.inr b)

/-- Luce's `P(g, h)` for gambles. -/
def gam (g h : Gamble A E) : ℝ := dp.P.binary (.inl g) (.inl h)

variable {dp}

/-- The reduced decomposition under perfect discrimination, as used inside the
    proofs of Theorems 13–14 (p. 87): if `P(a,b) = 1` then
    `P(aρb, aσb) = Q(ρ, σ)`. -/
theorem gam_of_alt_eq_one {a b : A} (hab : a ≠ b) (h1 : dp.alt a b = 1)
    (ρ σ : E) : dp.gam ⟨a, ρ, b⟩ ⟨a, σ, b⟩ = dp.Q.binary ρ σ := by
  have hc := dp.P.binary_complement
    (show (Sum.inr a : Alternative A E) ≠ Sum.inr b by simpa using hab)
  simp only [alt] at h1
  have hba : dp.P.binary (Sum.inr b) (Sum.inr a) = 0 := by linarith
  simp only [gam]
  rw [dp.axiom2 a b hab ρ σ, h1, hba]
  ring

/-! ### Definition 6: the subjective likelihood order -/

/-- Definition 6 (p. 79): `ρ ≿ σ` iff `Q(ρ, σ) ≥ ½` — `ρ` is deemed at least
    as likely as `σ`. -/
def EventPref (dp : DecomposablePreference A E) (ρ σ : E) : Prop :=
  1 / 2 ≤ dp.Q.binary ρ σ

/-- Subjective equi-likelihood `ρ ∼ σ`: the symmetric part of Definition 6's
    `≿`. On distinct events this is `Q(ρ, σ) = ½` (`eventIndiff_iff_eq_half`);
    on the diagonal it holds since `Q(ρ, ρ) = 1`. -/
def EventIndiff (dp : DecomposablePreference A E) (ρ σ : E) : Prop :=
  EventPref dp ρ σ ∧ EventPref dp σ ρ

theorem eventIndiff_refl (dp : DecomposablePreference A E) (ρ : E) :
    EventIndiff dp ρ ρ := by
  unfold EventIndiff EventPref
  rw [dp.Q.binary_self]
  norm_num

theorem EventIndiff.symm {ρ σ : E} (h : EventIndiff dp ρ σ) :
    EventIndiff dp σ ρ := ⟨h.2, h.1⟩

theorem eventIndiff_iff_eq_half {ρ σ : E} (hne : ρ ≠ σ) :
    EventIndiff dp ρ σ ↔ dp.Q.binary ρ σ = 1 / 2 := by
  have hc := dp.Q.binary_complement hne
  unfold EventIndiff EventPref
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; exact ⟨by linarith, by linarith⟩

theorem ne_of_not_eventIndiff {ρ σ : E} (h : ¬EventIndiff dp ρ σ) : ρ ≠ σ :=
  fun he => h (he ▸ eventIndiff_refl dp ρ)

/-- Totality of `≿` in strict form: a non-equi-likely pair is strictly
    ordered one way or the other. -/
theorem gt_half_or_of_not_eventIndiff {ρ σ : E} (h : ¬EventIndiff dp ρ σ) :
    1 / 2 < dp.Q.binary ρ σ ∨ 1 / 2 < dp.Q.binary σ ρ := by
  have hne := ne_of_not_eventIndiff h
  have hc := dp.Q.binary_complement hne
  by_contra hcon
  push Not at hcon
  exact h ⟨show 1 / 2 ≤ _ by linarith [hcon.1, hcon.2],
    show 1 / 2 ≤ _ by linarith [hcon.1, hcon.2]⟩

/-- The nondegeneracy hypothesis of **Theorem 10** (p. 80): some genuine pair
    of alternatives is discriminated imperfectly and asymmetrically,
    `P(a, b) ∉ {0, ½, 1}`. -/
def Nondegenerate (dp : DecomposablePreference A E) : Prop :=
  ∃ a b : A, a ≠ b ∧ dp.alt a b ≠ 0 ∧ dp.alt a b ≠ 1 / 2 ∧ dp.alt a b ≠ 1

private lemma alt_pos_pos {a b : A} (hab : a ≠ b) (h0 : dp.alt a b ≠ 0)
    (h1 : dp.alt a b ≠ 1) :
    0 < dp.alt a b ∧ 0 < dp.alt b a ∧ dp.alt a b + dp.alt b a = 1 := by
  have hc : dp.alt a b + dp.alt b a = 1 := dp.P.binary_complement
    (show (Sum.inr a : Alternative A E) ≠ Sum.inr b by simpa using hab)
  have hp0 : 0 ≤ dp.alt a b := dp.P.binary_nonneg _ _
  have hq0 : 0 ≤ dp.alt b a := dp.P.binary_nonneg _ _
  refine ⟨lt_of_le_of_ne hp0 (Ne.symm h0), ?_, hc⟩
  rcases eq_or_lt_of_le hq0 with heq | hlt
  · exact absurd (by linarith : dp.alt a b = 1) h1
  · exact hlt

private lemma mix_pos {p p' q : ℝ} (hp : 0 < p) (hp' : 0 < p')
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 < p' + (p - p') * q := by
  rcases eq_or_lt_of_le hq1 with rfl | hq
  · linarith
  · nlinarith [mul_pos hp' (show (0:ℝ) < 1 - q by linarith),
      mul_nonneg hp.le hq0]

private lemma mix_lt_one {p p' q : ℝ} (hp : 0 < p) (hp' : 0 < p')
    (hpp' : p + p' = 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    p' + (p - p') * q < 1 := by
  have h := mix_pos hp' hp hq0 hq1
  nlinarith [h]

/-- Axiom 2 in mixture-collapsed form: for a genuine outcome pair the gamble
    comparison is the `Q`-mixture `P(b,a) + [P(a,b) − P(b,a)]·Q(x, y)`. -/
private lemma gam_mix {a b : A} (hab : a ≠ b) {x y : E} (hxy : x ≠ y) :
    dp.gam ⟨a, x, b⟩ ⟨a, y, b⟩ =
      dp.alt b a + (dp.alt a b - dp.alt b a) * dp.Q.binary x y := by
  have hq := dp.Q.binary_complement hxy
  simp only [gam, alt]
  rw [dp.axiom2 a b hab x y,
      show dp.Q.binary y x = 1 - dp.Q.binary x y by linarith]
  ring

/-! ### The three-class theorems (§3.B.2) -/

/-- **Lemma 5** (p. 80), in denominator-cleared form: Luce's identity
    `(K+1){2[Q(ρ,σ)+Q(σ,τ)+Q(τ,ρ)] − 3} + K²[Q(ρ,σ)Q(σ,τ)Q(τ,ρ) −
    Q(ρ,τ)Q(τ,σ)Q(σ,ρ)] = 0`, `K = P(a,b)/P(b,a) − 1`, multiplied through by
    `P(b,a)²`. From Axiom 2 and Theorem 2 for the gamble triple
    `{aρb, aσb, aτb}`, whose pairwise discrimination is imperfect whenever
    `P(a,b) ∉ {0, 1}`. -/
theorem lemma5 {a b : A} (hab : a ≠ b)
    (h0 : dp.alt a b ≠ 0) (hhalf : dp.alt a b ≠ 1 / 2) (h1 : dp.alt a b ≠ 1)
    {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ) (hρτ : ρ ≠ τ) :
    dp.alt a b * dp.alt b a *
        (2 * (dp.Q.binary ρ σ + dp.Q.binary σ τ + dp.Q.binary τ ρ) - 3) +
      (dp.alt a b - dp.alt b a) ^ 2 *
        (dp.Q.binary ρ σ * dp.Q.binary σ τ * dp.Q.binary τ ρ -
          dp.Q.binary ρ τ * dp.Q.binary τ σ * dp.Q.binary σ ρ) = 0 := by
  obtain ⟨hpa, hpb, hsum⟩ := alt_pos_pos hab h0 h1
  have g12 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  have g23 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, τ, b⟩ := by
    simpa using hστ
  have g13 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, τ, b⟩ := by
    simpa using hρτ
  have hbnds : ∀ x y : E, x ≠ y →
      0 < dp.P.binary (.inl ⟨a, x, b⟩) (.inl ⟨a, y, b⟩) ∧
        dp.P.binary (.inl ⟨a, x, b⟩) (.inl ⟨a, y, b⟩) < 1 := by
    intro x y hxy
    have hmix := gam_mix (dp := dp) hab hxy
    simp only [gam] at hmix
    rw [hmix]
    exact ⟨mix_pos hpa hpb (dp.Q.binary_nonneg x y) (dp.Q.binary_le_one x y),
      mix_lt_one hpa hpb hsum (dp.Q.binary_nonneg x y) (dp.Q.binary_le_one x y)⟩
  have himp : dp.P.ImperfectOn
      {.inl ⟨a, ρ, b⟩, .inl ⟨a, σ, b⟩, .inl ⟨a, τ, b⟩} := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxy
      | exact hbnds _ _ hρσ
      | exact hbnds _ _ hρσ.symm
      | exact hbnds _ _ hστ
      | exact hbnds _ _ hστ.symm
      | exact hbnds _ _ hρτ
      | exact hbnds _ _ hρτ.symm
  have hcyc := dp.axiom1P.binary_mul_cycle g12 g23 g13 himp
  have e12 := gam_mix (dp := dp) hab hρσ
  have e23 := gam_mix (dp := dp) hab hστ
  have e31 := gam_mix (dp := dp) hab hρτ.symm
  have e13 := gam_mix (dp := dp) hab hρτ
  have e32 := gam_mix (dp := dp) hab hστ.symm
  have e21 := gam_mix (dp := dp) hab hρσ.symm
  simp only [gam] at e12 e23 e31 e13 e32 e21
  rw [e12, e23, e31, e13, e32, e21] at hcyc
  have f1 : dp.Q.binary σ ρ = 1 - dp.Q.binary ρ σ := by
    linarith [dp.Q.binary_complement hρσ]
  have f2 : dp.Q.binary τ σ = 1 - dp.Q.binary σ τ := by
    linarith [dp.Q.binary_complement hστ]
  have f3 : dp.Q.binary ρ τ = 1 - dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  rw [f1, f2, f3] at hcyc ⊢
  have hΔ : dp.alt a b - dp.alt b a ≠ 0 := by
    intro h
    exact hhalf (by linarith)
  refine mul_left_cancel₀ hΔ ?_
  rw [mul_zero]
  linear_combination hcyc

/-- **Lemma 6** (p. 80): `≿` is transitive (with `gt_half_or_of_not_eventIndiff`
    totality, a weak ordering of `E`). -/
theorem eventPref_trans (hnd : Nondegenerate dp)
    {ρ σ τ : E} (h1 : EventPref dp ρ σ) (h2 : EventPref dp σ τ) :
    EventPref dp ρ τ := by
  rcases eq_or_ne ρ σ with rfl | hρσ
  · exact h2
  rcases eq_or_ne σ τ with rfl | hστ
  · exact h1
  rcases eq_or_ne ρ τ with rfl | hρτ
  · show 1 / 2 ≤ _
    rw [dp.Q.binary_self]
    norm_num
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  unfold EventPref at h1 h2 ⊢
  by_contra hcon
  push Not at hcon
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  have hq3 : 1 / 2 < dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  have f1 : dp.Q.binary σ ρ = 1 - dp.Q.binary ρ σ := by
    linarith [dp.Q.binary_complement hρσ]
  have f2 : dp.Q.binary τ σ = 1 - dp.Q.binary σ τ := by
    linarith [dp.Q.binary_complement hστ]
  have f3 : dp.Q.binary ρ τ = 1 - dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  rw [f1, f2, f3] at h5
  set q1 := dp.Q.binary ρ σ with hq1_def
  set q2 := dp.Q.binary σ τ with hq2_def
  set q3 := dp.Q.binary τ ρ with hq3_def
  have hb1 := dp.Q.binary_le_one ρ σ
  have hb2 := dp.Q.binary_le_one σ τ
  have hb3 := dp.Q.binary_le_one τ ρ
  have s0 : (0:ℝ) ≤ (1 - q2) * (1 - q3) :=
    mul_nonneg (by linarith) (by linarith)
  have s1 : (1 - q1) * ((1 - q2) * (1 - q3)) ≤ q1 * ((1 - q2) * (1 - q3)) :=
    mul_le_mul_of_nonneg_right (by linarith) s0
  have s2 : q1 * ((1 - q2) * (1 - q3)) ≤ q1 * (q2 * (1 - q3)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0:ℝ) ≤ q1)
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have s3 : q1 * (q2 * (1 - q3)) ≤ q1 * (q2 * q3) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0:ℝ) ≤ q1)
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith [h5, mul_pos (mul_pos hpa hpb)
      (show (0:ℝ) < 2 * (q1 + q2 + q3) - 3 by linarith),
    mul_nonneg (sq_nonneg (dp.alt a b - dp.alt b a))
      (show (0:ℝ) ≤ q1 * q2 * q3 - (1 - q3) * (1 - q2) * (1 - q1) by
        nlinarith [s1, s2, s3])]

/-- `∼` is transitive: with `eventIndiff_refl` and `EventIndiff.symm`, an
    equivalence relation (the content of **Theorem 10**'s first clause). -/
theorem eventIndiff_trans (hnd : Nondegenerate dp)
    {ρ σ τ : E} (h1 : EventIndiff dp ρ σ) (h2 : EventIndiff dp σ τ) :
    EventIndiff dp ρ τ :=
  ⟨eventPref_trans hnd h1.1 h2.1, eventPref_trans hnd h2.2 h1.2⟩

private lemma cubic_of_sum_eq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (h : x / (x + y) + y / (y + z) + z / (z + x) = 3 / 2) :
    (x - y) * (y - z) * (x - z) = 0 := by
  have h1 : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have h2 : y + z ≠ 0 := ne_of_gt (add_pos hy hz)
  have h3 : z + x ≠ 0 := ne_of_gt (add_pos hz hx)
  field_simp at h
  linear_combination h

/-- **Lemma 7** (p. 81): three distinct events, pairwise imperfectly
    discriminated, cannot lie in three distinct `∼`-classes. -/
theorem lemma7 (hnd : Nondegenerate dp) {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ)
    (hρτ : ρ ≠ τ) (himp : dp.Q.ImperfectOn {ρ, σ, τ}) :
    EventIndiff dp ρ σ ∨ EventIndiff dp σ τ ∨ EventIndiff dp ρ τ := by
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  have hcyc := dp.axiom1Q.binary_mul_cycle hρσ hστ hρτ himp
  have hzero : dp.alt a b * dp.alt b a *
      (2 * (dp.Q.binary ρ σ + dp.Q.binary σ τ + dp.Q.binary τ ρ) - 3) = 0 := by
    linear_combination h5 - (dp.alt a b - dp.alt b a) ^ 2 * hcyc
  have hsum32 : dp.Q.binary ρ σ + dp.Q.binary σ τ + dp.Q.binary τ ρ = 3 / 2 := by
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact absurd h' (ne_of_gt (mul_pos hpa hpb))
    · linarith
  obtain ⟨v, hpos, hrule⟩ :=
    dp.axiom1Q.binaryRatioScaleOn ⟨ρ, Finset.mem_insert_self ρ _⟩ himp
  have mρ : ρ ∈ (↑({ρ, σ, τ} : Finset E) : Set E) := by simp
  have mσ : σ ∈ (↑({ρ, σ, τ} : Finset E) : Set E) := by simp
  have mτ : τ ∈ (↑({ρ, σ, τ} : Finset E) : Set E) := by simp
  have pρ := hpos ρ mρ
  have pσ := hpos σ mσ
  have pτ := hpos τ mτ
  rw [hrule ρ mρ σ mσ hρσ, hrule σ mσ τ mτ hστ,
      hrule τ mτ ρ mρ (Ne.symm hρτ)] at hsum32
  simp only [pairwiseProb] at hsum32
  have key := cubic_of_sum_eq pρ pσ pτ hsum32
  rcases mul_eq_zero.mp key with h' | hρτ'
  · rcases mul_eq_zero.mp h' with hρσ' | hστ'
    · refine Or.inl ((eventIndiff_iff_eq_half hρσ).mpr ?_)
      rw [hrule ρ mρ σ mσ hρσ]
      exact (pairwiseProb_eq_half_iff pρ pσ).mpr (by linarith)
    · refine Or.inr (Or.inl ((eventIndiff_iff_eq_half hστ).mpr ?_))
      rw [hrule σ mσ τ mτ hστ]
      exact (pairwiseProb_eq_half_iff pσ pτ).mpr (by linarith)
  · refine Or.inr (Or.inr ((eventIndiff_iff_eq_half hρτ).mpr ?_))
    rw [hrule ρ mρ τ mτ hρτ]
    exact (pairwiseProb_eq_half_iff pρ pτ).mpr (by linarith)

private lemma boost (hnd : Nondegenerate dp)
    {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ) (hρτ : ρ ≠ τ)
    (h1 : dp.Q.binary ρ σ = 1) (h2 : 1 / 2 < dp.Q.binary σ τ) :
    dp.Q.binary ρ τ = 1 := by
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  by_contra hne
  have hlt : dp.Q.binary ρ τ < 1 :=
    lt_of_le_of_ne (dp.Q.binary_le_one ρ τ) hne
  have hq3 : 0 < dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  have hσρ : dp.Q.binary σ ρ = 0 := by
    linarith [dp.Q.binary_complement hρσ]
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  rw [h1, hσρ] at h5
  nlinarith [h5, mul_pos (mul_pos hpa hpb)
      (show (0:ℝ) < 2 * (1 + dp.Q.binary σ τ + dp.Q.binary τ ρ) - 3 by linarith),
    mul_nonneg (sq_nonneg (dp.alt a b - dp.alt b a))
      (mul_nonneg (mul_nonneg one_pos.le (dp.Q.binary_nonneg σ τ))
        (dp.Q.binary_nonneg τ ρ))]

private lemma boost' (hnd : Nondegenerate dp)
    {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ) (hρτ : ρ ≠ τ)
    (h1 : 1 / 2 < dp.Q.binary ρ σ) (h2 : dp.Q.binary σ τ = 1) :
    dp.Q.binary ρ τ = 1 := by
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  by_contra hne
  have hlt : dp.Q.binary ρ τ < 1 :=
    lt_of_le_of_ne (dp.Q.binary_le_one ρ τ) hne
  have hq3 : 0 < dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  have hτσ : dp.Q.binary τ σ = 0 := by
    linarith [dp.Q.binary_complement hστ]
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  rw [h2, hτσ] at h5
  nlinarith [h5, mul_pos (mul_pos hpa hpb)
      (show (0:ℝ) < 2 * (dp.Q.binary ρ σ + 1 + dp.Q.binary τ ρ) - 3 by linarith),
    mul_nonneg (sq_nonneg (dp.alt a b - dp.alt b a))
      (mul_nonneg (mul_nonneg (dp.Q.binary_nonneg ρ σ) one_pos.le)
        (dp.Q.binary_nonneg τ ρ))]

private lemma no_strict_cycle (hnd : Nondegenerate dp) {ρ σ τ : E} (hρτ : ρ ≠ τ)
    (h1 : 1 / 2 < dp.Q.binary ρ σ) (h2 : 1 / 2 < dp.Q.binary σ τ)
    (h3 : 1 / 2 < dp.Q.binary τ ρ) : False := by
  have hle : EventPref dp ρ τ :=
    eventPref_trans hnd (show EventPref dp ρ σ from h1.le)
      (show EventPref dp σ τ from h2.le)
  have hc := dp.Q.binary_complement hρτ
  unfold EventPref at hle
  linarith

private lemma no_four_chain (hnd : Nondegenerate dp) {ρ σ τ ω : E}
    (nρσ : ¬EventIndiff dp ρ σ) (nρτ : ¬EventIndiff dp ρ τ)
    (nρω : ¬EventIndiff dp ρ ω) (nστ : ¬EventIndiff dp σ τ)
    (nτω : ¬EventIndiff dp τ ω)
    (h1 : 1 / 2 < dp.Q.binary ρ σ) (h2 : 1 / 2 < dp.Q.binary σ τ)
    (h3 : 1 / 2 < dp.Q.binary τ ω) : False := by
  have dρσ := ne_of_not_eventIndiff nρσ
  have dρτ := ne_of_not_eventIndiff nρτ
  have dρω := ne_of_not_eventIndiff nρω
  have dστ := ne_of_not_eventIndiff nστ
  have dτω := ne_of_not_eventIndiff nτω
  have hρτ : 1 / 2 < dp.Q.binary ρ τ := by
    have hle := eventPref_trans hnd (show EventPref dp ρ σ from h1.le)
      (show EventPref dp σ τ from h2.le)
    unfold EventPref at hle
    refine lt_of_le_of_ne hle (Ne.symm (fun he => nρτ ?_))
    exact (eventIndiff_iff_eq_half dρτ).mpr he
  have hQρτ : dp.Q.binary ρ τ = 1 := by
    by_cases hA : dp.Q.binary ρ σ = 1
    · exact boost hnd dρσ dστ dρτ hA h2
    by_cases hB : dp.Q.binary σ τ = 1
    · exact boost' hnd dρσ dστ dρτ h1 hB
    by_cases hC : dp.Q.binary ρ τ = 1
    · exact hC
    have core : ∀ u w : E, u ≠ w → 1 / 2 < dp.Q.binary u w →
        dp.Q.binary u w ≠ 1 →
        (0 < dp.Q.binary u w ∧ dp.Q.binary u w < 1) ∧
          0 < dp.Q.binary w u ∧ dp.Q.binary w u < 1 := by
      intro u w huw hgt hne1
      have hc := dp.Q.binary_complement huw
      have hlt := lt_of_le_of_ne (dp.Q.binary_le_one u w) hne1
      exact ⟨⟨by linarith, hlt⟩, by constructor <;> linarith⟩
    have himp : dp.Q.ImperfectOn {ρ, σ, τ} := by
      intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact absurd rfl hxy
      · exact (core _ _ dρσ h1 hA).1
      · exact (core _ _ dρτ hρτ hC).1
      · exact (core _ _ dρσ h1 hA).2
      · exact absurd rfl hxy
      · exact (core _ _ dστ h2 hB).1
      · exact (core _ _ dρτ hρτ hC).2
      · exact (core _ _ dστ h2 hB).2
      · exact absurd rfl hxy
    rcases lemma7 hnd dρσ dστ dρτ himp with h | h | h
    · exact absurd h nρσ
    · exact absurd h nστ
    · exact absurd h nρτ
  have hQρω : dp.Q.binary ρ ω = 1 := boost hnd dρτ dτω dρω hQρτ h3
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  have h5 := lemma5 hab h0 hhalf hone dρτ dτω dρω
  have hτρ : dp.Q.binary τ ρ = 0 := by
    linarith [dp.Q.binary_complement dρτ]
  have hωρ : dp.Q.binary ω ρ = 0 := by
    linarith [dp.Q.binary_complement dρω]
  rw [hQρτ, hτρ, hωρ] at h5
  have h5' : dp.alt a b * dp.alt b a * (2 * dp.Q.binary τ ω - 1) = 0 := by
    linear_combination h5
  have : dp.Q.binary τ ω = 1 / 2 := by
    rcases mul_eq_zero.mp h5' with h' | h'
    · exact absurd h' (ne_of_gt (mul_pos hpa hpb))
    · linarith
  exact nτω ((eventIndiff_iff_eq_half dτω).mpr this)

private lemma no_chain_insert (hnd : Nondegenerate dp) {a b c ω : E}
    (nab : ¬EventIndiff dp a b) (nac : ¬EventIndiff dp a c)
    (naω : ¬EventIndiff dp a ω) (nbc : ¬EventIndiff dp b c)
    (nbω : ¬EventIndiff dp b ω) (ncω : ¬EventIndiff dp c ω)
    (sab : 1 / 2 < dp.Q.binary a b) (sbc : 1 / 2 < dp.Q.binary b c) :
    False := by
  have N : ∀ {x y : E}, ¬EventIndiff dp x y → ¬EventIndiff dp y x :=
    fun n h => n h.symm
  rcases gt_half_or_of_not_eventIndiff naω with haω | hωa
  · rcases gt_half_or_of_not_eventIndiff nbω with hbω | hωb
    · rcases gt_half_or_of_not_eventIndiff ncω with hcω | hωc
      · exact no_four_chain hnd nab nac naω nbc ncω sab sbc hcω
      · exact no_four_chain hnd nab naω nac nbω (N ncω) sab hbω hωc
    · exact no_four_chain hnd naω nab nac (N nbω) nbc haω hωb sbc
  · exact no_four_chain hnd (N naω) (N nbω) (N ncω) nab nbc hωa sab sbc

/-- **Lemma 8** (p. 81) / the partition clause of **Theorem 10** (p. 80): in
    a nondegenerate decomposable preference structure, `∼` partitions the
    events into at most three classes — among any four events, two are
    subjectively equi-likely. -/
theorem atMostThreeClasses (hnd : Nondegenerate dp) (ρ σ τ ω : E) :
    EventIndiff dp ρ σ ∨ EventIndiff dp ρ τ ∨ EventIndiff dp ρ ω ∨
      EventIndiff dp σ τ ∨ EventIndiff dp σ ω ∨ EventIndiff dp τ ω := by
  by_contra hcon
  push Not at hcon
  obtain ⟨nρσ, nρτ, nρω, nστ, nσω, nτω⟩ := hcon
  have N : ∀ {x y : E}, ¬EventIndiff dp x y → ¬EventIndiff dp y x :=
    fun n h => n h.symm
  rcases gt_half_or_of_not_eventIndiff nρσ with h1 | h1'
  · rcases gt_half_or_of_not_eventIndiff nστ with h2 | h2'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_chain_insert hnd nρσ nρτ nρω nστ nσω nτω h1 h2
      · exact no_strict_cycle hnd (ne_of_not_eventIndiff nρτ) h1 h2 h3'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_chain_insert hnd nρτ nρσ nρω (N nστ) nτω nσω h3 h2'
      · exact no_chain_insert hnd (N nρτ) (N nστ) nτω nρσ nρω nσω h3' h1
  · rcases gt_half_or_of_not_eventIndiff nστ with h2 | h2'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_chain_insert hnd (N nρσ) nστ nσω nρτ nρω nτω h1' h3
      · exact no_chain_insert hnd nστ (N nρσ) nσω (N nρτ) nτω nρω h2 h3'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_strict_cycle hnd (ne_of_not_eventIndiff nστ) h1' h3 h2'
      · exact no_chain_insert hnd (N nστ) (N nρτ) nτω (N nρσ) nσω nρω h2' h1'

private lemma q_congr_left (hnd : Nondegenerate dp) {ρ ρ' σ : E}
    (h : EventIndiff dp ρ ρ') (hρσ : ρ ≠ σ) (hρ'σ : ρ' ≠ σ) :
    dp.Q.binary ρ' σ = dp.Q.binary ρ σ := by
  rcases eq_or_ne ρ ρ' with rfl | hρρ'
  · rfl
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  have hhalf1 : dp.Q.binary ρ ρ' = 1 / 2 := (eventIndiff_iff_eq_half hρρ').mp h
  have hhalf2 : dp.Q.binary ρ' ρ = 1 / 2 := by
    linarith [dp.Q.binary_complement hρρ']
  have h5 := lemma5 hab h0 hhalf hone hρρ' hρ'σ hρσ
  have f1 : dp.Q.binary σ ρ = 1 - dp.Q.binary ρ σ := by
    linarith [dp.Q.binary_complement hρσ]
  have f2 : dp.Q.binary σ ρ' = 1 - dp.Q.binary ρ' σ := by
    linarith [dp.Q.binary_complement hρ'σ]
  rw [hhalf1, hhalf2, f1, f2] at h5
  have key : (2 * (dp.alt a b * dp.alt b a) +
      (dp.alt a b - dp.alt b a) ^ 2 / 2) *
      (dp.Q.binary ρ' σ - dp.Q.binary ρ σ) = 0 := by
    linear_combination h5
  rcases mul_eq_zero.mp key with h' | h'
  · nlinarith [mul_pos hpa hpb, sq_nonneg (dp.alt a b - dp.alt b a)]
  · linarith

/-- **Theorem 11** (p. 82): `Q` is constant across `∼`-classes — if `ρ ∼ ρ'`
    and `σ ∼ σ'` then `Q(ρ, σ) = Q(ρ', σ')`. Both comparisons must be genuine
    pairs: at `ρ' = σ'` the total-`ChoiceFn` diagonal `Q(ρ', ρ') = 1` breaks
    the unguarded claim, which Luce's `P(x, x) = ½` convention (p. 5) hides. -/
theorem theorem11 (hnd : Nondegenerate dp) {ρ ρ' σ σ' : E}
    (h1 : EventIndiff dp ρ ρ') (h2 : EventIndiff dp σ σ')
    (hρσ : ρ ≠ σ) (hρ'σ' : ρ' ≠ σ') :
    dp.Q.binary ρ σ = dp.Q.binary ρ' σ' := by
  rcases eq_or_ne ρ' σ with rfl | hρ'σ
  · have e1 := (eventIndiff_iff_eq_half hρσ).mp h1
    have e2 := (eventIndiff_iff_eq_half hρ'σ').mp h2
    rw [e1, e2]
  · have s1 : dp.Q.binary ρ' σ = dp.Q.binary ρ σ := q_congr_left hnd h1 hρσ hρ'σ
    have s2 : dp.Q.binary σ' ρ' = dp.Q.binary σ ρ' :=
      q_congr_left hnd h2 (Ne.symm hρ'σ) (Ne.symm hρ'σ')
    have c1 := dp.Q.binary_complement hρ'σ
    have c2 := dp.Q.binary_complement hρ'σ'
    linarith [s1, s2, c1, c2]

/-- **Theorem 13** (p. 86): if `P(a,b) = P(c,d) = 1` and "all pairwise
    discriminations in the set `T = {aρb, aσb, cρd, cσd}` are imperfect",
    then `P(aρb, cρd) = P(aσb, cσd)` — the step-function prediction of §3.D.
    The local ratio scale of Luce's proof is supplied by Theorem 3
    (`ChoiceFn.HasChoiceAxiom.binaryRatioScaleOn`). -/
theorem theorem13 {a b c d : A} {ρ σ : E}
    (hab : a ≠ b) (hcd : c ≠ d) (ha1 : dp.alt a b = 1) (hc1 : dp.alt c d = 1)
    (himp : dp.P.ImperfectOn
      {.inl ⟨a, ρ, b⟩, .inl ⟨a, σ, b⟩, .inl ⟨c, ρ, d⟩, .inl ⟨c, σ, d⟩}) :
    dp.gam ⟨a, ρ, b⟩ ⟨c, ρ, d⟩ = dp.gam ⟨a, σ, b⟩ ⟨c, σ, d⟩ := by
  by_cases hρσ : ρ = σ
  · subst hρσ; rfl
  by_cases hacbd : a = c ∧ b = d
  · obtain ⟨rfl, rfl⟩ := hacbd
    simp only [gam]
    rw [dp.P.binary_self, dp.P.binary_self]
  have e1 : dp.gam ⟨a, ρ, b⟩ ⟨a, σ, b⟩ = dp.gam ⟨c, ρ, d⟩ ⟨c, σ, d⟩ := by
    rw [gam_of_alt_eq_one hab ha1, gam_of_alt_eq_one hcd hc1]
  have h12 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  have h34 : (Sum.inl ⟨c, ρ, d⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
    simpa using hρσ
  have h13 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, ρ, d⟩ := by
    simpa using hacbd
  have h24 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
    simpa using hacbd
  obtain ⟨v, hpos, hrule⟩ := dp.axiom1P.binaryRatioScaleOn
    ⟨_, Finset.mem_insert_self _ _⟩ himp
  have p1 := hpos (Sum.inl ⟨a, ρ, b⟩) (by simp)
  have p2 := hpos (Sum.inl ⟨a, σ, b⟩) (by simp)
  have p3 := hpos (Sum.inl ⟨c, ρ, d⟩) (by simp)
  have p4 := hpos (Sum.inl ⟨c, σ, d⟩) (by simp)
  simp only [gam] at e1 ⊢
  rw [hrule _ (by simp) _ (by simp) h12, hrule _ (by simp) _ (by simp) h34] at e1
  rw [hrule _ (by simp) _ (by simp) h13, hrule _ (by simp) _ (by simp) h24,
      pairwiseProb_eq_pairwiseProb_iff p1 p3 p2 p4]
  exact ((pairwiseProb_eq_pairwiseProb_iff p1 p2 p3 p4).mp e1).trans (mul_comm _ _)

section BooleanEvents

variable [BooleanAlgebra E]

/-- **Axiom 3** (p. 83): "P(aρb, x) = P(bρ̄a, x), where ρ̄ denotes the
    complement of ρ" — `aρb` and `bρ̄a` are the same prospect relabeled.
    The two guards exclude `x ∈ {aρb, bρ̄a}`: for Luce those instances are
    degenerate singleton choices, and over a total `ChoiceFn` the unguarded
    axiom is unsatisfiable (`complementation_unguarded_false`). -/
def Complementation (dp : DecomposablePreference A E) : Prop :=
  ∀ (a b : A) (ρ : E) (x : Alternative A E),
    x ≠ .inl ⟨a, ρ, b⟩ → x ≠ .inl ⟨b, ρᶜ, a⟩ →
      dp.P.binary (.inl ⟨a, ρ, b⟩) x = dp.P.binary (.inl ⟨b, ρᶜ, a⟩) x

/-- Without its guards, Axiom 3 is unsatisfiable for a total choice function:
    `x := bρ̄a` forces `P(aρb, bρ̄a) = 1`, and symmetrically
    `P(bρ̄a, aρb) = 1`, contradicting binary complementarity. -/
theorem complementation_unguarded_false [Nontrivial A]
    (dp : DecomposablePreference A E)
    (h : ∀ (a b : A) (ρ : E) (x : Alternative A E),
      dp.P.binary (.inl ⟨a, ρ, b⟩) x = dp.P.binary (.inl ⟨b, ρᶜ, a⟩) x) :
    False := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  have h1 : dp.P.binary (.inl ⟨a, ⊥, b⟩) (.inl ⟨b, ⊥ᶜ, a⟩) = 1 := by
    rw [h a b ⊥ (.inl ⟨b, ⊥ᶜ, a⟩)]
    exact dp.P.binary_self _
  have h2 : dp.P.binary (.inl ⟨b, ⊥ᶜ, a⟩) (.inl ⟨a, ⊥, b⟩) = 1 := by
    have e := h b a ⊥ᶜ (.inl ⟨a, ⊥, b⟩)
    rw [compl_compl] at e
    rw [e]
    exact dp.P.binary_self _
  have hne : (Sum.inl ⟨a, ⊥, b⟩ : Alternative A E) ≠ Sum.inl ⟨b, ⊥ᶜ, a⟩ := by
    simp [hab]
  have := dp.P.binary_complement hne
  linarith

/-- **Axiom 4** (p. 83): some pair of alternatives and some pair of events are
    discriminated away from ½. Distinctness is explicit: Luce's `P(a*, b*)`
    presupposes a genuine pair (`P(a, a) = 1 ≠ ½` would satisfy the inequality
    degenerately and break the determinant step of Lemma 9). -/
def NontrivialPreference (dp : DecomposablePreference A E) : Prop :=
  (∃ a b : A, a ≠ b ∧ dp.alt a b ≠ 1 / 2) ∧
    ∃ ρ σ : E, ρ ≠ σ ∧ dp.Q.binary ρ σ ≠ 1 / 2

/-- **Lemma 9** (p. 84): under Axioms 3–4, `Q(ρ, σ) = Q(σ̄, ρ̄)`. -/
theorem q_compl_compl (ax3 : Complementation dp)
    (ax4 : NontrivialPreference dp) (ρ σ : E) :
    dp.Q.binary ρ σ = dp.Q.binary σᶜ ρᶜ := by
  rcases eq_or_ne ρ σ with rfl | hρσ
  · rw [dp.Q.binary_self, dp.Q.binary_self]
  obtain ⟨⟨a, b, hab, hp⟩, -⟩ := ax4
  have hXY : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  have hXY' : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨b, σᶜ, a⟩ := by
    simp [hab]
  have hY'X' : (Sum.inl ⟨b, σᶜ, a⟩ : Alternative A E) ≠ Sum.inl ⟨b, ρᶜ, a⟩ := by
    simpa using compl_injective.ne (Ne.symm hρσ)
  -- flip the second argument `aσb ↝ bσ̄a` (Axiom 3 at schema (a, b, σ))
  have flipY : dp.P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨a, σ, b⟩) =
      dp.P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨b, σᶜ, a⟩) := by
    have e := ax3 a b σ (.inl ⟨a, ρ, b⟩) hXY hXY'
    have c1 := dp.P.binary_complement hXY
    have c2 := dp.P.binary_complement hXY'
    linarith
  -- flip the first argument `aρb ↝ bρ̄a` (Axiom 3 at schema (a, b, ρ))
  have flipX : dp.P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨b, σᶜ, a⟩) =
      dp.P.binary (.inl ⟨b, ρᶜ, a⟩) (.inl ⟨b, σᶜ, a⟩) :=
    ax3 a b ρ (.inl ⟨b, σᶜ, a⟩) (Ne.symm hXY') hY'X'
  have key := flipY.trans flipX
  rw [dp.axiom2 a b hab ρ σ, dp.axiom2 b a (Ne.symm hab) ρᶜ σᶜ] at key
  have cAB := dp.P.binary_complement
    (show (Sum.inr a : Alternative A E) ≠ Sum.inr b by simpa using hab)
  have cQ := dp.Q.binary_complement hρσ
  have cQc := dp.Q.binary_complement (show ρᶜ ≠ σᶜ from compl_injective.ne hρσ)
  simp only [alt] at hp
  have hkey : (dp.Q.binary ρ σ - dp.Q.binary σᶜ ρᶜ) *
      (2 * dp.P.binary (Sum.inr a) (Sum.inr b) - 1) = 0 := by
    linear_combination key -
      dp.P.binary (Sum.inr b) (Sum.inr a) * cQ +
      dp.P.binary (Sum.inr b) (Sum.inr a) * cQc +
      (dp.Q.binary ρ σ - dp.Q.binary σᶜ ρᶜ) * cAB
  rcases mul_eq_zero.mp hkey with h0 | h0
  · linarith
  · exact absurd (by linarith : dp.P.binary (Sum.inr a) (Sum.inr b) = 1 / 2) hp

/-- Under a global binary ratio scale for `Q`, Lemma 9 pins `v(ρ)·v(ρ̄)` to a
    constant — the source of the `φ(ρ)φ(ρ̄) = constant` clause of the §3.D.3
    decomposition (p. 89). -/
theorem v_mul_v_compl_const {v : E → ℝ}
    (hv : dp.Q.BinaryRatioScaleOn Set.univ v) (ax3 : Complementation dp)
    (ax4 : NontrivialPreference dp) (ρ σ : E) :
    v ρ * v ρᶜ = v σ * v σᶜ := by
  obtain ⟨hpos, hrule⟩ := hv
  rcases eq_or_ne ρ σ with rfl | hρσ
  · rfl
  have h9 := q_compl_compl ax3 ax4 ρ σ
  rw [hrule ρ trivial σ trivial hρσ,
      hrule σᶜ trivial ρᶜ trivial (compl_injective.ne (Ne.symm hρσ))] at h9
  exact ((pairwiseProb_eq_pairwiseProb_iff (hpos ρ trivial) (hpos σ trivial)
    (hpos σᶜ trivial) (hpos ρᶜ trivial)).mp h9).trans (mul_comm _ _)

/-- An event indifferent to its own complement: membership in Luce's class
    `C(½)` (Lemma 11, p. 85). -/
def Neutral (dp : DecomposablePreference A E) (ρ : E) : Prop :=
  dp.Q.binary ρ ρᶜ = 1 / 2

/-- An event deemed more likely than its complement: Luce's class `C(1)`. -/
def Favorable (dp : DecomposablePreference A E) (ρ : E) : Prop :=
  1 / 2 < dp.Q.binary ρ ρᶜ

/-- An event deemed less likely than its complement: Luce's class `C(0)`. -/
def Unfavorable (dp : DecomposablePreference A E) (ρ : E) : Prop :=
  dp.Q.binary ρ ρᶜ < 1 / 2

/-- Every event is unfavorable, neutral, or favorable. -/
theorem unfavorable_or_neutral_or_favorable (dp : DecomposablePreference A E)
    (ρ : E) : Unfavorable dp ρ ∨ Neutral dp ρ ∨ Favorable dp ρ :=
  lt_trichotomy _ _

/-- An event is neutral iff its complement is. -/
theorem neutral_compl_iff [Nontrivial E] (ρ : E) :
    Neutral dp ρᶜ ↔ Neutral dp ρ := by
  have hc := dp.Q.binary_complement (show ρ ≠ ρᶜ from (compl_ne_self (a := ρ)).symm)
  unfold Neutral
  rw [compl_compl]
  constructor <;> intro h <;> linarith

/-- An event is favorable iff its complement is unfavorable. -/
theorem favorable_iff_unfavorable_compl [Nontrivial E] (ρ : E) :
    Favorable dp ρ ↔ Unfavorable dp ρᶜ := by
  have hc := dp.Q.binary_complement (show ρ ≠ ρᶜ from (compl_ne_self (a := ρ)).symm)
  unfold Favorable Unfavorable
  rw [compl_compl]
  constructor <;> intro h <;> linarith

/-- Two distinct neutral events are indifferent — the first clause of
    **Lemma 10** (p. 84), "if ρ ∼ ρ̄ and σ ∼ σ̄, then ρ ∼ σ", via Theorem 11
    and Lemma 9. Distinctness is required: `Q(ρ, ρ) = 1`. -/
theorem neutral_indifferent [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp) {ρ σ : E}
    (hρ : Neutral dp ρ) (hσ : Neutral dp σ) (hρσ : ρ ≠ σ) :
    dp.Q.binary ρ σ = 1 / 2 := by
  have iρ : EventIndiff dp ρ ρᶜ :=
    (eventIndiff_iff_eq_half (compl_ne_self (a := ρ)).symm).mpr hρ
  have iσ : EventIndiff dp σ σᶜ :=
    (eventIndiff_iff_eq_half (compl_ne_self (a := σ)).symm).mpr hσ
  have h11 := theorem11 hnd iρ iσ hρσ (compl_injective.ne hρσ)
  have h9 := q_compl_compl ax3 ax4 ρᶜ σᶜ
  rw [compl_compl, compl_compl] at h9
  have hc := dp.Q.binary_complement hρσ
  linarith [h11, h9, hc]

/-- Favorable events are preferred to unfavorable ones: the between-class
    ordering `C(1) > C(0)` of the three-class picture (§3.C.2, p. 85),
    under a global ratio scale for `Q`. -/
theorem favorable_gt_unfavorable [Nontrivial E] {v : E → ℝ}
    (hv : dp.Q.BinaryRatioScaleOn Set.univ v) (ax3 : Complementation dp)
    (ax4 : NontrivialPreference dp) {ρ σ : E} (hρ : Favorable dp ρ)
    (hσ : Unfavorable dp σ) : 1 / 2 < dp.Q.binary ρ σ := by
  have hρσ : ρ ≠ σ := by
    rintro rfl
    unfold Favorable at hρ
    unfold Unfavorable at hσ
    linarith
  obtain ⟨hpos, hrule⟩ := hv
  have p1 := hpos ρ trivial
  have p2 := hpos ρᶜ trivial
  have p3 := hpos σ trivial
  have p4 := hpos σᶜ trivial
  -- favorable: v ρ̄ < v ρ; unfavorable: v σ < v σ̄
  have h1 : v ρᶜ < v ρ := by
    have h := hρ
    unfold Favorable at h
    rw [hrule ρ trivial ρᶜ trivial ((compl_ne_self (a := ρ)).symm)] at h
    exact (pairwiseProb_gt_half_iff p1 p2).mp h
  have h2 : v σ < v σᶜ := by
    have h := hσ
    unfold Unfavorable at h
    rw [hrule σ trivial σᶜ trivial ((compl_ne_self (a := σ)).symm)] at h
    exact (pairwiseProb_lt_half_iff p3 p4).mp h
  have hconst := v_mul_v_compl_const ⟨hpos, hrule⟩ ax3 ax4 ρ σ
  -- v ρ² > v ρ · v ρ̄ = v σ · v σ̄ > v σ², hence v σ < v ρ
  have hvv : v σ < v ρ := by nlinarith
  rw [hrule ρ trivial σ trivial hρσ]
  exact (pairwiseProb_gt_half_iff p1 p3).mpr hvv

/-- **Theorem 14** (p. 89): with Axiom 3, `P(a,b) = P(d,c) = 1`, and a local
    ratio scale over the six gambles involved, the scale satisfies
    `v(aρb)·v(dρ̄c) = v(aσb)·v(dσ̄c)`. Together with Theorem 13 this is what
    "suggests that `v` may be of the form `v(aρb) = w(a,b)·φ(ρ)`" (§3.D.3). -/
theorem theorem14 [Nontrivial E] (ax3 : Complementation dp)
    {a b c d : A} {ρ σ : E} {v : Alternative A E → ℝ}
    (hab : a ≠ b) (hcd : c ≠ d) (hρσ : ρ ≠ σ) (hacbd : ¬(a = c ∧ b = d))
    (ha1 : dp.alt a b = 1) (hd1 : dp.alt d c = 1)
    (hv : dp.P.BinaryRatioScaleOn
      {.inl ⟨a, ρ, b⟩, .inl ⟨a, σ, b⟩, .inl ⟨c, ρ, d⟩, .inl ⟨c, σ, d⟩,
        .inl ⟨d, ρᶜ, c⟩, .inl ⟨d, σᶜ, c⟩} v) :
    v (.inl ⟨a, ρ, b⟩) * v (.inl ⟨d, ρᶜ, c⟩) =
      v (.inl ⟨a, σ, b⟩) * v (.inl ⟨d, σᶜ, c⟩) := by
  obtain ⟨hpos, hrule⟩ := hv
  have p1 := hpos (Sum.inl ⟨a, ρ, b⟩) (by simp)
  have p2 := hpos (Sum.inl ⟨a, σ, b⟩) (by simp)
  have p3 := hpos (Sum.inl ⟨c, ρ, d⟩) (by simp)
  have p4 := hpos (Sum.inl ⟨c, σ, d⟩) (by simp)
  have p5 := hpos (Sum.inl ⟨d, ρᶜ, c⟩) (by simp)
  have p6 := hpos (Sum.inl ⟨d, σᶜ, c⟩) (by simp)
  -- Axiom 3 transfers the scale across the complement relabeling,
  -- witnessed against the third gamble aρb
  have hρc : v (.inl ⟨c, ρ, d⟩) = v (.inl ⟨d, ρᶜ, c⟩) := by
    have g1 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, ρ, d⟩ := by
      simpa using hacbd
    have g2 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨d, ρᶜ, c⟩ := by
      simp [(compl_ne_self (a := ρ)).symm]
    have e := ax3 c d ρ (.inl ⟨a, ρ, b⟩) g1 g2
    rw [hrule _ (by simp) _ (by simp) (Ne.symm g1),
        hrule _ (by simp) _ (by simp) (Ne.symm g2)] at e
    have := (pairwiseProb_eq_pairwiseProb_iff p3 p1 p5 p1).mp e
    exact mul_right_cancel₀ (ne_of_gt p1) this
  have hσc : v (.inl ⟨c, σ, d⟩) = v (.inl ⟨d, σᶜ, c⟩) := by
    have g1 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
      simpa using hacbd
    have g2 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨d, σᶜ, c⟩ := by
      simp [(compl_ne_self (a := σ)).symm]
    have e := ax3 c d σ (.inl ⟨a, σ, b⟩) g1 g2
    rw [hrule _ (by simp) _ (by simp) (Ne.symm g1),
        hrule _ (by simp) _ (by simp) (Ne.symm g2)] at e
    have := (pairwiseProb_eq_pairwiseProb_iff p4 p2 p6 p2).mp e
    exact mul_right_cancel₀ (ne_of_gt p2) this
  -- both same-outcome comparisons reduce to Q(ρ, σ)
  have hcd0 : dp.alt c d = 0 := by
    have hc := dp.P.binary_complement
      (show (Sum.inr c : Alternative A E) ≠ Sum.inr d by simpa using hcd)
    simp only [alt] at hd1 ⊢
    linarith
  have e2 : dp.gam ⟨c, ρ, d⟩ ⟨c, σ, d⟩ = dp.Q.binary σ ρ := by
    simp only [gam, alt] at hcd0 hd1 ⊢
    rw [dp.axiom2 c d hcd ρ σ, hcd0, hd1]
    ring
  have h34 : (Sum.inl ⟨c, ρ, d⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
    simpa using hρσ
  have e2' : dp.gam ⟨c, σ, d⟩ ⟨c, ρ, d⟩ = dp.Q.binary ρ σ := by
    have hPc : dp.gam ⟨c, ρ, d⟩ ⟨c, σ, d⟩ + dp.gam ⟨c, σ, d⟩ ⟨c, ρ, d⟩ = 1 := by
      simpa [gam] using dp.P.binary_complement h34
    have hQc := dp.Q.binary_complement hρσ
    linarith
  have e1 : dp.gam ⟨a, ρ, b⟩ ⟨a, σ, b⟩ = dp.gam ⟨c, σ, d⟩ ⟨c, ρ, d⟩ := by
    rw [gam_of_alt_eq_one hab ha1, e2']
  have h12 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  simp only [gam] at e1
  rw [hrule _ (by simp) _ (by simp) h12,
      hrule _ (by simp) _ (by simp) (Ne.symm h34)] at e1
  have hcross := (pairwiseProb_eq_pairwiseProb_iff p1 p2 p4 p3).mp e1
  -- v(aρb)·v(cρd) = v(cσd)·v(aσb); transfer via Axiom 3
  rw [hρc, hσc] at hcross
  linarith [hcross, mul_comm (v (.inl ⟨d, σᶜ, c⟩)) (v (.inl ⟨a, σ, b⟩))]

/-- **Axiom 5** (p. 84): some event is subjectively as likely as its
    complement. -/
def HasNeutralEvent (dp : DecomposablePreference A E) : Prop :=
  ∃ ε : E, dp.Q.binary ε εᶜ = 1 / 2

/-- The second clause of **Lemma 10** (p. 84): anything equi-likely with a
    neutral event is itself neutral — `C(½)` is exactly the neutral class. -/
theorem neutral_of_indiff_neutral [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp) {ρ σ : E}
    (hρ : Neutral dp ρ) (h : EventIndiff dp σ ρ) : Neutral dp σ := by
  rcases eq_or_ne σ ρ with rfl | hne
  · exact hρ
  have hσρ : dp.Q.binary σ ρ = 1 / 2 := (eventIndiff_iff_eq_half hne).mp h
  have h9 := q_compl_compl ax3 ax4 σ ρ
  have hcc : dp.Q.binary ρᶜ σᶜ = 1 / 2 := by linarith
  have icc : EventIndiff dp σᶜ ρᶜ :=
    ((eventIndiff_iff_eq_half (compl_injective.ne (Ne.symm hne))).mpr hcc).symm
  have h11 := theorem11 hnd h icc (compl_ne_self (a := σ)).symm
    (compl_ne_self (a := ρ)).symm
  unfold Neutral at hρ ⊢
  linarith [h11]

/-- **Lemma 11** (p. 85): with Axioms 3–5 and nondegeneracy there are at
    least three classes — a neutral event, a non-neutral event, and its
    complement are pairwise non-equivalent. -/
theorem atLeastThreeClasses [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp)
    (ax5 : HasNeutralEvent dp) :
    ∃ ε ρ : E, ¬EventIndiff dp ε ρ ∧ ¬EventIndiff dp ε ρᶜ ∧
      ¬EventIndiff dp ρ ρᶜ := by
  obtain ⟨ε, hε⟩ := ax5
  have hex : ∃ ρ : E, ¬Neutral dp ρ := by
    by_contra hall
    push Not at hall
    obtain ⟨ρ₀, σ₀, hρσ₀, hq₀⟩ := ax4.2
    exact hq₀ (neutral_indifferent hnd ax3 ax4 (hall ρ₀) (hall σ₀) hρσ₀)
  obtain ⟨ρ, hρ⟩ := hex
  exact ⟨ε, ρ, fun h => hρ (neutral_of_indiff_neutral hnd ax3 ax4 hε h.symm),
    fun h => hρ ((neutral_compl_iff ρ).mp
      (neutral_of_indiff_neutral hnd ax3 ax4 hε h.symm)),
    fun h => hρ ((eventIndiff_iff_eq_half (compl_ne_self (a := ρ)).symm).mp h)⟩

/-- **Theorem 12** (p. 84): given Axioms 3–5 and a nondegenerately
    discriminated pair of alternatives, `∼` partitions the events into
    exactly three classes: three pairwise non-equivalent events to one of
    which every event is equivalent. -/
theorem theorem12 [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp)
    (ax5 : HasNeutralEvent dp) :
    ∃ ρ₁ ρ₂ ρ₃ : E,
      (¬EventIndiff dp ρ₁ ρ₂ ∧ ¬EventIndiff dp ρ₁ ρ₃ ∧
        ¬EventIndiff dp ρ₂ ρ₃) ∧
      ∀ σ : E, EventIndiff dp σ ρ₁ ∨ EventIndiff dp σ ρ₂ ∨
        EventIndiff dp σ ρ₃ := by
  obtain ⟨ε, ρ, n1, n2, n3⟩ := atLeastThreeClasses hnd ax3 ax4 ax5
  refine ⟨ε, ρ, ρᶜ, ⟨n1, n2, n3⟩, fun σ => ?_⟩
  rcases atMostThreeClasses hnd σ ε ρ ρᶜ with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd h n1
  · exact absurd h n2
  · exact absurd h n3

end BooleanEvents

/-- The observable content of the §3.D.3 suggested factoring
    `v(aρb) = w(a,b)·φ(ρ)` (pp. 89–90): between gambles on the *same* event
    the event weight cancels, so binary choice follows the Luce rule on the
    outcome weights alone — "the step function described in theorem 13 can
    have only one step intermediate between 0 and 1" (p. 90). Luce offers the
    factoring as a hypothesis consistent with Theorems 13–14, not a theorem;
    accordingly it enters here as a hypothesis. -/
theorem gam_of_factored {S : Set (Gamble A E)} {v : Alternative A E → ℝ}
    {w : A → A → ℝ} {φ : E → ℝ}
    (hv : dp.P.BinaryRatioScaleOn (Sum.inl '' S) v) (hφ : ∀ τ, 0 < φ τ)
    (hfac : ∀ x y τ, (⟨x, τ, y⟩ : Gamble A E) ∈ S →
      v (.inl ⟨x, τ, y⟩) = w x y * φ τ)
    {a b c d : A} {ρ : E} (h₁ : (⟨a, ρ, b⟩ : Gamble A E) ∈ S)
    (h₂ : (⟨c, ρ, d⟩ : Gamble A E) ∈ S) (hacbd : ¬(a = c ∧ b = d)) :
    dp.gam ⟨a, ρ, b⟩ ⟨c, ρ, d⟩ = w a b / (w a b + w c d) := by
  obtain ⟨hpos, hrule⟩ := hv
  have m₁ : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ∈ Sum.inl '' S := ⟨_, h₁, rfl⟩
  have m₂ : (Sum.inl ⟨c, ρ, d⟩ : Alternative A E) ∈ Sum.inl '' S := ⟨_, h₂, rfl⟩
  have hg : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, ρ, d⟩ := by
    simpa using hacbd
  have hw1 : 0 < w a b := by
    have h := hpos _ m₁
    rw [hfac a b ρ h₁] at h
    by_contra hw
    push Not at hw
    nlinarith [hφ ρ]
  have hw2 : 0 < w c d := by
    have h := hpos _ m₂
    rw [hfac c d ρ h₂] at h
    by_contra hw
    push Not at hw
    nlinarith [hφ ρ]
  simp only [gam]
  rw [hrule _ m₁ _ m₂ hg, pairwiseProb, hfac a b ρ h₁, hfac c d ρ h₂,
      show w a b * φ ρ + w c d * φ ρ = (w a b + w c d) * φ ρ by ring,
      mul_div_mul_right _ _ (ne_of_gt (hφ ρ))]

end DecomposablePreference

end Utility

end Luce1959
