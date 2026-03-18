import Linglib.Core.Agent.RationalAction

/-!
# Psychophysics: Stevens' Power Law and Multidimensional Stimuli @cite{luce-1959}


@cite{luce-1959} §2.B–C: the power-law specialization of the Fechnerian framework
and its extension to multi-dimensional stimulus continua.

## §2.B: Stevens' Power Law (pp. 44–49)

Stevens' magnitude estimation experiments yield ψ(s) = k · sⁿ — a power function
relating physical stimulus intensity to psychological magnitude. Luce shows this
is not an independent discovery but a **corollary** of the Fechnerian framework
(`luce_fechnerian_exp` in `RationalAction.lean`) under a change of variables.

The key insight: if we work with log-intensity `u = log s` rather than raw
intensity `s`, then the ratio scale `v(s) = C · sⁿ = C · exp(n · log s)`
is exactly the exponential form forced by the Cauchy equation. In other words,
Stevens' power law IS Fechner's log law, viewed in different coordinates:

- **Fechner** (interval scale on log-intensity): `v = C · exp(n · u)`
- **Stevens** (ratio scale on raw intensity): `v = C · sⁿ`

The pairwise choice probability under Stevens' power law is:

  `P(s₁, s₂) = s₁ⁿ / (s₁ⁿ + s₂ⁿ)`

which is the Luce choice rule with `score(s) = sⁿ`.

## §2.C: Interaction of Stimulus Continua (pp. 49–53)

When stimuli vary along multiple dimensions simultaneously (e.g., both loudness
and brightness), Luce shows the choice rule decomposes multiplicatively:

  `v(a₁, a₂) = v₁(a₁) · v₂(a₂)`

provided the dimensions contribute independently to discriminability. This
`DimensionIndependence` axiom says that the relative discriminability along
one dimension does not depend on the value along the other.

-/

namespace Core

open Real BigOperators Finset

-- ============================================================================
-- §2.B: Stevens' Power Law
-- ============================================================================

/-- A Stevens power-law scale: ψ(s) = k · sⁿ.

The exponent `n` characterizes the sensory modality (e.g., n ≈ 0.67 for
brightness, n ≈ 3.5 for electric shock). The coefficient `k` is a unit
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
    let ra := stevens_is_luce σ (![s₁, s₂]) (λ i => by fin_cases i <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one])
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

/-- **Stevens–Fechner equivalence** (@cite{luce-1959}, §2.B):
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

-- ============================================================================
-- §2.C: Interaction of Stimulus Continua
-- ============================================================================

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

/-- Independence axiom for multi-dimensional stimuli (@cite{luce-1959}, §2.C):
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

/-- **Multidimensional decomposition** (@cite{luce-1959}, §2.C, Theorem):
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
      funext fun d => if_pos (Finset.mem_univ d)
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
    have hmix_d₀ : (mix T') d₀ = a₀ d₀ := if_neg hd₀
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
    (λ d _ => le_of_lt (ms.scale_pos d (stimulus a d)))

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

-- ============================================================================
-- §2.B–C Connection: Stevens Power Law on Multiple Dimensions
-- ============================================================================

/-- Positive reals: the natural domain for stimulus intensities.
    Wraps a real number with a proof of positivity. -/
structure PosReal where
  val : ℝ
  pos : 0 < val

/-- A multi-dimensional Stevens scale: each dimension has its own
    power-law exponent. The overall scale is the product of per-dimension
    power functions.

    Example: for loudness (n₁ ≈ 0.67) × brightness (n₂ ≈ 0.33),
    `v(s₁, s₂) = C · s₁^0.67 · s₂^0.33`.

    The domain is `PosReal` (positive reals) because stimulus intensities
    are inherently positive, and `rpow` requires a positive base. -/
noncomputable def multidimStevens {D : Type*} [Fintype D]
    (exponents : D → StevensScale) :
    MultidimStimulus D (λ _ => PosReal) where
  scale _ s := s.val ^ (exponents _).n
  scale_pos d s := rpow_pos_of_pos s.pos (exponents d).n

/-- Each dimension of a multi-dimensional Stevens model satisfies
    the Fechner equivalence independently. -/
theorem multidimStevens_fechner_per_dim {D : Type*} [Fintype D]
    (exponents : D → StevensScale) (d : D) {s : ℝ} (hs : 0 < s) :
    s ^ (exponents d).n = exp ((exponents d).n * log s) := by
  rw [rpow_def_of_pos hs, mul_comm (log s)]

end Core
