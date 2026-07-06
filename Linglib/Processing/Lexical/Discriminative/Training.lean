import Linglib.Core.Probability.Choice.Learning
import Linglib.Processing.Lexical.Discriminative.Defs
import Linglib.Processing.Lexical.Discriminative.Measures
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# DLM training: endstate vs frequency-informed learning
[baayen-2019] [gahl-baayen-2024] [heitmeier-2024] [heitmeier-chuang-baayen-2026]

The DLM's trained production map, characterised as the minimiser of a
frequency-weighted quadratic loss. The choice of frequency weights `q` is the
cognitive commitment (uniform = endstate learning, token counts =
frequency-informed learning); the optimisation is fixed across theories.

## Main definitions

* `TrainingExperience`, `FrequencyVector`, `weightedLoss`, `IsERMSolution`,
  with `IsELSolution`/`IsFILSolution` the uniform and frequency-weighted cases.
* `TrainingExperience.sqrtScale`, `residualPairing`, `whCorrection`, `whUpdate`.

## Main results

* `ermSolution_iff_rescaled`: only the empirical distribution of `q` matters.
* `isERMSolution_iff_coordResidual`: ERM is columnwise-unbeatable regression.
* `isELSolution_sqrtScale_iff`: FIL under `q` is EL on the `√q`-premultiplied
  experience ([heitmeier-2024]'s FIL-EL equivalence, invertibility-free).
* `exists_isERMSolution`: ERM solutions exist, by columnwise orthogonal
  projection.
* `isERMSolution_iff_residualPairing_eq_zero`: the normal equations
  `SᵀQ(SG − C) = 0` as an invertibility-free iff.
* `IsERMSolution.apply_eq_of_mem_span` / `exists_apply_ne`: fitted values are
  unique exactly on the span of experienced meanings.
* `isERMSolution_iff_whEquilibrium`: the endstate of learning is the
  equilibrium of Widrow-Hoff error-driven learning.
* `whUpdate_single_eq_rescorlaWagner_update`: on binary cues with uniform
  salience, a Widrow-Hoff step is a Rescorla-Wagner trial
  (`Core.RescorlaWagner`).

## TODO

Closed form `G = (SᵀS)⁻¹SᵀC` under full column rank; Widrow-Hoff trajectory
convergence (the fixed-point half is `isERMSolution_iff_whEquilibrium`);
approximate-decodability gap bounds for `semSup`.
-/

namespace Processing.Lexical.Discriminative

noncomputable section TrainingSubstrate

variable {m n d : ℕ}  -- m = numEvents, n = formDim, d = meaningDim

/-! ### Substrate types -/

/-- A **training experience** is a finite indexed collection of
    `(meaning, form)` observation pairs. The paper's `S` matrix has
    rows `data.meanings i` and `C` matrix has rows `data.forms i`,
    indexed by event `i : Fin m`.

    The cognitive interpretation: each `i : Fin m` is a "usage event"
    — a single attestation of a (meaning, form) pair. Type-based
    learning treats each unique pair as one event; frequency-informed
    learning may have multiple events per pair (replication = weight,
    deferred). -/
structure TrainingExperience (numEvents formDim meaningDim : ℕ) where
  meanings : Fin numEvents → MeaningVec meaningDim
  forms    : Fin numEvents → FormVec formDim

/-- A **frequency vector** — paper notation `Q` (the diagonal entries
    of the weight matrix in [gahl-baayen-2024] appendix §A1.3).
    One nonneg weight per usage event.

    We use `Fin m → ℝ` (rather than `Fin m → NNReal`) for proof
    convenience; nonnegativity is documented and asserted as a
    hypothesis in theorems that need it. The cognitive theory choice
    IS the choice of `q`:

    - `q ≡ 1` (uniform): type-based learning → EL
    - `q i = #occurrences i`: frequency-informed → FIL
    - `q i = log(#occurrences i)`: log-frequency learning (which
      [gahl-baayen-2024]'s appendix cautions distorts learning relative
      to incremental Widrow-Hoff)
    - `q i = exp(-decay · timeAgo i)`: recency-weighted

    All instantiations of `FrequencyVector` correspond to different
    cognitive commitments about which usage events count for learning. -/
abbrev FrequencyVector (numEvents : ℕ) : Type := Fin numEvents → ℝ

/-- The constant-1 frequency vector — type-uniform weighting; every
    event counts once regardless of frequency. Endstate learning
    operates with this `q`. -/
def uniformFrequency (m : ℕ) : FrequencyVector m :=
  fun _ => 1

/-- Total mass of a frequency vector — the sum of all event weights.
    Cognitive interpretation: the total accumulated experience the
    learner has been exposed to. -/
def FrequencyVector.totalMass (q : FrequencyVector m) : ℝ :=
  ∑ i, q i

/-- Normalise a frequency vector so its weights sum to 1. The result
    represents the **empirical distribution** over events. Note this
    is a `FrequencyVector` (still typed as `Fin m → ℝ`); for the
    actual `PMF` cast use `PMF.ofRealWeightFn` from
    `Core.Probability.Constructions`. -/
def FrequencyVector.normalize (q : FrequencyVector m) : FrequencyVector m :=
  fun i => q i / q.totalMass

@[simp] theorem FrequencyVector.normalize_apply
    (q : FrequencyVector m) (i : Fin m) :
    q.normalize i = q i / q.totalMass := rfl

/-! ### The weighted loss -/

/-- Squared coordinate-distance between two form vectors:
    `Σⱼ (a j - b j)²`. Direct formula, no normed-space machinery
    required. Distinct from the bare-Pi sup-norm in `Normed.lean`;
    here we want the L² (Frobenius) inner product structure on
    `Fin n → ℝ` that the paper's quadratic loss uses. -/
def squaredDist (a b : FormVec n) : ℝ :=
  ∑ j, (a j - b j) ^ 2

theorem squaredDist_self (a : FormVec n) : squaredDist a a = 0 :=
  Finset.sum_eq_zero fun _ _ => by rw [sub_self]; ring

theorem squaredDist_nonneg (a b : FormVec n) : 0 ≤ squaredDist a b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The **frequency-weighted training loss** for a candidate
    production map `G`:

    `weightedLoss data q G = Σᵢ qᵢ · ‖G(meaningsᵢ) − formsᵢ‖²`

    where `‖·‖²` is squared coordinate-distance (= squared Frobenius
    norm on the form-vector slot).

    The papers specify the mapping procedurally — premultiply `S` and `C`
    by `√Q` and solve the normal equations ([gahl-baayen-2024] appendix;
    [heitmeier-chuang-baayen-2026]); this loss is the standard variational
    characterisation of that procedure, connected to it by
    `weightedLoss_sqrtScale`. The cognitive commitment is at the level of
    this loss function: the learner minimises the per-event squared
    mismatch between produced and observed form vectors, weighted by
    frequency of occurrence. -/
def weightedLoss
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) : ℝ :=
  ∑ i, q i * squaredDist (G (data.meanings i)) (data.forms i)

theorem weightedLoss_nonneg
    (data : TrainingExperience m n d) {q : FrequencyVector m}
    (hq : ∀ i, 0 ≤ q i) (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    0 ≤ weightedLoss data q G :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hq k) (squaredDist_nonneg _ _)

/-! ### Solution Props: ERM, EL, FIL -/

/-- A linear map `G` is an **empirical risk minimiser** (ERM) for
    the experience `data` under frequency vector `q` if no other
    linear map achieves a smaller weighted loss.

    The cognitive theory choice IS the choice of `q`. Different
    theories of learning specify different `q`'s; the optimisation
    procedure (minimise the resulting weighted L² loss) is fixed
    across them. -/
def IsERMSolution
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) : Prop :=
  ∀ G' : MeaningVec d →ₗ[ℝ] FormVec n,
    weightedLoss data q G ≤ weightedLoss data q G'

/-- An **endstate-learning solution** for the experience: an ERM
    solution under type-uniform weights. Paper appendix §A1.1 of
    [gahl-baayen-2024]. -/
abbrev IsELSolution
    (data : TrainingExperience m n d)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) : Prop :=
  IsERMSolution data (uniformFrequency m) G

/-- A **frequency-informed learning solution** — abbreviation for
    ERM under arbitrary `q`. The cognitive interpretation that `q`
    is "token frequencies of usage events" lives in the choice of
    `q` the consumer passes; the substrate is agnostic about which
    `q` is empirically correct.

    Paper appendix §A1.3 of [gahl-baayen-2024] introduces FIL
    with `q` = corpus token frequencies; future cognitive theories
    may motivate other `q` choices. -/
abbrev IsFILSolution
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) : Prop :=
  IsERMSolution data q G

/-! ### Structural theorems -/

/-- **T-Loss-linearity**: the weighted loss is linear in the
    frequency vector. Direct algebraic fact; basis for `T-Rescaling`. -/
theorem weightedLoss_smul_frequency
    (data : TrainingExperience m n d) (q : FrequencyVector m) (c : ℝ)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    weightedLoss data (c • q) G = c * weightedLoss data q G := by
  unfold weightedLoss
  rw [Finset.mul_sum (Finset.univ : Finset (Fin m))]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (c • q) i * _ = c * (q i * _)
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- **T-Loss-add-distrib**: the weighted loss decomposes additively
    over the frequency vector. Used downstream to formalise mixture
    decompositions of cognitive theories. -/
theorem weightedLoss_add_frequency
    (data : TrainingExperience m n d) (q₁ q₂ : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    weightedLoss data (q₁ + q₂) G = weightedLoss data q₁ G + weightedLoss data q₂ G := by
  unfold weightedLoss
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (q₁ + q₂) i * _ = q₁ i * _ + q₂ i * _
  rw [Pi.add_apply, add_mul]

/-- **T-Rescaling**: ERM solutions are invariant under positive
    rescaling of the frequency vector. Relative frequencies matter;
    absolute scale doesn't.

    Cognitive content: a learner who has experienced word A 100
    times and word B 50 times has the same trained lexicon as one
    who experienced A 200 times and B 100 times. Time of accumulated
    experience (= overall scale of `q`) doesn't affect the trained
    end-state — only the relative ratios.

    Proved via `weightedLoss_smul_frequency`: scaling `q` by `c > 0`
    scales the loss by `c`; argmins are invariant under positive
    scalar multiples. -/
theorem ermSolution_iff_rescaled
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) {c : ℝ} (hc : 0 < c) :
    IsERMSolution data (c • q) G ↔ IsERMSolution data q G := by
  unfold IsERMSolution
  constructor
  · intro h G'
    have h' := h G'
    rw [weightedLoss_smul_frequency, weightedLoss_smul_frequency] at h'
    nlinarith
  · intro h G'
    have h' := h G'
    rw [weightedLoss_smul_frequency, weightedLoss_smul_frequency]
    nlinarith

/-- **T-Support (weak form)**: if `q i = 0`, event `i` contributes
    nothing to the weighted loss.

    Cognitive content: events that the learner has not experienced
    (`q i = 0`) cannot update the trained lexicon. Novel words and
    pseudowords don't retroactively modify the production map; they
    can only be processed by the existing `D.production` (which is
    polymorphic over the entire meaning space, hence applies to any
    meaning vector — but the trained map's coefficients reflect
    only the support of `q`). -/
theorem weightedLoss_zero_event_drops
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) (i₀ : Fin m) (h : q i₀ = 0) :
    weightedLoss data q G =
      weightedLoss data (Function.update q i₀ 0) G := by
  unfold weightedLoss
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = i₀
  · subst hi; rw [h, Function.update_self]
  · rw [Function.update_of_ne hi]

/-- **Definitional equivalence**: an `IsELSolution` is exactly an ERM
    solution under uniform weights. Paper-canonical: paper §3.1 of
    [gahl-baayen-2024] introduces EL as the special case of FIL
    with `Q = I`. Here `uniformFrequency = fun _ => 1` is the discrete
    analogue. -/
theorem isELSolution_eq_isERM_uniform
    (data : TrainingExperience m n d)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    IsELSolution data G ↔ IsERMSolution data (uniformFrequency m) G :=
  Iff.rfl

/-! ### Per-coordinate residual optimality

The loss separates across form coordinates: each column of `G`
regresses one cue's support on the semantic dimensions, "optimal in
the least-squares sense" ([heitmeier-chuang-baayen-2026] ch. 6). So
ERM is exactly columnwise unbeatability, and a coordinate that some
functional decodes exactly is reproduced exactly. -/

/-- Weighted squared residual of a predicted column `pred` against
    form coordinate `j₀` of the training data. -/
def coordResidual (data : TrainingExperience m n d) (q : FrequencyVector m)
    (pred : Fin m → ℝ) (j₀ : Fin n) : ℝ :=
  ∑ k, q k * (pred k - data.forms k j₀) ^ 2

theorem coordResidual_nonneg
    (data : TrainingExperience m n d) {q : FrequencyVector m}
    (hq : ∀ i, 0 ≤ q i) (pred : Fin m → ℝ) (j₀ : Fin n) :
    0 ≤ coordResidual data q pred j₀ :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hq k) (sq_nonneg _)

/-- **T-Separability**: the weighted loss is the sum over form
    coordinates of the per-coordinate residuals — each column of the
    production map is an independent regression. -/
theorem weightedLoss_eq_sum_coordResidual
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    weightedLoss data q G
      = ∑ j, coordResidual data q (fun k => G (data.meanings k) j) j := by
  unfold weightedLoss squaredDist coordResidual
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private theorem squaredDist_update (a b : FormVec n) (j₀ : Fin n) (x : ℝ) :
    squaredDist (Function.update a j₀ x) b
      = squaredDist a b - (a j₀ - b j₀) ^ 2 + (x - b j₀) ^ 2 := by
  unfold squaredDist
  rw [← Finset.add_sum_erase Finset.univ
        (fun j => (Function.update a j₀ x j - b j) ^ 2) (Finset.mem_univ j₀),
      ← Finset.add_sum_erase Finset.univ
        (fun j => (a j - b j) ^ 2) (Finset.mem_univ j₀),
      Finset.sum_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
  simp only [Function.update_self]
  ring

/-- **T-Coordinate-optimality**: `G` is an ERM solution iff at every form
    coordinate its column's residual is at most that of any linear
    functional of the meanings — ERM is columnwise-unbeatable regression.
    No sign condition on `q` in either direction. -/
theorem isERMSolution_iff_coordResidual
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    IsERMSolution data q G ↔
      ∀ (j₀ : Fin n) (w : MeaningVec d →ₗ[ℝ] ℝ),
        coordResidual data q (fun k => G (data.meanings k) j₀) j₀
          ≤ coordResidual data q (fun k => w (data.meanings k)) j₀ := by
  constructor
  · intro hG j₀ w
    -- the competitor: `G` with coordinate `j₀` replaced by `w`
    have happ : ∀ s,
        LinearMap.pi (Function.update (fun j => (LinearMap.proj j).comp G) j₀ w) s
          = Function.update (G s) j₀ (w s) := fun s => by
      funext j
      rcases eq_or_ne j j₀ with hj | hj
      · subst hj; simp only [LinearMap.pi_apply, Function.update_self]
      · simp only [LinearMap.pi_apply, Function.update_of_ne hj,
          LinearMap.comp_apply, LinearMap.proj_apply]
    have hloss : weightedLoss data q
          (LinearMap.pi (Function.update (fun j => (LinearMap.proj j).comp G) j₀ w))
        = weightedLoss data q G
          - coordResidual data q (fun k => G (data.meanings k) j₀) j₀
          + coordResidual data q (fun k => w (data.meanings k)) j₀ := by
      unfold weightedLoss coordResidual
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [happ, squaredDist_update]
      ring
    have h := hG (LinearMap.pi (Function.update (fun j => (LinearMap.proj j).comp G) j₀ w))
    rw [hloss] at h
    linarith
  · intro h G'
    rw [weightedLoss_eq_sum_coordResidual data q G,
      weightedLoss_eq_sum_coordResidual data q G']
    exact Finset.sum_le_sum fun j _ => h j ((LinearMap.proj j).comp G')

/-- **T-Decodable-exact-fit**: if some linear functional `w` of the meanings
    exactly reproduces coordinate `j₀` of the observed forms, then any ERM
    solution under positive weights also reproduces it exactly on the
    training events. Zero-residual case of `isERMSolution_iff_coordResidual`. -/
theorem IsERMSolution.coord_eq_of_decodable
    {data : TrainingExperience m n d} {q : FrequencyVector m} (hq : ∀ i, 0 < q i)
    {G : MeaningVec d →ₗ[ℝ] FormVec n} (hG : IsERMSolution data q G)
    {j₀ : Fin n} {w : MeaningVec d →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.meanings i) = data.forms i j₀) (i : Fin m) :
    G (data.meanings i) j₀ = data.forms i j₀ := by
  have hle := (isERMSolution_iff_coordResidual data q G).1 hG j₀ w
  have hB : coordResidual data q (fun k => w (data.meanings k)) j₀ = 0 :=
    Finset.sum_eq_zero fun k _ => by
      show q k * (w (data.meanings k) - data.forms k j₀) ^ 2 = 0
      rw [hw k, sub_self]; ring
  rw [hB] at hle
  have h0 : coordResidual data q (fun k => G (data.meanings k) j₀) j₀ = 0 :=
    le_antisymm hle (coordResidual_nonneg data (fun k => (hq k).le) _ _)
  have hnn : ∀ k ∈ Finset.univ,
      (0:ℝ) ≤ q k * (G (data.meanings k) j₀ - data.forms k j₀) ^ 2 :=
    fun k _ => mul_nonneg (hq k).le (sq_nonneg _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (Finset.mem_univ i)
  have hsq : (G (data.meanings i) j₀ - data.forms i j₀) ^ 2 = 0 :=
    (mul_eq_zero.1 hterm).resolve_left (hq i).ne'
  exact sub_eq_zero.1 (sq_eq_zero_iff.1 hsq)

/-- **T-Interpolation**: a map that reproduces every training form exactly
    is an ERM solution under any nonnegative weights — `IsERMSolution` is
    nonvacuous whenever the data are linearly interpolable. -/
theorem isERMSolution_of_interpolates
    {data : TrainingExperience m n d} {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    {G : MeaningVec d →ₗ[ℝ] FormVec n} (hG : ∀ i, G (data.meanings i) = data.forms i) :
    IsERMSolution data q G := fun G' => by
  have h0 : weightedLoss data q G = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hG k, squaredDist_self, mul_zero]
  rw [h0]
  exact weightedLoss_nonneg data hq G'

/-! ### Normal equations: ERM ⟺ residual orthogonality

[gahl-baayen-2024]'s appendix and [heitmeier-2024] compute the mappings from
the normal equations of regression (`SᵀQ(SG − C) = 0` premultiplied into closed
form under invertibility). Stated invertibility-free: `G` is an ERM solution
iff every residual-prediction pairing vanishes — the first-order condition of
the quadratic loss. Fitted values on experienced meanings are therefore unique
across ERM solutions, which is what makes the model's predictions (and the
`semSup` measures) well-defined properties of the training experience. -/

/-- The `q`-weighted pairing of `G`'s residuals with `H`'s predictions:
    `∑ᵢ qᵢ ⟨G(sᵢ) − cᵢ, H(sᵢ)⟩`. The normal equations say this vanishes
    for every `H` exactly at the ERM solutions. -/
def residualPairing (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G H : MeaningVec d →ₗ[ℝ] FormVec n) : ℝ :=
  ∑ i, q i * ∑ j, (G (data.meanings i) j - data.forms i j) * H (data.meanings i) j

/-- The `q`-weighted squared magnitude of `H`'s predictions on the
    training meanings. -/
def predictionEnergy (data : TrainingExperience m n d) (q : FrequencyVector m)
    (H : MeaningVec d →ₗ[ℝ] FormVec n) : ℝ :=
  ∑ i, q i * ∑ j, H (data.meanings i) j ^ 2

theorem predictionEnergy_nonneg (data : TrainingExperience m n d)
    {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    (H : MeaningVec d →ₗ[ℝ] FormVec n) : 0 ≤ predictionEnergy data q H :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg (hq i) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem residualPairing_smul (data : TrainingExperience m n d)
    (q : FrequencyVector m) (G : MeaningVec d →ₗ[ℝ] FormVec n) (t : ℝ)
    (H : MeaningVec d →ₗ[ℝ] FormVec n) :
    residualPairing data q G (t • H) = t * residualPairing data q G H := by
  unfold residualPairing
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem predictionEnergy_smul (data : TrainingExperience m n d)
    (q : FrequencyVector m) (t : ℝ) (H : MeaningVec d →ₗ[ℝ] FormVec n) :
    predictionEnergy data q (t • H) = t ^ 2 * predictionEnergy data q H := by
  unfold predictionEnergy
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Quadratic expansion of the weighted loss around `G`: perturbing by `H`
    adds twice the residual pairing plus the energy of the perturbation. -/
theorem weightedLoss_add (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G H : MeaningVec d →ₗ[ℝ] FormVec n) :
    weightedLoss data q (G + H)
      = weightedLoss data q G + 2 * residualPairing data q G H
        + predictionEnergy data q H := by
  unfold weightedLoss residualPairing predictionEnergy squaredDist
  simp only [LinearMap.add_apply, Pi.add_apply, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **T-Normal-equations**: `G` is an ERM solution iff every residual-prediction
    pairing vanishes — the first-order condition of the quadratic loss, with no
    invertibility hypothesis. -/
theorem isERMSolution_iff_residualPairing_eq_zero
    {data : TrainingExperience m n d} {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    {G : MeaningVec d →ₗ[ℝ] FormVec n} :
    IsERMSolution data q G ↔
      ∀ H : MeaningVec d →ₗ[ℝ] FormVec n, residualPairing data q G H = 0 := by
  constructor
  · intro hG H
    set B := residualPairing data q G H with hB
    set E := predictionEnergy data q H with hE
    have hE0 : 0 ≤ E := predictionEnergy_nonneg data hq H
    have key := hG (G + (-(B / (E + 1))) • H)
    rw [weightedLoss_add, residualPairing_smul, predictionEnergy_smul] at key
    have hE1 : (0:ℝ) < E + 1 := by linarith
    set t : ℝ := -(B / (E + 1)) with ht'
    have ht : t * (E + 1) = -B := by
      rw [ht']; field_simp
    have htB : t * B = -(t ^ 2 * (E + 1)) := by
      have hBt : B = -(t * (E + 1)) := by rw [ht]; ring
      rw [hBt]; ring
    have h0 : 0 ≤ 2 * (t * B) + t ^ 2 * E := by linarith
    have ht2 : t ^ 2 ≤ 0 := by nlinarith [sq_nonneg t, hE0]
    have htz : t = 0 := sq_eq_zero_iff.mp (le_antisymm ht2 (sq_nonneg t))
    have hBz : -B = 0 := by rw [← ht, htz]; ring
    linarith
  · intro h G'
    have hG' : G + (G' - G) = G' := by abel
    have hexp := weightedLoss_add data q G (G' - G)
    rw [hG', h (G' - G)] at hexp
    have := predictionEnergy_nonneg data hq (G' - G)
    linarith [hexp.ge, hexp.le]

/-- The normal equations in the papers' columnwise form: for every form
    coordinate, the `q`-weighted residual column is orthogonal to every linear
    functional of the meanings — quantifying over functionals is `SᵀQ(SG − C) = 0`
    with `Sᵀ`'s rows generalized to the full dual space. -/
theorem isERMSolution_iff_forall_column
    {data : TrainingExperience m n d} {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    {G : MeaningVec d →ₗ[ℝ] FormVec n} :
    IsERMSolution data q G ↔
      ∀ (j : Fin n) (w : MeaningVec d →ₗ[ℝ] ℝ),
        ∑ i, q i * ((G (data.meanings i) j - data.forms i j) * w (data.meanings i))
          = 0 := by
  rw [isERMSolution_iff_residualPairing_eq_zero hq]
  have hswap : ∀ H : MeaningVec d →ₗ[ℝ] FormVec n,
      residualPairing data q G H
        = ∑ j, ∑ i, q i *
            ((G (data.meanings i) j - data.forms i j) * H (data.meanings i) j) := by
    intro H
    unfold residualPairing
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  constructor
  · intro h j w
    have := h ((LinearMap.single ℝ (fun _ : Fin n => ℝ) j).comp w)
    rw [hswap] at this
    simpa [LinearMap.comp_apply, LinearMap.single_apply, Pi.single_apply,
           mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
           Finset.sum_ite_eq', Finset.mem_univ] using this
  · intro h H
    rw [hswap]
    refine Finset.sum_eq_zero fun j _ => ?_
    simpa using h j ((LinearMap.proj j).comp H)

/-- **T-Unique-fit**: all ERM solutions under positive weights produce the same
    predicted form for every experienced meaning — fitted values are unique even
    when the ERM map is not. Differences between ERM solutions live entirely off
    the training span. -/
theorem IsERMSolution.apply_meanings_eq
    {data : TrainingExperience m n d} {q : FrequencyVector m} (hq : ∀ i, 0 < q i)
    {G G' : MeaningVec d →ₗ[ℝ] FormVec n}
    (hG : IsERMSolution data q G) (hG' : IsERMSolution data q G') (i : Fin m) :
    G (data.meanings i) = G' (data.meanings i) := by
  have hB := (isERMSolution_iff_residualPairing_eq_zero fun k => (hq k).le).mp
    hG (G' - G)
  have hGadd : G + (G' - G) = G' := by abel
  have hexp := weightedLoss_add data q G (G' - G)
  rw [hGadd, hB] at hexp
  have hE : predictionEnergy data q (G' - G) = 0 := by
    have h1 := hG G'
    have h2 := hG' G
    linarith
  have hterm : ∀ k ∈ Finset.univ,
      (0:ℝ) ≤ q k * ∑ j, (G' - G) (data.meanings k) j ^ 2 := fun k _ =>
    mul_nonneg (hq k).le (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hE i (Finset.mem_univ i)
  have hsum : ∑ j, (G' - G) (data.meanings i) j ^ 2 = 0 :=
    (mul_eq_zero.mp hi).resolve_left (hq i).ne'
  funext j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).mp
    hsum j (Finset.mem_univ j)
  have h0 : G' (data.meanings i) j - G (data.meanings i) j = 0 := by
    simpa [LinearMap.sub_apply, Pi.sub_apply] using sq_eq_zero_iff.mp hj
  linarith [sub_eq_zero.mp h0]

/-- Uniqueness of fitted values extends by linearity: ERM solutions agree at
    every meaning in the **span** of the experienced ones. Together with
    `IsERMSolution.exists_apply_ne`, novel-item predictions are well-defined
    exactly on the span of experience — the model generalizes by linear
    combination of experienced meanings and is unconstrained beyond them. -/
theorem IsERMSolution.apply_eq_of_mem_span
    {data : TrainingExperience m n d} {q : FrequencyVector m} (hq : ∀ i, 0 < q i)
    {G G' : MeaningVec d →ₗ[ℝ] FormVec n}
    (hG : IsERMSolution data q G) (hG' : IsERMSolution data q G')
    {s : MeaningVec d} (hs : s ∈ Submodule.span ℝ (Set.range data.meanings)) :
    G s = G' s := by
  have hker : Submodule.span ℝ (Set.range data.meanings)
      ≤ LinearMap.ker (G' - G) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h := IsERMSolution.apply_meanings_eq hq hG hG' i
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply,
               sub_eq_zero]
    exact h.symm
  have hmem := hker hs
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hmem
  exact hmem.symm

/-- **T-Underdetermination**: off the span of experienced meanings, ERM
    solutions are genuinely underdetermined — any ERM solution can be modified
    into another with a different prediction at any unexperienced meaning
    direction, by adding a correction supported on the annihilator of the span. -/
theorem IsERMSolution.exists_apply_ne [NeZero n]
    {data : TrainingExperience m n d} {q : FrequencyVector m}
    {G : MeaningVec d →ₗ[ℝ] FormVec n} (hG : IsERMSolution data q G)
    {s : MeaningVec d} (hs : s ∉ Submodule.span ℝ (Set.range data.meanings)) :
    ∃ G' : MeaningVec d →ₗ[ℝ] FormVec n,
      IsERMSolution data q G' ∧ G s ≠ G' s := by
  have h1 : ¬ ∀ φ ∈ (Submodule.span ℝ (Set.range data.meanings)).dualAnnihilator,
      φ s = 0 := fun h => hs
    ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ s).mp h)
  push Not at h1
  obtain ⟨φ, hφmem, hφs⟩ := h1
  have hφ0 : ∀ x ∈ Submodule.span ℝ (Set.range data.meanings), φ x = 0 :=
    (Submodule.mem_dualAnnihilator φ).mp hφmem
  refine ⟨G + φ.smulRight (Pi.single 0 1), fun G'' => ?_, fun h => ?_⟩
  · have hsame : weightedLoss data q (G + φ.smulRight (Pi.single 0 1))
        = weightedLoss data q G := by
      unfold weightedLoss
      refine Finset.sum_congr rfl fun i _ => ?_
      have hzero : φ (data.meanings i) = 0 :=
        hφ0 _ (Submodule.subset_span (Set.mem_range_self i))
      simp [LinearMap.add_apply, LinearMap.smulRight_apply, hzero]
    rw [hsame]
    exact hG G''
  · have h0 := congrFun h (0 : Fin n)
    simp only [LinearMap.add_apply, LinearMap.smulRight_apply, Pi.add_apply,
               Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h0
    exact hφs (by linarith)

/-! ### Widrow-Hoff dynamics: the endstate as equilibrium

[heitmeier-2024] learns the mappings incrementally by the Widrow-Hoff rule
`Fₜ₊₁ = Fₜ + cₜᵀ(sₜ − ŝₜ)·η` — an error-driven rank-one correction per usage
event, with frequencies entering as replicated learning events —
and [heitmeier-chuang-baayen-2026] observes the rule is stochastic gradient
descent on the quadratic loss. `whCorrection` is the production-direction
correction; `isERMSolution_iff_whEquilibrium` earns the *endstate* name as a
theorem: the ERM solutions are exactly the equilibria of frequency-weighted
error-driven learning. -/

/-- The dot-product functional `s' ↦ ∑ l, x l * s' l`. -/
def dotFunctional {k : ℕ} (x : Fin k → ℝ) : (Fin k → ℝ) →ₗ[ℝ] ℝ where
  toFun s := ∑ l, x l * s l
  map_add' s s' := by
    simp only [Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' t s := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

theorem dotFunctional_apply {k : ℕ} (x s : Fin k → ℝ) :
    dotFunctional x s = ∑ l, x l * s l := rfl

theorem dotFunctional_comm {k : ℕ} (x y : Fin k → ℝ) :
    dotFunctional x y = dotFunctional y x := by
  rw [dotFunctional_apply, dotFunctional_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- Every linear functional on `MeaningVec d` is a dot product. -/
private theorem eq_dotFunctional (w : MeaningVec d →ₗ[ℝ] ℝ) :
    w = dotFunctional (fun l => w fun j' => if l = j' then 1 else 0) := by
  refine LinearMap.ext fun s => ?_
  rw [LinearMap.pi_apply_eq_sum_univ w s, dotFunctional_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul, mul_comm]

/-- The single-event **Widrow-Hoff correction** to a production map: the
    rank-one error-driven update direction `s' ↦ ⟨s, s'⟩ • (c − G s)`
    ([heitmeier-2024]'s `cᵀ(s − ŝ)`, production direction). -/
def whCorrection (s : MeaningVec d) (c : FormVec n)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) : MeaningVec d →ₗ[ℝ] FormVec n :=
  (dotFunctional s).smulRight (c - G s)

@[simp] theorem whCorrection_apply (s : MeaningVec d) (c : FormVec n)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) (s' : MeaningVec d) :
    whCorrection s c G s' = dotFunctional s s' • (c - G s) := rfl

/-- One **Widrow-Hoff learning step** on the observation `(s, c)` with
    learning rate `η`. -/
def whUpdate (η : ℝ) (s : MeaningVec d) (c : FormVec n)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) : MeaningVec d →ₗ[ℝ] FormVec n :=
  G + η • whCorrection s c G

/-- A single event's update fixes `G` iff that event's correction vanishes. -/
theorem whUpdate_eq_self_iff {η : ℝ} (hη : η ≠ 0) (s : MeaningVec d)
    (c : FormVec n) (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    whUpdate η s c G = G ↔ whCorrection s c G = 0 := by
  unfold whUpdate
  constructor
  · intro h
    have h' : G + η • whCorrection s c G = G + 0 := by simpa using h
    exact (smul_eq_zero.mp (add_left_cancel h')).resolve_left hη
  · intro h
    rw [h, smul_zero, add_zero]

private theorem sum_whCorrection_apply (data : TrainingExperience m n d)
    (q : FrequencyVector m) (G : MeaningVec d →ₗ[ℝ] FormVec n)
    (s' : MeaningVec d) (j : Fin n) :
    (∑ i, q i • whCorrection (data.meanings i) (data.forms i) G) s' j
      = ∑ i, q i * ((data.forms i j - G (data.meanings i) j)
          * dotFunctional s' (data.meanings i)) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, whCorrection_apply,
             Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotFunctional_comm s' (data.meanings i)]
  ring

/-- The error-form and residual-form pairings sum to zero. -/
private theorem errorSum_add_residSum (data : TrainingExperience m n d)
    (q : FrequencyVector m) (G : MeaningVec d →ₗ[ℝ] FormVec n)
    (s' : MeaningVec d) (j : Fin n) :
    (∑ i, q i * ((data.forms i j - G (data.meanings i) j)
        * dotFunctional s' (data.meanings i)))
      + ∑ i, q i * ((G (data.meanings i) j - data.forms i j)
          * dotFunctional s' (data.meanings i)) = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _ => by ring

/-- **T-Equilibrium**: `G` is an ERM solution iff the frequency-weighted total
    Widrow-Hoff correction vanishes. The *endstate of learning* is exactly the
    equilibrium of error-driven learning — regression solutions and learning
    equilibria coincide, with no invertibility hypothesis. -/
theorem isERMSolution_iff_whEquilibrium
    {data : TrainingExperience m n d} {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    {G : MeaningVec d →ₗ[ℝ] FormVec n} :
    IsERMSolution data q G ↔
      ∑ i, q i • whCorrection (data.meanings i) (data.forms i) G = 0 := by
  rw [isERMSolution_iff_forall_column hq]
  constructor
  · intro h
    refine LinearMap.ext fun s' => funext fun j => ?_
    rw [sum_whCorrection_apply]
    have hres := h j (dotFunctional s')
    have hzero := errorSum_add_residSum data q G s' j
    simp only [LinearMap.zero_apply, Pi.zero_apply]
    linarith
  · intro h j w
    rw [eq_dotFunctional w]
    have h0 := congrFun
      (LinearMap.congr_fun h (fun l => w fun j' => if l = j' then 1 else 0)) j
    rw [sum_whCorrection_apply] at h0
    simp only [LinearMap.zero_apply, Pi.zero_apply] at h0
    have hzero := errorSum_add_residSum data q G
      (fun l => w fun j' => if l = j' then 1 else 0) j
    linarith

/-- **T-RW-specialization**: on a binary cue vector with uniform salience, one
    Widrow-Hoff step reproduces one Rescorla-Wagner trial: the updated weight
    of each cue `l` — the updated map evaluated on the `l`-th basis vector, at
    the single outcome coordinate — is `Core.RescorlaWagner.update`. The
    discrete NDL special case of the DLM's learning rule ([heitmeier-2024];
    [rescorla-wagner-1972] via `Core.Probability.Choice.Learning`). -/
theorem whUpdate_single_eq_rescorlaWagner_update
    (rw : Core.RescorlaWagner (Fin d)) (hsal : ∀ c, rw.salience c = 1)
    (present : Finset (Fin d)) (V : Fin d → ℝ) (l : Fin d) :
    whUpdate rw.learnRate (fun c => if c ∈ present then (1:ℝ) else 0)
        ((fun _ => rw.maxCond) : FormVec 1)
        ((dotFunctional V).smulRight fun _ => 1)
        (Pi.single l 1) 0
      = rw.update present V l := by
  have hsum : (∑ l', if l' ∈ present then V l' else 0) = ∑ c ∈ present, V c := by
    simp [Finset.sum_ite_mem, Finset.univ_inter]
  unfold whUpdate Core.RescorlaWagner.update Core.RescorlaWagner.predictionError
  simp only [LinearMap.add_apply, LinearMap.smul_apply, whCorrection_apply,
             LinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply,
             smul_eq_mul, Pi.sub_apply, dotFunctional_apply, Pi.single_apply,
             mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
             if_true, hsal, hsum]
  split_ifs with h <;> ring

/-! ### Rescaling invariance

The "frequency-vector-as-counts" view (DLM-paper-faithful) and the
"frequency-vector-as-empirical-distribution" view (Bayesian-tradition) make
identical predictions about which production maps are ERM-optimal. For the
`PMF (Fin m)` cast of `q.normalize`, call `PMF.ofRealWeightFn` from
`Core.Probability.Constructions` directly. -/

/-- **Normalisation preserves ERM solutions.** A FrequencyVector and
    its empirical distribution agree on which production maps are ERM
    solutions. This is the formal statement that the cognitive content
    is in the *relative weights* (= the normalised distribution) and
    not in the absolute scale.

    Direct application of `ermSolution_iff_rescaled` with `c = 1/totalMass`. -/
theorem isERMSolution_normalize_iff
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) (h : 0 < q.totalMass) :
    IsERMSolution data q.normalize G ↔ IsERMSolution data q G := by
  have hinv : (0:ℝ) < (q.totalMass)⁻¹ := inv_pos.mpr h
  have hnorm : q.normalize = (q.totalMass)⁻¹ • q := by
    funext i
    show q i / q.totalMass = (q.totalMass)⁻¹ * q i
    rw [div_eq_inv_mul]
  rw [hnorm]
  exact ermSolution_iff_rescaled data q G hinv

/-- **Two FrequencyVectors with identical empirical distributions are
    ERM-equivalent.** The cognitive content lives at the level of the
    normalised distribution; theories that assign different absolute
    scales but the same relative frequencies make the same predictions. -/
theorem isERMSolution_of_same_normalize
    (data : TrainingExperience m n d) (q₁ q₂ : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n)
    (h₁ : 0 < q₁.totalMass) (h₂ : 0 < q₂.totalMass)
    (hnorm : q₁.normalize = q₂.normalize) :
    IsERMSolution data q₁ G ↔ IsERMSolution data q₂ G := by
  rw [← isERMSolution_normalize_iff data q₁ G h₁,
      ← isERMSolution_normalize_iff data q₂ G h₂, hnorm]

/-! ### √Q transport and existence of ERM solutions

[gahl-baayen-2024]'s appendix computes EL from the normal equations of
regression and FIL by solving the EL problem on `√Q`-premultiplied `S` and
`C` matrices; [heitmeier-chuang-baayen-2026] gives the same construction, and
[heitmeier-2024] proves the equivalence with frequency-replicated training
data via the closed-form normal-equations solution, under invertibility.
Here the premultiplied experience is `TrainingExperience.sqrtScale`, the
equivalence (`isELSolution_sqrtScale_iff`) is stated invertibility-free at
the level of ERM solution sets, and ERM existence follows by orthogonal
projection onto the prediction subspace, columnwise. -/

/-- The `√q`-premultiplied training experience: event `i` scaled by
    `√(q i)` in both meaning and form — the `√Q`-premultiplication of `S`
    and `C` of [gahl-baayen-2024]'s appendix and
    [heitmeier-chuang-baayen-2026]. -/
def TrainingExperience.sqrtScale (data : TrainingExperience m n d)
    (q : FrequencyVector m) : TrainingExperience m n d where
  meanings i := Real.sqrt (q i) • data.meanings i
  forms i := Real.sqrt (q i) • data.forms i

theorem squaredDist_smul (c : ℝ) (a b : FormVec n) :
    squaredDist (c • a) (c • b) = c ^ 2 * squaredDist a b := by
  unfold squaredDist
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- **T-Sqrt-transport** (loss level): the uniform-weight loss on the
    `√q`-premultiplied experience is the `q`-weighted loss on the original. -/
theorem weightedLoss_sqrtScale (data : TrainingExperience m n d)
    {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    weightedLoss (data.sqrtScale q) (uniformFrequency m) G
      = weightedLoss data q G := by
  unfold weightedLoss
  refine Finset.sum_congr rfl fun i _ => ?_
  show 1 * squaredDist (G (Real.sqrt (q i) • data.meanings i))
        (Real.sqrt (q i) • data.forms i) = _
  rw [one_mul, map_smul, squaredDist_smul, Real.sq_sqrt (hq i)]

/-- **T-Sqrt-transport**: FIL under `q` is exactly EL on the
    `√q`-premultiplied experience — [heitmeier-2024]'s FIL-EL equivalence,
    invertibility-free. -/
theorem isELSolution_sqrtScale_iff (data : TrainingExperience m n d)
    {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    IsELSolution (data.sqrtScale q) G ↔ IsERMSolution data q G := by
  unfold IsELSolution IsERMSolution
  exact forall_congr' fun G' => by
    rw [weightedLoss_sqrtScale data hq, weightedLoss_sqrtScale data hq]

private theorem coordResidual_uniform_eq_norm_sq (data : TrainingExperience m n d)
    (pred : Fin m → ℝ) (j : Fin n) :
    coordResidual data (uniformFrequency m) pred j
      = ‖WithLp.toLp 2 (fun k => data.forms k j)
          - WithLp.toLp 2 pred‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold coordResidual
  refine Finset.sum_congr rfl fun k _ => ?_
  show 1 * (pred k - data.forms k j) ^ 2 = _
  rw [one_mul, ← WithLp.toLp_sub]
  simp only [Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  ring

private theorem exists_forall_coordResidual_le (data : TrainingExperience m n d)
    (j : Fin n) :
    ∃ w : MeaningVec d →ₗ[ℝ] ℝ, ∀ w' : MeaningVec d →ₗ[ℝ] ℝ,
      coordResidual data (uniformFrequency m) (fun k => w (data.meanings k)) j
        ≤ coordResidual data (uniformFrequency m) (fun k => w' (data.meanings k)) j := by
  classical
  -- prediction subspace: range of the evaluation map into Euclidean event space
  set Ev : (MeaningVec d →ₗ[ℝ] ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap.comp
      (LinearMap.pi fun k => LinearMap.applyₗ (data.meanings k)) with hEv
  set y : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun k => data.forms k j) with hy
  haveI : CompleteSpace ↥(LinearMap.range Ev) := FiniteDimensional.complete ℝ _
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp ((LinearMap.range Ev).starProjection_apply_mem y)
  refine ⟨w, fun w' => ?_⟩
  have hmin : ∀ v : ↥(LinearMap.range Ev),
      ‖y - (LinearMap.range Ev).starProjection y‖ ≤ ‖y - ↑v‖ := fun v => by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro r ⟨x, rfl⟩; exact norm_nonneg _⟩ v
  have hle : ‖y - Ev w‖ ≤ ‖y - Ev w'‖ := by
    rw [hw]
    exact hmin ⟨Ev w', LinearMap.mem_range_self _ _⟩
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hEvw : ∀ v : MeaningVec d →ₗ[ℝ] ℝ,
      Ev v = WithLp.toLp 2 (fun k => v (data.meanings k)) := fun _ => rfl
  rw [coordResidual_uniform_eq_norm_sq, coordResidual_uniform_eq_norm_sq]
  rw [hEvw w, hEvw w', hy] at hsq
  exact hsq

/-- **T-EL-existence**: endstate solutions exist — the normal-equations
    solvability of [gahl-baayen-2024]'s appendix, by orthogonal projection
    of each observed form column onto the prediction subspace. -/
theorem exists_isELSolution (data : TrainingExperience m n d) :
    ∃ G : MeaningVec d →ₗ[ℝ] FormVec n, IsELSolution data G := by
  choose w hw using exists_forall_coordResidual_le data
  refine ⟨LinearMap.pi w, (isERMSolution_iff_coordResidual _ _ _).mpr fun j w' => ?_⟩
  simpa only [LinearMap.pi_apply] using hw j w'

/-- **T-Existence**: ERM solutions exist for any nonnegative frequency
    vector, via `exists_isELSolution` on the `√q`-premultiplied experience. -/
theorem exists_isERMSolution (data : TrainingExperience m n d)
    {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i) :
    ∃ G, IsERMSolution data q G :=
  let ⟨G, hG⟩ := exists_isELSolution (data.sqrtScale q)
  ⟨G, (isELSolution_sqrtScale_iff data hq G).mp hG⟩

end TrainingSubstrate

/-! ### Connection to `LinearDiscriminativeLexicon` -/

section Connection

variable {m n d : ℕ}

/-- A `LinearDiscriminativeLexicon`'s production map is the
    **trained** production map for given training data and
    frequency weights iff the production map is an ERM solution.

    The substrate is agnostic about which `q` is empirically
    correct; this predicate just records the relationship between
    a DLM's production map and a particular cognitive theory's
    training data. -/
def LinearDiscriminativeLexicon.IsTrainedOn
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (data : TrainingExperience m n d) (q : FrequencyVector m) : Prop :=
  IsERMSolution data q D.production

/-- A DLM is **EL-trained** for given data iff its production map is
    the type-uniform ERM solution. -/
abbrev LinearDiscriminativeLexicon.IsELTrainedOn
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (data : TrainingExperience m n d) : Prop :=
  D.IsTrainedOn data (uniformFrequency m)

/-- A DLM is **FIL-trained** with a given frequency vector iff its
    production map is the corresponding ERM solution. -/
abbrev LinearDiscriminativeLexicon.IsFILTrainedOn
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (data : TrainingExperience m n d) (q : FrequencyVector m) : Prop :=
  D.IsTrainedOn data q

variable {D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d)}
  {data : TrainingExperience m n d} {q : FrequencyVector m}

/-- A trained DLM's semantic support at a linearly decodable form coordinate
    equals the observed form value on every positively-weighted training
    event; any contrast carried by that coordinate — categorical or graded —
    transfers to `semSup` exactly. -/
theorem LinearDiscriminativeLexicon.IsTrainedOn.semSup_eq_of_decodable
    (hD : D.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {j₀ : Fin n} {w : MeaningVec d →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.meanings i) = data.forms i j₀) (i : Fin m) :
    semSup D (data.meanings i) j₀ = data.forms i j₀ :=
  IsERMSolution.coord_eq_of_decodable hq hD hw i

/-- Two DLMs trained on the same experience and weights have identical semantic
    support at every experienced meaning (`IsERMSolution.apply_meanings_eq`):
    `semSup` is a well-defined property of the training experience, not of the
    particular ERM solution. -/
theorem LinearDiscriminativeLexicon.IsTrainedOn.semSup_eq
    {D' : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d)}
    (hD : D.IsTrainedOn data q) (hD' : D'.IsTrainedOn data q)
    (hq : ∀ i, 0 < q i) (i : Fin m) (j : Fin n) :
    semSup D (data.meanings i) j = semSup D' (data.meanings i) j :=
  congrFun (IsERMSolution.apply_meanings_eq hq hD hD' i) j

/-- `semSup` is well-defined for **novel** meanings too, as long as they lie in
    the span of experienced ones — the model's analogical-generalization regime.
    Off the span, predictions are underdetermined
    (`IsERMSolution.exists_apply_ne`). -/
theorem LinearDiscriminativeLexicon.IsTrainedOn.semSup_eq_of_mem_span
    {D' : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d)}
    (hD : D.IsTrainedOn data q) (hD' : D'.IsTrainedOn data q)
    (hq : ∀ i, 0 < q i) {s : MeaningVec d}
    (hs : s ∈ Submodule.span ℝ (Set.range data.meanings)) (j : Fin n) :
    semSup D s j = semSup D' s j :=
  congrFun (IsERMSolution.apply_eq_of_mem_span hq hD hD' hs) j

/-- [heitmeier-chuang-baayen-2026]'s *Semantic Support for Form* — `semSupWord`
    over a word's cue coordinates — equals the sum of the observed form values
    whenever each coordinate is linearly decodable from the meanings. -/
theorem LinearDiscriminativeLexicon.IsTrainedOn.semSupWord_eq_of_decodable
    (hD : D.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {js : List (Fin n)}
    (hw : ∀ j ∈ js, ∃ w : MeaningVec d →ₗ[ℝ] ℝ,
      ∀ i, w (data.meanings i) = data.forms i j)
    (i : Fin m) :
    semSupWord D (data.meanings i) js = (js.map fun j => data.forms i j).sum := by
  unfold semSupWord
  congr 1
  refine List.map_congr_left fun j hj => ?_
  obtain ⟨w, hwj⟩ := hw j hj
  exact hD.semSup_eq_of_decodable hq hwj i

end Connection

end Processing.Lexical.Discriminative
