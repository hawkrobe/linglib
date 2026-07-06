import Linglib.Processing.Lexical.Discriminative.Defs
import Linglib.Processing.Lexical.Discriminative.Measures
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
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
  with `IsELSolution` the uniform special case.
* `TrainingExperience.sqrtScale`, `residualPairing`, `predictionEnergy`.

## Main results

* `isERMSolution_iff_rescaled`: only the empirical distribution of `q` matters.
* `isERMSolution_iff_coordResidual`: ERM is columnwise-unbeatable regression.
* `isELSolution_sqrtScale_iff`: FIL under `q` is EL on the `√q`-premultiplied
  experience ([heitmeier-2024]'s FIL-EL equivalence, also
  [heitmeier-chuang-axen-baayen-2024]; invertibility-free).
* `isERMSolution_iff_residualPairing_eq_zero`: the normal equations
  `SᵀQ(SG − C) = 0` as an invertibility-free iff.
* `IsERMSolution.apply_eq_of_mem_span` / `exists_apply_ne`: fitted values are
  unique exactly on the span of experienced meanings.

Existence of ERM solutions is in `Existence.lean`, via the least-squares
keystone `Core.IsLeastSquares`. The endstate theory is rule-agnostic: composing
`isERMSolution_iff_forall_column` with the orthogonality principle
`Core.sum_whCorrection_eq_zero_iff` identifies the ERM set with the
equilibria of any error-driven rule in the Widrow-Hoff family.

## TODO

Closed form `G = (SᵀS)⁻¹SᵀC` under full column rank; approximate-decodability
gap bounds for `semSup`.
-/

namespace Processing.Lexical.Discriminative

noncomputable section TrainingSubstrate

variable {m n d : ℕ}

/-! ### Substrate types -/

/-- A **training experience** is a finite indexed family of (meaning, form)
    observation pairs — the rows of the papers' `S` and `C` matrices. -/
structure TrainingExperience (numEvents formDim meaningDim : ℕ) where
  meanings : Fin numEvents → MeaningVec meaningDim
  forms    : Fin numEvents → FormVec formDim

/-- A **frequency vector** assigns one weight to each usage event — the
    diagonal of the papers' `Q` ([gahl-baayen-2024] appendix). The choice of
    `q` is the cognitive commitment: uniform weights give EL and token counts
    give FIL (log-transforms distort learning per [gahl-baayen-2024]).
    Nonnegativity is a per-theorem hypothesis. -/
abbrev FrequencyVector (numEvents : ℕ) : Type := Fin numEvents → ℝ

/-- The constant-1 frequency vector counts every event once (endstate
    learning). -/
def uniformFrequency (m : ℕ) : FrequencyVector m := fun _ => 1

variable (data : TrainingExperience m n d) (q : FrequencyVector m)
  (G : MeaningVec d →ₗ[ℝ] FormVec n)

/-- The sum of all event weights. -/
def FrequencyVector.totalMass : ℝ := ∑ i, q i

/-- `q.normalize` rescales `q` to sum to 1, giving the empirical
    distribution over events. For the `PMF` cast use `PMF.ofRealWeightFn`. -/
def FrequencyVector.normalize : FrequencyVector m := fun i => q i / q.totalMass

@[simp] theorem FrequencyVector.normalize_apply (i : Fin m) :
    q.normalize i = q i / q.totalMass := rfl

/-! ### The weighted loss -/

/-- Squared coordinate-distance `Σⱼ (a j − b j)²` between two form vectors. -/
def squaredDist (a b : FormVec n) : ℝ := ∑ j, (a j - b j) ^ 2

theorem squaredDist_self (a : FormVec n) : squaredDist a a = 0 :=
  Finset.sum_eq_zero fun _ _ => by rw [sub_self]; ring

theorem squaredDist_nonneg (a b : FormVec n) : 0 ≤ squaredDist a b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The **frequency-weighted training loss**
    `Σᵢ qᵢ · squaredDist (G (meanings i)) (forms i)`. This is the variational
    characterisation of the papers' procedural `√Q` normal-equations
    specification ([gahl-baayen-2024] appendix; see `weightedLoss_sqrtScale`). -/
def weightedLoss : ℝ := ∑ i, q i * squaredDist (G (data.meanings i)) (data.forms i)

theorem weightedLoss_nonneg (hq : ∀ i, 0 ≤ q i) :
    0 ≤ weightedLoss data q G :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hq k) (squaredDist_nonneg _ _)

/-! ### Solution Props: ERM and EL -/

/-- `G` is an **empirical risk minimiser** (ERM) for `data` under `q` if
    no linear map achieves a smaller weighted loss. -/
def IsERMSolution : Prop :=
  ∀ G' : MeaningVec d →ₗ[ℝ] FormVec n,
    weightedLoss data q G ≤ weightedLoss data q G'

/-- An **endstate-learning** (EL) solution is an ERM solution under uniform
    weights ([gahl-baayen-2024] appendix). -/
abbrev IsELSolution : Prop :=
  IsERMSolution data (uniformFrequency m) G

/-! ### Structural theorems -/

/-- The weighted loss is linear in the frequency vector. -/
theorem weightedLoss_smul_frequency (c : ℝ) :
    weightedLoss data (c • q) G = c * weightedLoss data q G := by
  simp [weightedLoss, Finset.mul_sum, mul_assoc]

/-- ERM solutions are invariant under positive rescaling
    of the frequency vector — only relative frequencies matter. -/
theorem isERMSolution_iff_rescaled {c : ℝ} (hc : 0 < c) :
    IsERMSolution data (c • q) G ↔ IsERMSolution data q G := by
  simp only [IsERMSolution, weightedLoss_smul_frequency, mul_le_mul_iff_right₀ hc]

/-! ### Per-coordinate residual optimality

The loss separates across form coordinates — each column of `G` regresses one
cue's support on the semantic dimensions, "optimal in the least-squares sense"
([heitmeier-chuang-baayen-2026] ch. 6) — so ERM is exactly columnwise
unbeatability. -/

/-- Weighted squared residual of a predicted column `pred` against
    form coordinate `j₀` of the training data. -/
def coordResidual (pred : Fin m → ℝ) (j₀ : Fin n) : ℝ := ∑ k, q k * (pred k - data.forms k j₀) ^ 2

theorem coordResidual_nonneg (hq : ∀ i, 0 ≤ q i) (pred : Fin m → ℝ)
    (j₀ : Fin n) : 0 ≤ coordResidual data q pred j₀ :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hq k) (sq_nonneg _)

/-- The weighted loss is the sum over form coordinates of the per-coordinate
    residuals — each column of the production map is an independent
    regression. -/
theorem weightedLoss_eq_sum_coordResidual :
    weightedLoss data q G
      = ∑ j, coordResidual data q (fun k => G (data.meanings k) j) j := by
  unfold weightedLoss squaredDist coordResidual
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- Minimising a separable finite sum over a product is exactly minimising
    each coordinate. `[UPSTREAM]` candidate. -/
private theorem sum_min_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} (g : ∀ i, β i → ℝ) (x : ∀ i, β i) :
    (∀ y : ∀ i, β i, ∑ i, g i (x i) ≤ ∑ i, g i (y i)) ↔
      ∀ i, ∀ b : β i, g i (x i) ≤ g i b := by
  refine ⟨fun h i b => ?_, fun h y => Finset.sum_le_sum fun i _ => h i (y i)⟩
  have hy := h (Function.update x i b)
  simp_rw [Function.apply_update (fun j => g j) x i b] at hy
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
      ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
      Finset.erase_eq] at hy
  linarith

/-- `G` is an ERM solution iff at every form coordinate its column's residual
    is at most that of any linear functional of the meanings — ERM is
    columnwise-unbeatable regression. No sign condition on `q`. -/
theorem isERMSolution_iff_coordResidual :
    IsERMSolution data q G ↔
      ∀ (j₀ : Fin n) (w : MeaningVec d →ₗ[ℝ] ℝ),
        coordResidual data q (fun k => G (data.meanings k) j₀) j₀
          ≤ coordResidual data q (fun k => w (data.meanings k)) j₀ := by
  constructor
  · intro hG
    refine (sum_min_iff (fun j (w : MeaningVec d →ₗ[ℝ] ℝ) =>
        coordResidual data q (fun k => w (data.meanings k)) j)
        (fun j => (LinearMap.proj j).comp G)).mp fun y => ?_
    have h := hG (LinearMap.pi y)
    rwa [weightedLoss_eq_sum_coordResidual, weightedLoss_eq_sum_coordResidual] at h
  · intro h G'
    rw [weightedLoss_eq_sum_coordResidual data q G,
      weightedLoss_eq_sum_coordResidual data q G']
    exact Finset.sum_le_sum fun j _ => h j ((LinearMap.proj j).comp G')

/-! ### Rescaling invariance

The "frequency-vector-as-counts" view (DLM-paper-faithful) and the
"frequency-vector-as-empirical-distribution" view (Bayesian-tradition) make
identical predictions about which production maps are ERM-optimal. For the
`PMF (Fin m)` cast of `q.normalize`, call `PMF.ofRealWeightFn` from
`Core.Probability.Constructions` directly. -/

/-- A frequency vector and its empirical distribution agree on which
    production maps are ERM solutions. -/
theorem isERMSolution_normalize_iff (h : 0 < q.totalMass) :
    IsERMSolution data q.normalize G ↔ IsERMSolution data q G := by
  have hinv : (0:ℝ) < (q.totalMass)⁻¹ := inv_pos.mpr h
  have hnorm : q.normalize = (q.totalMass)⁻¹ • q := by
    funext i
    show q i / q.totalMass = (q.totalMass)⁻¹ * q i
    rw [div_eq_inv_mul]
  rw [hnorm]
  exact isERMSolution_iff_rescaled data q G hinv

/-! ### √Q transport

[gahl-baayen-2024]'s appendix computes EL from the normal equations of
regression and FIL by solving the EL problem on `√Q`-premultiplied `S` and
`C` matrices; [heitmeier-chuang-baayen-2026] gives the same construction, and
[heitmeier-2024] proves the equivalence with frequency-replicated training
data via the closed-form normal-equations solution, under invertibility.
Here the premultiplied experience is `TrainingExperience.sqrtScale` and the
equivalence (`isELSolution_sqrtScale_iff`) is stated invertibility-free at
the level of ERM solution sets. (`Existence.lean` applies the same `√q`
scaling inside its design map.) -/

/-- The `√q`-premultiplied training experience scales event `i` by `√(q i)`
    in both meaning and form — the `√Q`-premultiplication of `S` and `C` of
    [gahl-baayen-2024]'s appendix and [heitmeier-chuang-baayen-2026]. -/
def TrainingExperience.sqrtScale : TrainingExperience m n d where
  meanings i := Real.sqrt (q i) • data.meanings i
  forms i := Real.sqrt (q i) • data.forms i

theorem squaredDist_smul (c : ℝ) (a b : FormVec n) :
    squaredDist (c • a) (c • b) = c ^ 2 * squaredDist a b := by
  unfold squaredDist
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [Pi.smul_apply, smul_eq_mul]; ring

/-! ### Normal equations: ERM ⟺ residual orthogonality

[gahl-baayen-2024]'s appendix and [heitmeier-2024] compute the mappings from
the normal equations of regression (`SᵀQ(SG − C) = 0` premultiplied into closed
form under invertibility). Stated invertibility-free: `G` is an ERM solution
iff every residual-prediction pairing vanishes — the first-order condition of
the quadratic loss. Fitted values on experienced meanings are therefore unique
across ERM solutions, which is what makes the model's predictions (and the
`semSup` measures) well-defined properties of the training experience. -/

/-- The `q`-weighted pairing `∑ᵢ qᵢ ⟨G(sᵢ) − cᵢ, H(sᵢ)⟩` of `G`'s residuals
    with `H`'s predictions. The normal equations say this vanishes for every
    `H` exactly at the ERM solutions. -/
def residualPairing (H : MeaningVec d →ₗ[ℝ] FormVec n) : ℝ :=
  ∑ i, q i * ∑ j, (G (data.meanings i) j - data.forms i j) * H (data.meanings i) j

/-- The `q`-weighted squared magnitude of `H`'s predictions on the
    training meanings. -/
def predictionEnergy (H : MeaningVec d →ₗ[ℝ] FormVec n) : ℝ :=
  ∑ i, q i * ∑ j, H (data.meanings i) j ^ 2

theorem predictionEnergy_nonneg (hq : ∀ i, 0 ≤ q i)
    (H : MeaningVec d →ₗ[ℝ] FormVec n) : 0 ≤ predictionEnergy data q H :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg (hq i) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem residualPairing_smul (t : ℝ) (H : MeaningVec d →ₗ[ℝ] FormVec n) :
    residualPairing data q G (t • H) = t * residualPairing data q G H := by
  unfold residualPairing
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem predictionEnergy_smul (t : ℝ) (H : MeaningVec d →ₗ[ℝ] FormVec n) :
    predictionEnergy data q (t • H) = t ^ 2 * predictionEnergy data q H := by
  unfold predictionEnergy
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Perturbing the weighted loss around `G` by `H` adds twice the residual
    pairing plus the energy of the perturbation. -/
theorem weightedLoss_add (H : MeaningVec d →ₗ[ℝ] FormVec n) :
    weightedLoss data q (G + H)
      = weightedLoss data q G + 2 * residualPairing data q G H
        + predictionEnergy data q H := by
  unfold weightedLoss residualPairing predictionEnergy squaredDist
  simp only [LinearMap.add_apply, Pi.add_apply, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

variable {data q G}

/-! ### ERM characterisations, uniqueness, and transport -/

/-- If some linear functional `w` of the meanings exactly reproduces
    coordinate `j₀` of the observed forms, then any ERM solution under
    positive weights also reproduces it exactly on the training events. -/
theorem IsERMSolution.coord_eq_of_decodable (hq : ∀ i, 0 < q i)
    (hG : IsERMSolution data q G)
    {j₀ : Fin n} {w : MeaningVec d →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.meanings i) = data.forms i j₀) (i : Fin m) :
    G (data.meanings i) j₀ = data.forms i j₀ := by
  have hB : coordResidual data q (fun k => w (data.meanings k)) j₀ = 0 := by
    simp [coordResidual, hw]
  have h0 : coordResidual data q (fun k => G (data.meanings k) j₀) j₀ = 0 :=
    le_antisymm (hB ▸ (isERMSolution_iff_coordResidual data q G).1 hG j₀ w)
      (coordResidual_nonneg data q (fun k => (hq k).le) _ _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    fun k _ => mul_nonneg (hq k).le (sq_nonneg _)).1 h0 i (Finset.mem_univ i)
  exact sub_eq_zero.1 (sq_eq_zero_iff.1
    ((mul_eq_zero.1 hterm).resolve_left (hq i).ne'))

/-- A map that reproduces every training form exactly is an ERM solution
    under any nonnegative weights — `IsERMSolution` is nonvacuous whenever
    the data are linearly interpolable. -/
theorem isERMSolution_of_interpolates (hq : ∀ i, 0 ≤ q i)
    (hG : ∀ i, G (data.meanings i) = data.forms i) :
    IsERMSolution data q G := fun G' => by
  have h0 : weightedLoss data q G = 0 := by simp [weightedLoss, hG, squaredDist_self]
  exact h0 ▸ weightedLoss_nonneg data q G' hq

/-- `G` is an ERM solution iff every residual-prediction pairing vanishes.
    This is the first-order condition of the quadratic loss, with no
    invertibility hypothesis. -/
theorem isERMSolution_iff_residualPairing_eq_zero (hq : ∀ i, 0 ≤ q i) :
    IsERMSolution data q G ↔
      ∀ H : MeaningVec d →ₗ[ℝ] FormVec n, residualPairing data q G H = 0 := by
  constructor
  · intro hG H
    -- along direction `H` the loss is a nonnegative quadratic in `t`,
    -- so its discriminant is nonpositive
    have key : ∀ t : ℝ, 0 ≤ predictionEnergy data q H * (t * t)
        + 2 * residualPairing data q G H * t + 0 := fun t => by
      have h := hG (G + t • H)
      rw [weightedLoss_add, residualPairing_smul, predictionEnergy_smul] at h
      nlinarith [h]
    have hd := discrim_le_zero key
    simp only [discrim] at hd
    exact sq_eq_zero_iff.mp (le_antisymm (by nlinarith [hd]) (sq_nonneg _))
  · intro h G'
    have hexp := weightedLoss_add data q G (G' - G)
    rw [show G + (G' - G) = G' by abel, h (G' - G)] at hexp
    linarith [predictionEnergy_nonneg data q hq (G' - G)]

/-- In the papers' columnwise form of the normal equations, `G` is an ERM
    solution iff at every form coordinate the `q`-weighted residual column is
    orthogonal to every linear functional of the meanings. Quantifying over
    functionals is `SᵀQ(SG − C) = 0` with `Sᵀ`'s rows generalized to the full
    dual space. -/
theorem isERMSolution_iff_forall_column (hq : ∀ i, 0 ≤ q i) :
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

/-- Under positive weights the prediction energy is definite: it vanishes iff
    the predictions vanish on every training meaning. -/
theorem predictionEnergy_eq_zero_iff (hq : ∀ i, 0 < q i)
    {H : MeaningVec d →ₗ[ℝ] FormVec n} :
    predictionEnergy data q H = 0 ↔ ∀ i, H (data.meanings i) = 0 := by
  constructor
  · intro hE i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (hq k).le (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp
      hE i (Finset.mem_univ i)
    have hsum := (mul_eq_zero.mp hi).resolve_left (hq i).ne'
    funext j
    exact sq_eq_zero_iff.mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).mp hsum j
        (Finset.mem_univ j))
  · intro h
    simp [predictionEnergy, h]

/-- All ERM solutions under positive weights produce the same predicted form
    for every experienced meaning — fitted values are unique even when the
    ERM map is not. -/
theorem IsERMSolution.apply_meanings_eq (hq : ∀ i, 0 < q i)
    {G' : MeaningVec d →ₗ[ℝ] FormVec n}
    (hG : IsERMSolution data q G) (hG' : IsERMSolution data q G') (i : Fin m) :
    G (data.meanings i) = G' (data.meanings i) := by
  have hexp := weightedLoss_add data q G (G' - G)
  rw [show G + (G' - G) = G' by abel,
      (isERMSolution_iff_residualPairing_eq_zero fun k => (hq k).le).mp
        hG (G' - G)] at hexp
  have hE : predictionEnergy data q (G' - G) = 0 := by linarith [hG G', hG' G]
  have h0 : G' (data.meanings i) = G (data.meanings i) := by
    simpa [sub_eq_zero] using (predictionEnergy_eq_zero_iff hq).mp hE i
  exact h0.symm

/-- ERM solutions agree at every meaning in the **span** of the experienced
    ones. Together with
    `IsERMSolution.exists_apply_ne`, novel-item predictions are well-defined
    exactly on the span of experience — the model generalizes by linear
    combination of experienced meanings and is unconstrained beyond them. -/
theorem IsERMSolution.apply_eq_of_mem_span (hq : ∀ i, 0 < q i)
    {G' : MeaningVec d →ₗ[ℝ] FormVec n}
    (hG : IsERMSolution data q G) (hG' : IsERMSolution data q G')
    {s : MeaningVec d} (hs : s ∈ Submodule.span ℝ (Set.range data.meanings)) :
    G s = G' s := by
  have hker : Submodule.span ℝ (Set.range data.meanings)
      ≤ LinearMap.ker (G' - G) :=
    Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun i => by
      simp [LinearMap.mem_ker,
            (IsERMSolution.apply_meanings_eq hq hG hG' i).symm]
  have h0 : G' s = G s := by
    simpa [LinearMap.mem_ker, sub_eq_zero] using hker hs
  exact h0.symm

/-- Adding a map that vanishes on every training meaning preserves ERM: the
    ERM solutions are closed under the data-annihilating directions (and by
    `IsERMSolution.apply_meanings_eq` they form exactly such a coset). -/
theorem IsERMSolution.add_of_forall_eq_zero (hG : IsERMSolution data q G)
    {H : MeaningVec d →ₗ[ℝ] FormVec n} (hH : ∀ i, H (data.meanings i) = 0) :
    IsERMSolution data q (G + H) := fun G' => by
  have h0 : weightedLoss data q (G + H) = weightedLoss data q G := by
    rw [weightedLoss_add]
    simp [residualPairing, predictionEnergy, hH]
  exact h0 ▸ hG G'

/-- Off the span of experienced meanings, ERM solutions are genuinely
    underdetermined — any ERM solution can be modified into another with a
    different prediction at any unexperienced meaning direction, by adding a
    correction supported on the annihilator of the span. -/
theorem IsERMSolution.exists_apply_ne [NeZero n]
    (hG : IsERMSolution data q G)
    {s : MeaningVec d} (hs : s ∉ Submodule.span ℝ (Set.range data.meanings)) :
    ∃ G' : MeaningVec d →ₗ[ℝ] FormVec n,
      IsERMSolution data q G' ∧ G s ≠ G' s := by
  obtain ⟨φ, hφ, hφs⟩ : ∃ φ ∈ (Submodule.span ℝ
      (Set.range data.meanings)).dualAnnihilator, φ s ≠ 0 := by
    have h := mt (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ s).mp hs
    push Not at h
    exact h
  refine ⟨G + φ.smulRight (Pi.single 0 1),
    hG.add_of_forall_eq_zero fun i => by
      simp [(Submodule.mem_dualAnnihilator φ).mp hφ _
        (Submodule.subset_span (Set.mem_range_self i))],
    fun h => ?_⟩
  have h0 := congrFun h (0 : Fin n)
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply, Pi.add_apply,
             Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h0
  exact hφs (by linarith)

/-- The uniform-weight loss on the `√q`-premultiplied experience is the
    `q`-weighted loss on the original. -/
theorem weightedLoss_sqrtScale (hq : ∀ i, 0 ≤ q i) :
    weightedLoss (data.sqrtScale q) (uniformFrequency m) G
      = weightedLoss data q G := by
  simp [weightedLoss, TrainingExperience.sqrtScale, uniformFrequency,
        map_smul, squaredDist_smul, Real.sq_sqrt, hq]

/-- FIL under `q` is exactly EL on the `√q`-premultiplied experience —
    [heitmeier-2024]'s FIL-EL equivalence, invertibility-free. -/
theorem isELSolution_sqrtScale_iff (hq : ∀ i, 0 ≤ q i) :
    IsELSolution (data.sqrtScale q) G ↔ IsERMSolution data q G := by
  simp only [IsELSolution, IsERMSolution, weightedLoss_sqrtScale hq]



end TrainingSubstrate

/-! ### Connection to `LinearDiscriminativeLexicon` -/

namespace LinearDiscriminativeLexicon

variable {m n d : ℕ}
  (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
  (data : TrainingExperience m n d) (q : FrequencyVector m)

/-- `D` is **trained on** `data` under weights `q` if its production map is
    an ERM solution. -/
def IsTrainedOn : Prop := IsERMSolution data q D.production

/-- A DLM is **EL-trained** for given data iff its production map is
    the type-uniform ERM solution. -/
abbrev IsELTrainedOn : Prop := D.IsTrainedOn data (uniformFrequency m)

/-- A DLM is **FIL-trained** with a given frequency vector iff its
    production map is the corresponding ERM solution. -/
abbrev IsFILTrainedOn : Prop := D.IsTrainedOn data q

variable {D data q}

/-- A trained DLM's semantic support at a linearly decodable form coordinate
    equals the observed form value on every positively-weighted training
    event; any contrast carried by that coordinate — categorical or graded —
    transfers to `semSup` exactly. -/
theorem IsTrainedOn.semSup_eq_of_decodable
    (hD : D.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {j₀ : Fin n} {w : MeaningVec d →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.meanings i) = data.forms i j₀) (i : Fin m) :
    semSup D (data.meanings i) j₀ = data.forms i j₀ :=
  IsERMSolution.coord_eq_of_decodable hq hD hw i

/-- Two DLMs trained on the same experience and weights have identical
    semantic support at every experienced meaning
    (`IsERMSolution.apply_meanings_eq`); `semSup` is thus a well-defined
    property of the training experience, not of the particular ERM solution. -/
theorem IsTrainedOn.semSup_eq
    {D' : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d)}
    (hD : D.IsTrainedOn data q) (hD' : D'.IsTrainedOn data q)
    (hq : ∀ i, 0 < q i) (i : Fin m) (j : Fin n) :
    semSup D (data.meanings i) j = semSup D' (data.meanings i) j :=
  congrFun (IsERMSolution.apply_meanings_eq hq hD hD' i) j

/-- `semSup` is well-defined for **novel** meanings too, as long as they lie
    in the span of experienced ones — the model generalizes by linear
    combination of experienced meanings. Off the span, predictions are
    underdetermined (`IsERMSolution.exists_apply_ne`). -/
theorem IsTrainedOn.semSup_eq_of_mem_span
    {D' : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d)}
    (hD : D.IsTrainedOn data q) (hD' : D'.IsTrainedOn data q)
    (hq : ∀ i, 0 < q i) {s : MeaningVec d}
    (hs : s ∈ Submodule.span ℝ (Set.range data.meanings)) (j : Fin n) :
    semSup D s j = semSup D' s j :=
  congrFun (IsERMSolution.apply_eq_of_mem_span hq hD hD' hs) j

/-- *Semantic Support for Form* ([gahl-baayen-2024] appendix;
    [heitmeier-chuang-baayen-2026]) — `semSupWord` over a word's cue
    coordinates — equals the sum of the observed form values whenever each
    coordinate is linearly decodable from the meanings. -/
theorem IsTrainedOn.semSupWord_eq_of_decodable
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

end LinearDiscriminativeLexicon

end Processing.Lexical.Discriminative
