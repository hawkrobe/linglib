import Linglib.Processing.Lexical.Discriminative.Training

/-!
# DLM ERM-invariance under positive rescaling
@cite{baayen-2019} @cite{gahl-baayen-2024}

Sibling to `Training.lean`. Two theorems making explicit that ERM
solutions for the DLM weighted loss are invariant under positive
rescaling of the frequency vector. The substrate operations
`FrequencyVector.totalMass` and `FrequencyVector.normalize` live in
`Training.lean` next to `FrequencyVector` itself; this file consumes
them to prove the invariance theorems.

## Why a separate file

These two theorems form the **bridge that lets cross-tradition
comparisons go through**: when comparing DLM predictions to Bayesian
word-learning posteriors over the same event inventory, the
"frequency-vector-as-counts" view (DLM-paper-faithful) and the
"frequency-vector-as-empirical-distribution" view (Bayesian-tradition)
make identical predictions about which `G : MeaningVec → FormVec` is
ERM-optimal.

The DLM literature (paper appendix §A1.3 of @cite{gahl-baayen-2024})
uses `Q` as a diagonal matrix of raw counts, not a normalised
distribution. Paper §6.4 explicitly cautions against reifying any
single mathematical representation. The rescaling-invariance theorems
make the equivalence formal.

## PMF view

To cast a `FrequencyVector m` into a mathlib `PMF (Fin m)` (e.g., for
KL-divergence or total-variation comparisons against probabilistic
models), call `PMF.ofRealWeightFn` from `Core.Probability.Constructions`
directly:

```
PMF.ofRealWeightFn q hq i₀ hq_pos_i₀
```

where `i₀ : Fin m` is some index with `hq_pos_i₀ : 0 < q i₀`. From a
positive-total hypothesis `htot : 0 < q.totalMass` together with `hq`
nonneg, extract a witness via the standard contrapositive:
```
have ⟨i₀, hq_pos_i₀⟩ : ∃ i, 0 < q i := by
  by_contra h_no
  push_neg at h_no
  have : ∑ i, q i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (h_no i) (hq i))
  exact absurd this (ne_of_gt htot)
```

There is no project-side `toEmpiricalPMF` wrapper — the inline
`PMF.ofRealWeightFn` call is the canonical entry point. (An earlier
`toEmpiricalPMF` reinvented `PMF.ofRealWeightFn`; removed 0.231.X.)
-/

namespace Processing.Lexical.Discriminative

noncomputable section RescalingInvariance

variable {m n d : ℕ}

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

end RescalingInvariance

end Processing.Lexical.Discriminative
