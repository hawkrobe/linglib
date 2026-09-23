/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Kernel.IonescuTulcea.PartialTraj
public import Linglib.Processing.Expectation.InformationValue

/-!
# Giulianelli, Wallbridge, Cotterell and Fernández (2026): Incremental Alternative Sampling as a Lens into the Temporal and Representational Resolution of Linguistic Prediction

This file formalizes the incremental alternative sampling (IAS) family of [giulianelli-etal-2026].
A language model is the family of next-unit kernels of an autoregressive process, and a
comprehender samples continuations of the context over a forecast horizon of `h` units, the
partial trajectory of the process (`Kernel.partialTraj`); the generalised surprisal of the next
unit is the substrate's `genSurprisal` at that kernel. Standard surprisal is the member with the
negative logarithm and the prefix indicator at every horizon, because the alternatives' first
unit is distributed as the model's next unit (`genSurprisal_prefixIndicator`); it thus evaluates
alternatives by lexical identity alone, and the discrete distance shows what this conflates,
since information value with it is the probability of error (`informationValue1_discrete`).
Incremental information value replaces the indicator by a representational distance between each
alternative and the observed unit followed by the alternatives sampled after it, the double
expectation of the paper's definition (`iiv`), whose horizon-one case is the information value of
the substrate (`iiv_zero`).

## Implementation notes

* Contexts are trajectories `Π i : Iic n, X i` of the process and alternatives are trajectories
  to time `n + h`, which carry the context as their prefix; a fixed alphabet is the constant
  family, and an end-of-string unit belongs to it, absorbing if the model makes it so.
* The alternative-set reformulation with mean, minimum and maximum summary statistics, and its
  reduction to the single-alternative definition under the mean, are not formalized; nor are the
  representation functions, which the paper takes from a Transformer's layers and which enter
  here only through the distance.
* The paper's regression results, which horizon and layer best predict cloze probability, the
  N400 and P600, and eye-tracked and self-paced reading times, are empirical fits and stay in
  prose: explicit predictability peaks at horizon one and lexical representations, the ERP
  components at horizon two, and self-paced reading of multi-sentence stimuli at longer horizons.

## References

* [giulianelli-etal-2026]
* [giulianelli-opedal-cotterell-2024]
* [levy-2008]
-/

@[expose] public section

open Finset InformationTheory MeasureTheory ProbabilityTheory Processing.PredictiveUncertainty

namespace GiulianelliEtAl2026

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSingletonClass (X n)]
  (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))) [∀ n, IsMarkovKernel (κ n)] {n h : ℕ}

/-- The context `x` followed by the unit `w`. -/
def snoc (x : Π i : Iic n, X i) (w : X (n + 1)) : Π i : Iic (n + 1), X i :=
  IicProdIoc n (n + 1) (x, MeasurableEquiv.piSingleton n w)

/-! ### Standard surprisal at every horizon -/

/-- The prefix indicator: one when the alternative's first unit is `w`. -/
noncomputable def prefixIndicator (w : X (n + 1)) (a : Π i : Iic (n + h + 1), X i) : ℝ :=
  ({w} : Set (X (n + 1))).indicator 1 (a ⟨n + 1, mem_Iic.2 (by omega)⟩)

/-- The expected prefix indicator is the next-unit probability, at every horizon. -/
theorem integral_prefixIndicator (x : Π i : Iic n, X i) (w : X (n + 1)) :
    ∫ a, prefixIndicator w a ∂(Kernel.partialTraj κ n (n + h + 1) x) = (κ n x).real {w} := by
  have hm : Measurable fun a : Π i : Iic (n + h + 1), X i => a ⟨n + 1, mem_Iic.2 (by omega)⟩ :=
    measurable_pi_apply _
  simp only [prefixIndicator]
  rw [← integral_map hm.aemeasurable
      (stronglyMeasurable_one.indicator (measurableSet_singleton w)).aestronglyMeasurable,
    ← Kernel.map_apply _ hm, Kernel.map_partialTraj_eval_succ (by omega),
    integral_indicator_one (measurableSet_singleton w)]

/-- Standard surprisal is the generalised surprisal with the negative logarithm and the prefix
indicator, at every horizon. -/
theorem genSurprisal_prefixIndicator (x : Π i : Iic n, X i) (w : X (n + 1)) :
    genSurprisal (Kernel.partialTraj κ n (n + h + 1)) (λ r => -Real.log r)
      (λ a w _ => prefixIndicator w a) x w = surprisal (κ n x) w := by
  simp only [genSurprisal]
  rw [integral_prefixIndicator]
  rfl

/-! ### What the indicator conflates -/

/-- The discrete distance on units: an alternative is accurate only when identical to the
unit. -/
noncomputable def discrete (a w : X (n + 1)) : ℝ := 1 - ({w} : Set (X (n + 1))).indicator 1 a

/-- Information value with the discrete distance is the probability of error, `1 − p(w | c)`: the
alternatives' similarity to the unit counts for nothing, as under surprisal. -/
theorem informationValue1_discrete (x : Π i : Iic n, X i) (w : X (n + 1)) :
    informationValue1 (κ n) discrete x w = 1 - (κ n x).real {w} := by
  simp only [informationValue1, discrete]
  rw [integral_sub (integrable_const _)
      ((integrable_const 1).indicator (measurableSet_singleton w)),
    integral_const, integral_indicator_one (measurableSet_singleton w)]
  simp

/-! ### Incremental information value -/

/-- Incremental information value at horizon `h + 1`: the expected representational distance
between an alternative sampled before the unit and the unit followed by the alternatives sampled
after it, the paper's double expectation. -/
noncomputable def iiv (d : (Π i : Iic (n + h + 1), X i) → (Π i : Iic (n + h + 1), X i) → ℝ)
    (x : Π i : Iic n, X i) (w : X (n + 1)) : ℝ :=
  ∫ a, ∫ a', d a a' ∂(Kernel.partialTraj κ (n + 1) (n + h + 1) (snoc x w))
    ∂(Kernel.partialTraj κ n (n + h + 1) x)

/-- At horizon one, incremental information value is the information value of the substrate,
with the distance read on the extended contexts. -/
theorem iiv_zero [∀ n, Countable (X n)]
    (d : (Π i : Iic (n + 1), X i) → (Π i : Iic (n + 1), X i) → ℝ) (x : Π i : Iic n, X i)
    (w : X (n + 1)) :
    iiv κ (h := 0) d x w = informationValue1 (κ n) (λ a w' => d (snoc x a) (snoc x w')) x w := by
  simp only [iiv, informationValue1, Nat.add_zero, Kernel.partialTraj_self, Kernel.id_apply,
    integral_dirac, Kernel.partialTraj_succ_self_apply]
  rw [integral_map (by fun_prop) (measurable_of_countable _).aestronglyMeasurable]
  rfl

end GiulianelliEtAl2026
