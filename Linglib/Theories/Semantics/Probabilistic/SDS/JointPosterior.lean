import Linglib.Theories.Semantics.Probabilistic.SDS.GraphicalModel
import Linglib.Core.Probability.PMFPosterior

/-!
# Joint posterior for an SDS graphical model

Given an `SDS.GraphicalModel m`, an `n`-node sentence with roles
`roles : Fin n → Role`, and observations `obs : Fin n → Finset Concept`
(the admissible concept sets at each node), this file provides:

- `partitionFunction m roles obs` — the normalizing constant
  `Z = ∑_{(s, c)} jointFactorObs m roles obs s c`
- `jointPosterior m roles obs h` — the joint posterior PMF over
  `(scenarioAssign, conceptAssign)` consistent with observations,
  defined when `Z ≠ 0` (at least one consistent assignment has
  nonzero unnormalized factor)
- `conceptPosteriorAt m roles obs target h c` — the marginal posterior
  probability that the target concept-node has value `c`, integrating
  over all other nodes' scenario+concept assignments

## Closed form

By the SDS generative process, the joint factor at a configuration is
product-form:

```
factor(s, c | roles, obs) =
  [c is consistent with obs] · seqProb_α(counts(s)) ·
  ∏_i perScenario(s_i, c_i) · ∏_i selectional(roles_i, c_i)
```

The joint posterior normalizes this over all consistent configurations.
The marginal at a target node is the natural sum:

```
P(c_target = c | obs) ∝
  ∑_{s, c' with c'_target = c, c' consistent with obs} factor(s, c' | roles, obs)
```

This is closed-form computable for finite Scenario, Concept, n. Phase 3
will instantiate it for the bat-in-player and astronomer-married-star
sentences and compute the Table-1/Table-2 numbers as concrete corollaries.

## Honest scope

The closed form sums over `Scenario^n × Concept^n`, which is
exponential in `n`. For the small n in paper Tables 1–2 (3-4 nodes),
this is tractable. For longer sentences, mathlib's `tsum`/`Finset.sum`
machinery handles the abstraction; concrete computation would need
either MCMC (out of scope) or aggressive structural simplification.
-/

namespace Semantics.Probabilistic.SDS

open scoped ENNReal
open ProbabilityTheory GraphicalModel

variable {Scenario Concept Role : Type}
  [Fintype Scenario] [DecidableEq Scenario] [Nonempty Scenario]
  [Fintype Concept] [DecidableEq Concept]

namespace GraphicalModel

/-- The partition function: total unnormalized mass over all
configurations consistent with observations. -/
noncomputable def partitionFunction (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} (roles : Fin n → Role) (obs : Observations Concept n) : ℝ≥0∞ :=
  ∑ sAssign : Fin n → Scenario, ∑ cAssign : Fin n → Concept,
    m.jointFactorObs roles obs sAssign cAssign

/-- The joint posterior over (scenarioAssign, conceptAssign) consistent
with observations, normalized by the partition function. Well-defined
when `partitionFunction m roles obs ≠ 0`. -/
noncomputable def jointPosterior (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} (roles : Fin n → Role) (obs : Observations Concept n)
    (sAssign : Fin n → Scenario) (cAssign : Fin n → Concept) : ℝ≥0∞ :=
  m.jointFactorObs roles obs sAssign cAssign / m.partitionFunction roles obs

@[simp]
theorem jointPosterior_eq_zero_of_inconsistent (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} (roles : Fin n → Role) (obs : Observations Concept n)
    (sAssign : Fin n → Scenario) (cAssign : Fin n → Concept)
    (h : ¬ Consistent cAssign obs) :
    m.jointPosterior roles obs sAssign cAssign = 0 := by
  simp only [jointPosterior, jointFactorObs, h, if_false, ENNReal.zero_div]

/-- The marginal posterior at a target concept-node: the probability
that the target node has value `c`, integrating over all other nodes'
scenario and concept assignments. -/
noncomputable def conceptPosteriorAt (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} (roles : Fin n → Role) (obs : Observations Concept n)
    (target : Fin n) (c : Concept) : ℝ≥0∞ :=
  ∑ sAssign : Fin n → Scenario, ∑ cAssign : Fin n → Concept,
    if cAssign target = c then m.jointPosterior roles obs sAssign cAssign else 0

/-- The marginal at a target node, broken into the sum-of-numerator over
the partition function. The natural form for explicit computation. -/
theorem conceptPosteriorAt_eq_unnormalized_sum_div_Z
    (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} (roles : Fin n → Role) (obs : Observations Concept n)
    (target : Fin n) (c : Concept) :
    m.conceptPosteriorAt roles obs target c =
      (∑ sAssign : Fin n → Scenario, ∑ cAssign : Fin n → Concept,
        if cAssign target = c then m.jointFactorObs roles obs sAssign cAssign else 0) /
      m.partitionFunction roles obs := by
  unfold conceptPosteriorAt jointPosterior
  -- Convert /Z to *Z⁻¹ throughout to use Finset.sum_mul (works in ENNReal).
  simp only [div_eq_mul_inv]
  -- Now: ∑ ∑ (if h then x * Z⁻¹ else 0) = (∑ ∑ if h then x else 0) * Z⁻¹
  -- Push * Z⁻¹ out of inner if:
  have rewrite_inner : ∀ (sA : Fin n → Scenario) (cA : Fin n → Concept),
      (if cA target = c then m.jointFactorObs roles obs sA cA * (m.partitionFunction roles obs)⁻¹
       else 0) =
      (if cA target = c then m.jointFactorObs roles obs sA cA else 0) *
        (m.partitionFunction roles obs)⁻¹ := by
    intros sA cA
    by_cases h : cA target = c
    · simp [h]
    · simp [h]
  simp_rw [rewrite_inner, ← Finset.sum_mul]

-- Support-enumeration: the discharge primitive for paper-replication theorems

/-- Enumerated-support partition function: when an explicit `Finset`
contains all configurations with non-zero `jointFactorObs`, the
partition function equals the sum over that `Finset`. The discharge
primitive that lets paper-replication study files skip the
8 ⋅ |Concept|^n direct enumeration. -/
theorem partitionFunction_eq_sum_of_support
    (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} (roles : Fin n → Role) (obs : Observations Concept n)
    (supp : Finset ((Fin n → Scenario) × (Fin n → Concept)))
    (h_supp : ∀ p, p ∉ supp → m.jointFactorObs roles obs p.1 p.2 = 0) :
    m.partitionFunction roles obs =
      ∑ p ∈ supp, m.jointFactorObs roles obs p.1 p.2 := by
  unfold partitionFunction
  rw [← Finset.sum_product', Finset.univ_product_univ]
  exact (Finset.sum_subset supp.subset_univ (fun p _ hp => h_supp p hp)).symm

/-- Enumerated-support marginal posterior: the analogous discharge
primitive for `conceptPosteriorAt`. The numerator and denominator both
reduce to sums over the explicit support. -/
theorem conceptPosteriorAt_eq_of_support
    (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} (roles : Fin n → Role) (obs : Observations Concept n)
    (target : Fin n) (c : Concept)
    (supp : Finset ((Fin n → Scenario) × (Fin n → Concept)))
    (h_supp : ∀ p, p ∉ supp → m.jointFactorObs roles obs p.1 p.2 = 0) :
    m.conceptPosteriorAt roles obs target c =
      (∑ p ∈ supp, if p.2 target = c then m.jointFactorObs roles obs p.1 p.2 else 0) /
      (∑ p ∈ supp, m.jointFactorObs roles obs p.1 p.2) := by
  rw [conceptPosteriorAt_eq_unnormalized_sum_div_Z]
  congr 1
  · -- Numerator: ∑ sA, ∑ cA, if cA target = c then jointFactorObs else 0
    rw [← Finset.sum_product', Finset.univ_product_univ]
    refine (Finset.sum_subset supp.subset_univ (fun p _ hp => ?_)).symm
    rw [h_supp p hp]
    simp
  · -- Denominator: same as partition function
    exact partitionFunction_eq_sum_of_support m roles obs supp h_supp

end GraphicalModel

end Semantics.Probabilistic.SDS
