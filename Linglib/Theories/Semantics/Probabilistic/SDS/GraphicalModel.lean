import Linglib.Theories.Semantics.Probabilistic.SDS.ConceptNode
import Linglib.Theories.Semantics.Probabilistic.SDS.ScenarioMix

/-!
# SDS graphical model: multi-node assembly

The directed graphical model of @cite{erk-herbelot-2024} §5.1, Figure 5
(bat-in-player) and Figure 6 (astronomer-married-star). An utterance with
multiple concept-nodes is modelled by:

1. A **scenario-mix latent** at the top (paper Figure 5 node 1) — a
   distribution over scenarios, sampled from a symmetric Dirichlet(α).
2. **Per-concept-node scenario variables** (Figure 5 nodes 2, 3, 4) —
   each independently sampled from the scenario-mix.
3. **Per-concept-node concept variables** (Figure 5 nodes 5, 8, 9) —
   each conditional on its scenario node AND its semantic role node,
   combined via Product of Experts (paper §5.1 p. 569 formula).
4. **Observation nodes** (Figure 5 nodes 10–14) — observed condition
   labels (the surface word forms in the DRS) that constrain which
   concepts are admissible at each node.

This file gives the typed assembly: a `GraphicalModel` carries the
utterance-independent ingredients (per-scenario distributions,
selectional preferences, α), and the per-utterance shape (number of
concept-nodes, their roles, observed-concept restrictions) is supplied
to `jointFactor`.

## Honest scope

We do not represent the simplex-valued scenario-mix node directly (no
continuous Dirichlet in mathlib — see `SDS/ScenarioMix.lean`'s "Honest
scope"). Instead we use the marginal likelihood of scenario assignments
under the symmetric Dirichlet(α) prior, which equals
`PolyaUrn.symmetric.seqProb (counts of scenarioAssign)` by D-M
conjugacy. This is enough for paper Tables 1–2 since those tables
report posteriors over concept assignments, not over the scenario
mixture itself.

## Generative story → joint factor

By the paper's generative process (§5.1 p. 567+, formal version p. 579):

```
P(s_1..s_n, c_1..c_n | roles_1..roles_n)
  ∝ seqProb_α(counts(s_1..s_n))                  -- D-M scenario likelihood
    × ∏_i  perScenario(s_i, c_i)                  -- scenario→concept
    × ∏_i  selectional(roles_i, c_i)              -- role→concept
```

The unnormalized joint at a specific assignment is `jointFactor` below.
Normalizing over all assignments consistent with observations gives the
joint posterior (in `SDS/JointPosterior.lean`, Phase 2 part B).
-/

namespace Semantics.Probabilistic.SDS

open scoped ENNReal
open ProbabilityTheory

/-- An SDS graphical model: utterance-independent ingredients. The
sentence-specific data (n nodes, their roles, observations) is supplied
to `jointFactor` and `jointPosterior` below. -/
structure GraphicalModel (Scenario Concept Role : Type) where
  /-- Per-scenario concept distribution `P(c | s)`. Same across nodes. -/
  perScenario : Scenario → PMF Concept
  /-- Per-role selectional preference `P(c | role)`. -/
  selectional : Role → PMF Concept
  /-- Dirichlet concentration α governing scenario-mix sparsity. -/
  alpha : ℝ
  /-- α must be strictly positive (Dirichlet hyperparameter requirement). -/
  alphaPos : 0 < alpha

namespace GraphicalModel

variable {Scenario Concept Role : Type}
  [Fintype Scenario] [DecidableEq Scenario] [Nonempty Scenario]

/-- Count of how many concept-nodes were assigned scenario `s` in the
assignment `sAssign`. -/
def counts {n : ℕ} (sAssign : Fin n → Scenario) (s : Scenario) : ℕ :=
  (Finset.univ.filter (sAssign · = s)).card

/-- The unnormalized joint factor at a specific
(scenarioAssignment, conceptAssignment) configuration given roles. By
the SDS generative process (paper §5.1 + appendix p. 579):

```
factor(s, c | roles) =
  seqProb_α(counts(s)) · ∏_i perScenario(s_i, c_i) · selectional(roles_i, c_i)
```

The seqProb factor is the marginal likelihood of the scenario assignment
under the symmetric Dirichlet(α) prior, by D-M conjugacy (the simplex
is integrated out). -/
noncomputable def jointFactor (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} (roles : Fin n → Role)
    (sAssign : Fin n → Scenario) (cAssign : Fin n → Concept) : ℝ≥0∞ :=
  ENNReal.ofReal ((PolyaUrn.symmetric (α := Scenario) m.alpha m.alphaPos).seqProb
                    (counts sAssign)) *
  ∏ i, m.perScenario (sAssign i) (cAssign i) *
       m.selectional (roles i) (cAssign i)

/-- An observation at a concept-node: the finite set of concepts admissible
under the observed condition label (e.g., observing the word "bat" admits
{bat-animal, bat-stick}; observing "player" admits {player}). -/
abbrev Observations (Concept : Type) (n : ℕ) := Fin n → Finset Concept

/-- A concept assignment is *consistent* with observations when each node's
assigned concept is in the admissible set. -/
def Consistent {n : ℕ} {Concept : Type} (cAssign : Fin n → Concept)
    (obs : Observations Concept n) : Prop :=
  ∀ i, cAssign i ∈ obs i

instance {n : ℕ} {Concept : Type} (cAssign : Fin n → Concept)
    (obs : Observations Concept n) [∀ i, Decidable (cAssign i ∈ obs i)] :
    Decidable (Consistent cAssign obs) :=
  Fintype.decidableForallFintype

/-- The unnormalized joint factor restricted to assignments consistent with
observations. Zero on inconsistent assignments. -/
noncomputable def jointFactorObs (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} [Fintype Concept] [DecidableEq Concept]
    (roles : Fin n → Role) (obs : Observations Concept n)
    (sAssign : Fin n → Scenario) (cAssign : Fin n → Concept) : ℝ≥0∞ :=
  if Consistent cAssign obs then jointFactor m roles sAssign cAssign else 0

/-- The joint factor is zero if any concept-node has zero per-scenario
probability — a single zero in the per-node product zeros the whole. The
discharge tool for proving "this configuration contributes nothing to
the posterior" inside paper-replication theorems. -/
theorem jointFactor_eq_zero_of_perScenario_zero
    (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} (roles : Fin n → Role)
    (sAssign : Fin n → Scenario) (cAssign : Fin n → Concept)
    {i : Fin n} (h : m.perScenario (sAssign i) (cAssign i) = 0) :
    m.jointFactor roles sAssign cAssign = 0 := by
  unfold jointFactor
  rw [Finset.prod_eq_zero (Finset.mem_univ i)]
  · simp
  · rw [h, zero_mul]

/-- The joint factor is zero if any concept-node has zero selectional
weight at its role. Companion to `jointFactor_eq_zero_of_perScenario_zero`. -/
theorem jointFactor_eq_zero_of_selectional_zero
    (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} (roles : Fin n → Role)
    (sAssign : Fin n → Scenario) (cAssign : Fin n → Concept)
    {i : Fin n} (h : m.selectional (roles i) (cAssign i) = 0) :
    m.jointFactor roles sAssign cAssign = 0 := by
  unfold jointFactor
  rw [Finset.prod_eq_zero (Finset.mem_univ i)]
  · simp
  · rw [h, mul_zero]

/-- Companion: `jointFactorObs` is zero on observation-inconsistent
assignments, by definition. Used explicitly (via `exact`) in h_supp
discharge; not `@[simp]` because the hypothesis-form would over-fire. -/
theorem jointFactorObs_eq_zero_of_inconsistent
    (m : GraphicalModel Scenario Concept Role)
    {n : ℕ} [Fintype Concept] [DecidableEq Concept]
    (roles : Fin n → Role) (obs : Observations Concept n)
    (sAssign : Fin n → Scenario) (cAssign : Fin n → Concept)
    (h : ¬ Consistent cAssign obs) :
    m.jointFactorObs roles obs sAssign cAssign = 0 := by
  simp only [jointFactorObs, h, if_false]

end GraphicalModel

end Semantics.Probabilistic.SDS
