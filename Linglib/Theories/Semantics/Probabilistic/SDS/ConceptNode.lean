import Linglib.Core.Probability.PMFPosterior
import Mathlib.Probability.Distributions.Uniform

/-!
# Concept node for SDS

A concept node in the SDS graphical model (@cite{erk-herbelot-2024}
Figure 5 nodes (5), (8), (9); paper §5.1). Each unary predicate in the
DRS pairs with a concept-node random variable whose value is a concept
drawn from a distribution determined by:

1. Its associated *scenario node* (provides `P(c | s)` — paper §5.1
   p. 569: scenario nodes "express their preferences through a
   multinomial distribution over concepts")
2. Its associated *semantic role node* (provides selectional preference
   `P(c | role)` — paper §5.1 p. 569: the role-conditional is "again a
   multinomial distribution over concepts")

The two are combined via Product of Experts at the concept node:
```
P(c | scenario, role) ∝ P(c | s) · P(c | role)
```

Both factors are PMFs (paper p. 569: "P(c | hold-theme) = 0 for c=hold;
0.125 else" — and 8 × 0.125 = 1.0 over the 8 concrete objects in the
inventory). PoE on two PMFs has bounded total mass (≤ 1), so the
finiteness hypothesis on `PMF.normalize` is automatic.

This file provides the typed primitives for those two contributions and
their PoE combination at a single concept node. The graphical-model
assembly (`SDS/GraphicalModel.lean`, Phase 2) composes these across all
concept nodes in a DRS.

## Cross-reference: legacy ℚ-valued selectional substrate

A parallel substrate at `Theories/Semantics/Verb/SelectionalPreferences.lean`
uses `Concept → ℚ` (Resnik 1996 + Erk 2007 + Erk-Herbelot 2024). Its
`RoleWithConstraint Concept` is the ℚ analogue of `SelectionalDist Role
Concept` here. Full unification (promoting the legacy file to ℝ≥0∞ + PMF)
is a separate project. Prefer this PMF version for new SDS work.

## Design choice: `α → PMF β`, not `Kernel α β`

We work at the PMF level (not mathlib's measure-theoretic `Kernel`) because
all our spaces are finite, composition via `PMF.bind` is enough for
`SDS/GraphicalModel.lean`, and avoiding `[MeasurableSpace]` keeps
signatures clean. Lifting to `Kernel` is only needed if downstream work
requires disintegration/Radon-Nikodym lemmas.
-/

namespace Semantics.Probabilistic.SDS.ConceptNode

open scoped ENNReal
open Semantics.Probabilistic.SDS

variable {Scenario Concept Role : Type}

/-- Per-scenario concept distribution: `P(c | s)`. The scenario contribution
to the concept node, paper §5.1 p. 569 ("scenario nodes express their
preferences through a multinomial distribution over concepts"). -/
abbrev PerScenarioDist (Scenario Concept : Type) := Scenario → PMF Concept

/-- Per-role selectional preference: `P(c | role)`. The role contribution
to the concept node, paper §5.1 p. 569: the role-conditional "is again
associated with a selectional constraint, which is expressed as a
multinomial distribution over concepts." Paper-faithful: PMF, not an
unnormalized weight (paper's `P(c | hold-theme) = 0.125` ×8 = 1.0 over
the 8 holdable concrete objects). -/
abbrev SelectionalDist (Role Concept : Type) := Role → PMF Concept

/-- The conditional concept distribution at a node, given a fixed scenario
and a fixed role. Combines the per-scenario distribution with the role's
selectional preference via Product of Experts (paper §5.1 p. 569
formula: `P(c | s, r) ∝ P(c | s) · P(c | r)`).

Hypothesis: at least one concept must have non-zero mass under both
factors (paper @cite{erk-herbelot-2024} fn 10). The finiteness of the
sum is automatic: both factors are PMFs, so `∑ p · q ≤ ∑ p = 1`. -/
noncomputable def conditionalAt
    (perScenario : PerScenarioDist Scenario Concept)
    (sel : SelectionalDist Role Concept)
    (s : Scenario) (r : Role)
    (h_pos : (∑' c, perScenario s c * sel r c) ≠ 0) : PMF Concept :=
  (perScenario s).productOfExperts (sel r) h_pos

@[simp]
theorem conditionalAt_apply
    (perScenario : PerScenarioDist Scenario Concept)
    (sel : SelectionalDist Role Concept)
    (s : Scenario) (r : Role)
    (h_pos : (∑' c, perScenario s c * sel r c) ≠ 0) (c : Concept) :
    conditionalAt perScenario sel s r h_pos c =
      perScenario s c * sel r c * (∑' x, perScenario s x * sel r x)⁻¹ :=
  PMF.productOfExperts_apply _ _ _ _

/-- The conditional kernel produces a PMF only when the per-scenario and
selectional distributions agree on at least one concept (paper fn 10).
Returns an `Option`: `none` is the pathological "no agreement" case. -/
noncomputable def conditionalKernel
    (perScenario : PerScenarioDist Scenario Concept)
    (sel : SelectionalDist Role Concept)
    (s : Scenario) (r : Role) : Option (PMF Concept) :=
  if h : (∑' c, perScenario s c * sel r c) ≠ 0 then
    some (conditionalAt perScenario sel s r h)
  else none

/-- The PoE support is the intersection of the per-scenario and selectional
supports (paper @cite{erk-herbelot-2024} fn 10's caveat made formal). -/
theorem mem_support_conditionalAt_iff
    (perScenario : PerScenarioDist Scenario Concept)
    (sel : SelectionalDist Role Concept)
    (s : Scenario) (r : Role)
    (h_pos : (∑' c, perScenario s c * sel r c) ≠ 0) (c : Concept) :
    c ∈ (conditionalAt perScenario sel s r h_pos).support ↔
      perScenario s c ≠ 0 ∧ sel r c ≠ 0 :=
  PMF.mem_support_productOfExperts_iff _ _ _ _

/-- PoE-with-self identity: when the selectional preference equals the
per-scenario distribution, the conditional is `perScenario s` weighted
by itself (`sq`-and-renormalize). A useful sanity check on the PoE
combinator behavior. -/
theorem conditionalAt_self
    (perScenario : PerScenarioDist Scenario Concept)
    (sel : SelectionalDist Role Concept)
    (s : Scenario) (r : Role)
    (h_pos : (∑' c, perScenario s c * sel r c) ≠ 0)
    (h_eq : sel r = perScenario s) (c : Concept) :
    conditionalAt perScenario sel s r h_pos c =
      (perScenario s c)^2 * (∑' x, (perScenario s x)^2)⁻¹ := by
  simp only [conditionalAt_apply, h_eq, sq]

/-- The genuine paper §4 reduction: when the per-scenario distribution
is *uniform* over the concept space — equivalently, when the model has
no scenario contribution at the concept node (paper §4 = "selectional
constraints only," no scenario-mix node) — the conditional reduces to
the selectional PMF unchanged. The PoE with uniform is the identity (up
to renormalization, which is also trivial since selectional already
sums to 1). -/
theorem conditionalAt_perScenario_uniform [Fintype Concept] [Nonempty Concept]
    (perScenario : PerScenarioDist Scenario Concept)
    (sel : SelectionalDist Role Concept) (s : Scenario) (r : Role)
    (h_uniform : perScenario s = PMF.uniformOfFintype Concept)
    (h_pos : (∑' c, perScenario s c * sel r c) ≠ 0) (c : Concept) :
    conditionalAt perScenario sel s r h_pos c = sel r c := by
  have hN_pos : (Fintype.card Concept : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp Fintype.card_pos
  have hN_fin : (Fintype.card Concept : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hNinv_pos : (Fintype.card Concept : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hN_fin
  have hNinv_fin : (Fintype.card Concept : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hN_pos
  simp only [conditionalAt_apply, h_uniform, PMF.uniformOfFintype_apply]
  rw [ENNReal.tsum_mul_left, (sel r).tsum_coe, mul_one]
  rw [mul_comm ((Fintype.card Concept : ℝ≥0∞)⁻¹) (sel r c), mul_assoc,
      ENNReal.mul_inv_cancel hNinv_pos hNinv_fin, mul_one]

end Semantics.Probabilistic.SDS.ConceptNode
