import Linglib.Core.Probability.Finite

/-!
# Probabilistic Conditional Semantics
[adams-1965] [jeffrey-edgington-1991] [douven-2008]
[kaufmann-2005] [kaufmann-2013] [pearl-2013]

The conditional `if φ then γ` as the **expected value of `γ` given `φ`**.

[adams-1965] proposes that the assertability of an indicative
conditional `if φ then ψ` equals the conditional probability
`P(ψ ∣ φ)`. [jeffrey-edgington-1991] push this further: the
conditional *denotation* is `P(ψ ∣ φ)`. [douven-2008] provides
the evidential support theory variant; [kaufmann-2005] [kaufmann-2013] extend to causal premise semantics; [pearl-2013]
develops the structural-counterfactual face.

[chung-mascarenhas-2024] eq. 44 promotes the consequent from a
proposition to a **measure function** `γ : W → ℝ≥0∞`:

    ⟦if φ, γ⟧^w = E_w[γ ∣ φ]

When `γ` is the indicator of `ψ` this reduces to the
[adams-1965]/[jeffrey-edgington-1991] conditional
probability (`condIf_propositional`). When `γ` is the
count-of-relevant-propositions `μ_R(w) = |{r ∈ R ∣ r true at w}|`,
it yields C&M's "explanatory value" / "expected utility". One
operator, two flavors.

`condIf` is an `abbrev` for `PMF.condExpect`: the wrapping is for
linguistic naming only; the equality is definitional. The Lewis 1976
triviality results bear on identifying the conditional with a
*proposition* in some space; we are content to identify it with a
*number* (an expected value), so they do not bite.

## Out of scope

Counterfactual conditionals (intervention semantics [pearl-2013];
see `Core/Causal/SEM/Counterfactual.lean`) and the Stalnaker
selection-function tradition
(`Semantics/Conditionals/SelectionFunction.lean`) are formalized
elsewhere. Their relation to the probabilistic conditional is itself a
research question ([schulz-2011],
[ciardelli-zhang-champollion-2018]).
-/

namespace Semantics.Conditionals.Probabilistic

open PMF
open scoped ENNReal

variable {W : Type*} [Fintype W]

/-- [chung-mascarenhas-2024] compositional conditional:
`⟦if φ, γ⟧^w = E_w[γ ∣ φ]`. Definitionally `condExpect`. -/
noncomputable abbrev condIf (p : PMF W) (φ : Set W) (γ : W → ℝ≥0∞) : ℝ≥0∞ :=
  p.condExpect φ γ

/-- [adams-1965]: when the consequent is the indicator of `ψ`, the
conditional reduces to the conditional probability `P(ψ ∣ φ)`. -/
theorem condIf_propositional (p : PMF W) (φ ψ : Set W) :
    condIf p φ (ψ.indicator (fun _ => 1)) = p.condProbSet φ ψ :=
  p.condExpect_indicator φ ψ

end Semantics.Conditionals.Probabilistic
