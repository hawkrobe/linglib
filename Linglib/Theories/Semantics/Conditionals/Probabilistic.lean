import Linglib.Core.Probability.Finite

/-!
# Probabilistic Conditional Semantics
@cite{adams-1965} @cite{jeffrey-edgington-1991} @cite{douven-2008}
@cite{kaufmann-2005} @cite{kaufmann-2013} @cite{pearl-2013}

The conditional `if φ then γ` as the **expected value of `γ` given `φ`**.

@cite{adams-1965} proposes that the assertability of an indicative
conditional `if φ then ψ` equals the conditional probability
`P(ψ ∣ φ)`. @cite{jeffrey-edgington-1991} push this further: the
conditional *denotation* is `P(ψ ∣ φ)`. @cite{douven-2008} provides
the evidential support theory variant; @cite{kaufmann-2005,
kaufmann-2013} extend to causal premise semantics; @cite{pearl-2013}
develops the structural-counterfactual face.

@cite{chung-mascarenhas-2024} eq. 44 promotes the consequent from a
proposition to a **measure function** `γ : W → ℝ≥0∞`:

    ⟦if φ, γ⟧^w = E_w[γ ∣ φ]

When `γ` is the indicator of `ψ` this reduces to the
@cite{adams-1965}/@cite{jeffrey-edgington-1991} conditional
probability. When `γ` is the count-of-relevant-propositions
`μ_R(w) = |{r ∈ R ∣ r true at w}|`, it yields C&M's "explanatory
value" / "expected utility". One operator, two flavors.

This file is a paper-thin naming wrapper around
`PMF.condExpect` (`Core.Probability.Finite`). The Lewis 1976 triviality
results are not addressed here: they bear on identifying the
conditional with a *proposition* in some space; we are content to
identify the conditional with a *number* (an expected value).

## Out of scope

Counterfactual conditionals (which require an intervention semantics
@cite{pearl-2013}; see `Core/Causal/SEM/Counterfactual.lean`) and the
Stalnaker selection-function tradition (see
`Theories/Semantics/Conditionals/SelectionFunction.lean`) are formalized
elsewhere. Their relation to the probabilistic conditional is itself
a research question (see @cite{schulz-2011}, @cite{ciardelli-zhang-champollion-2018}).
-/

set_option autoImplicit false

namespace Semantics.Conditionals.Probabilistic

open PMF

variable {W : Type*} [Fintype W]
open scoped ENNReal

/-! ## §1. Measure-valued consequent (C&M eq. 44) -/

/-- The @cite{chung-mascarenhas-2024} compositional conditional:
`⟦if φ, γ⟧^w = E_w[γ ∣ φ]`, where `γ : W → ℝ≥0∞` is a measure function
on worlds. Reduces to a probability when `γ` is a `{0,1}`-indicator. -/
noncomputable def condIf (p : PMF W) (φ : Set W) (γ : W → ℝ≥0∞) : ℝ≥0∞ :=
  p.condExpect φ γ

/-- @cite{adams-1965}: when the consequent `γ` is the `{0,1}`-indicator
of a propositional consequent `ψ`, the conditional reduces to the
conditional probability `P(ψ ∣ φ)`. -/
theorem condIf_propositional (p : PMF W) (φ ψ : Set W)
    [DecidablePred (· ∈ φ)] [DecidablePred (· ∈ ψ)] :
    condIf p φ (fun w => if w ∈ ψ then 1 else 0) = p.condProbSet φ ψ :=
  p.condExpect_indicator φ ψ

end Semantics.Conditionals.Probabilistic
