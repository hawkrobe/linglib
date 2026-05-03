import Linglib.Core.Logic.Bilateral.Defs

/-!
# Bilateral polarity-flip theorems

@cite{anttila-2021} @cite{aloni-2022}

Derived theorems on top of `Core.Logic.Bilateral.IsBilateral`. Consumers
(BSML, QBSML, BUS, ICDRT, Truthmaker) get these for free once they prove
their `IsBilateral` instance.

The headline `IsBilateral.positive_negate_negate` lives in `Defs.lean`
(it's a one-line corollary used pervasively). This file collects the
less-headline-but-still-useful identities about polarity composition.
-/

namespace Core.Logic.Bilateral

universe u v

variable {Form : Type u} {Result : Type v}
variable {positive negative : Form → Result} {negate : Form → Form}

-- ============================================================================
-- §1 Triple-negation collapse
-- ============================================================================

/-- Three applications of `negate` collapse to one (on `positive`):
    `positive (negate^3 φ) = negative φ`. The DNE result on `positive`
    composes with another `positive_negate` step. -/
theorem IsBilateral.positive_negate_three (h : IsBilateral positive negative negate)
    (φ : Form) : positive (negate (negate (negate φ))) = negative φ := by
  rw [h.positive_negate_negate, h.positive_negate]

/-- Three applications of `negate` collapse to one (on `negative`):
    `negative (negate^3 φ) = positive φ`. -/
theorem IsBilateral.negative_negate_three (h : IsBilateral positive negative negate)
    (φ : Form) : negative (negate (negate (negate φ))) = positive φ := by
  rw [h.negative_negate_negate, h.negative_negate]

-- ============================================================================
-- §2 Bilateral congruence
-- ============================================================================

/-- If two formulas have equal `positive`, their negations have equal
    `negative`. The bilateral analogue of "negation is a function." -/
theorem IsBilateral.negate_congr_negative (h : IsBilateral positive negative negate)
    {φ ψ : Form} (heq : positive φ = positive ψ) :
    negative (negate φ) = negative (negate ψ) := by
  rw [h.negative_negate, h.negative_negate, heq]

/-- If two formulas have equal `negative`, their negations have equal
    `positive`. -/
theorem IsBilateral.negate_congr_positive (h : IsBilateral positive negative negate)
    {φ ψ : Form} (heq : negative φ = negative ψ) :
    positive (negate φ) = positive (negate ψ) := by
  rw [h.positive_negate, h.positive_negate, heq]

end Core.Logic.Bilateral
