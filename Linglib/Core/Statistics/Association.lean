import Mathlib.Algebra.Order.Ring.Rat

/-!
# Directional Association (ΔP)
@cite{cheng-holyoak-1995} @cite{ellis-2006} @cite{dunn-2025}

ΔP is a contingency-table directional association measure (Cheng & Holyoak's
Probabilistic Contrast Model). Originally housed in `Core.InformationTheory`
but relocated here in 0.230.602 — it's a frequency-based statistic, not a
Shannon-entropy quantity.

## Definitions

- `deltaP`: directional association `P(y|x) − P(y|¬x)` (ℚ-valued, no log)
- `deltaPCounts`: ΔP from a 2×2 contingency table (ℚ-valued, no log)
- `deltaP_eq_zero_of_independent`: ΔP = 0 under statistical independence

ΔP-based theories used in linglib:
- @cite{ellis-2006} — L2 morpheme acquisition difficulty (low-ΔP grammatical
  functors are acquired late because of cue-outcome competition)
- @cite{dunn-2025} — corpus-based construction grammar (ΔP-thresholded
  slot-filler associations identify constructions)
-/

namespace Core.Statistics

/-- ΔP: directional association measure (@cite{ellis-2006}, Table 1;
via @cite{cheng-holyoak-1995} Probabilistic Contrast Model).

ΔP(x → y) = P(y | x) - P(y | ¬x)

Measures how much knowing x changes the probability of y.
@cite{ellis-2006} uses ΔP to explain L2 morpheme acquisition: grammatical
functors with low ΔP (many cue-outcome competitors) are acquired late.
@cite{dunn-2025} uses ΔP to identify constructions from corpus data.

Properties:
- Bounded: ΔP ∈ [-1, 1] for valid probability inputs
- ΔP = 0 when x and y are independent (see `deltaP_eq_zero_of_independent`)
- Directional: ΔP(x→y) ≠ ΔP(y→x) in general

Takes joint probability P(x,y), marginal P(x), and marginal P(y).
Returns the directional association from x to y. -/
def deltaP (pXY pX pY : ℚ) : ℚ :=
  let pYgivenX := if pX ≤ 0 then 0 else pXY / pX
  let pYgivenNotX := if pX ≥ 1 then 0 else (pY - pXY) / (1 - pX)
  pYgivenX - pYgivenNotX

/-- ΔP from a 2×2 contingency table (@cite{ellis-2006}, Table 1).

Given observed counts:

|     |  y  | ¬y  |
|-----|-----|-----|
|  x  |  a  |  b  |
| ¬x  |  c  |  d  |

ΔP(x → y) = a/(a+b) - c/(c+d)

This is the standard form for contingency learning: `a` is the frequency of
cue-outcome co-occurrence, `b` is cue without outcome, `c` is outcome
without cue, `d` is neither. Also used in corpus-based CxG (@cite{dunn-2025})
for slot-filler association strength. -/
def deltaPCounts (a b c d : ℕ) : ℚ :=
  let ab : ℚ := ↑a + ↑b
  let cd : ℚ := ↑c + ↑d
  (if ab = 0 then 0 else ↑a / ab) - (if cd = 0 then 0 else ↑c / cd)

/-- ΔP vanishes under independence: if P(x,y) = P(x)·P(y), then ΔP = 0.

This is the key property: ΔP measures departure from independence.
When slot and filler are statistically independent (knowing the slot
tells you nothing about the filler), ΔP is zero. -/
theorem deltaP_eq_zero_of_independent (pX pY : ℚ)
    (hpX_pos : 0 < pX) (hpX_lt : pX < 1) :
    deltaP (pX * pY) pX pY = 0 := by
  have hne : pX ≠ 0 := (ne_of_lt hpX_pos).symm
  have hne1 : (1 : ℚ) - pX ≠ 0 := sub_ne_zero.mpr (ne_of_lt hpX_lt).symm
  dsimp only [deltaP]
  rw [if_neg (not_le.mpr hpX_pos), if_neg (not_le.mpr hpX_lt)]
  rw [mul_div_cancel_left₀ pY hne]
  rw [show pY - pX * pY = pY * (1 - pX) from by
    rw [mul_sub, mul_one, mul_comm pY pX]]
  rw [mul_div_cancel_right₀ pY hne1, sub_self]

end Core.Statistics
