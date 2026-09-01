import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Prototype meaning for quantity words

A quantity word's meaning as a non-negative gradient over the proportion scale, peaking at a
per-word `prototype` and falling off with distance at a per-word `spread`.

The bump kernel is a rational-arithmetic approximation of a Gaussian
`exp(-x²)` — specifically, a piecewise-linear-in-`|x|` tent that is
genuinely non-negative, monotone-decreasing in `|x|`, and continuous
at the breakpoints. See `bumpKernel`.

Paper-specific models (`Studies/VanTielEtAl2021.lean`) supply the prototype and spread
parameters.

## References

* [B. van Tiel, M. Franke and U. Sauerland, *Probabilistic pragmatics explains gradience and
  focality in natural language quantification* (2021)][van-tiel-franke-sauerland-2021]
-/

namespace Quantification.Prototype

/-- Tent kernel: `max 0 (1 - |x|)`. Non-negative, monotone-decreasing
in `|x|`, continuous, peak `1` at `x = 0`, vanishes for `|x| ≥ 1`.
Approximates a Gaussian bump in rational arithmetic without the
discontinuities and negative excursions of the previous piecewise
quadratic. -/
def bumpKernel (x : ℚ) : ℚ :=
  let ax := if x < 0 then -x else x
  if ax ≥ 1 then 0 else 1 - ax

theorem bumpKernel_nonneg (x : ℚ) : 0 ≤ bumpKernel x := by
  simp only [bumpKernel]
  split_ifs with h1 h2 h2
  · norm_num
  · linarith
  · norm_num
  · linarith

/-- PT meaning at intersection-count `t` for a word with prototype `p`
and spread `d > 0` over a domain of size `n`.

Distance from the prototype is normalized by spread, then passed
through the bump kernel. -/
def ptMeaning (n : Nat) (p : Nat) (d : ℚ) (t : Fin (n + 1)) : ℚ :=
  let distance : ℚ := (t.val : ℚ) - (p : ℚ)
  let normalized := distance / d
  bumpKernel normalized

theorem ptMeaning_nonneg (n : Nat) (p : Nat) (d : ℚ) (t : Fin (n + 1)) :
    0 ≤ ptMeaning n p d t :=
  bumpKernel_nonneg _

end Quantification.Prototype
