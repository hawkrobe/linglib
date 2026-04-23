import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Prototype Theory: Gradient Meaning over a Numerical Domain

Generic Prototype-Theory operator parameterized by per-word
`prototype` and `spread`: meaning is a non-negative gradient peaking
at the prototype and falling off with distance, scaled by `spread`.

The bump kernel is a rational-arithmetic approximation of a Gaussian
`exp(-x²)` — specifically, a piecewise-linear-in-`|x|` tent that is
genuinely non-negative, monotone-decreasing in `|x|`, and continuous
at the breakpoints. See `bumpKernel`.

This is the parametric theory consumed by paper-specific PT models
(e.g., `Phenomena/ScalarImplicatures/Studies/VanTielEtAl2021.lean`),
which provide their own prototype/spread parameter values.
-/

namespace Theories.Semantics.Probabilistic.PrototypeTheory

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

end Theories.Semantics.Probabilistic.PrototypeTheory
