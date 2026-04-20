import Linglib.Tactics.RSAPredict.Backend.QInterval
import Linglib.Tactics.RSAPredict.Backend.PadeExp
import Linglib.Tactics.RSAPredict.Backend.LogInterval
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# SqrtInterval — Interval Square Root via exp(log/2)

For positive intervals, `√x = exp(log(x)/2)`. Computed by chaining
`logInterval`, rational halving, and `expInterval`.

Used by `RExpr.rsqrt` to support `Real.sqrt` in the `rsa_predict` tactic,
enabling Hellinger-distance-based RSA models (@cite{herbstritt-franke-2019}).
-/

namespace Interval

open Interval.QInterval

/-- Interval square root for positive intervals.
    Uses the identity `√x = exp(log(x) / 2)` for `x > 0`.
    Chains `logInterval`, rational halving, and `expInterval`. -/
def sqrtInterval (a : QInterval) (ha : 0 < a.lo) : QInterval :=
  let logA := logInterval a ha
  let halfLog : QInterval := {
    lo := logA.lo / 2,
    hi := logA.hi / 2,
    valid := by linarith [logA.valid]
  }
  expInterval halfLog

/-- Soundness: if `x ∈ [a.lo, a.hi]` and `a.lo > 0`, then `√x ∈ sqrtInterval a`. -/
theorem sqrtInterval_containsReal {a : QInterval} {x : ℝ}
    (ha : 0 < a.lo) (hx : a.containsReal x) :
    (sqrtInterval a ha).containsReal (Real.sqrt x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le (by exact_mod_cast ha) hx.1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx_pos]
  unfold sqrtInterval
  apply expInterval_containsReal
  have hlog := logInterval_containsReal ha hx
  simp only [containsReal]
  push_cast
  constructor <;> nlinarith [hlog.1, hlog.2]

end Interval
