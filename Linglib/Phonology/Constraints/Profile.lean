import Linglib.Core.Optimization.Evaluation
import Linglib.Phonology.Constraints.Defs

/-!
# Violation Profiles

The framework-neutral violation-profile vocabulary, shared by Optimality
Theory (lexicographic comparison) and Harmonic Grammar (weighted aggregation,
see `[riggle-2009]`). A `ViolationProfile n` is the `n`-tuple of violation
counts a candidate incurs against `n` ranked constraints.

These are OT-tradition names for the neutral primitives in
`Core.Optimization.Evaluation`; downstream phonology code uses these rather
than the generic `Lex (Fin n → Nat)` / `lexFinNatOf` spellings.

## Main definitions

* `ViolationProfile n` — `Lex (Fin n → Nat)`, a fixed-length violation vector.
* `buildViolationProfile` — assemble a profile from a constraint vector.
* `mkProfile` — assemble a profile from a ranked `NamedConstraint` list.

## Main results

* `ViolationProfile.zero_le` — the zero profile is the bottom element.
* `ViolationProfile.le_apply_zero` — first-component extraction from `≤`.
-/

namespace Constraints

open Core.Optimization.Evaluation

/-- OT-named alias for `Lex (Fin n → Nat)` — fixed-length violation profile. -/
abbrev ViolationProfile (n : Nat) := Lex (Fin n → Nat)

variable {C : Type*} {n : Nat}

/-- OT-named alias for `lexFinNatOf` — assemble a profile from a constraint
vector `Fin n → C → Nat`. -/
abbrev buildViolationProfile
    (constraints : Fin n → C → Nat) (c : C) : ViolationProfile n :=
  lexFinNatOf constraints c

/-- The zero profile is the minimum: `0 ≤ p` for every profile `p`.

Under `Pi.Lex`, `p < 0` would require some `p i < 0 i = 0`, impossible in
`Nat`. This is the structural reason a candidate with zero violations on every
constraint wins under any ranking, and underlies Dijkstra monotonicity of the
violation semiring (`[riggle-2009]`). -/
theorem ViolationProfile.zero_le (p : ViolationProfile n) :
    (0 : ViolationProfile n) ≤ p :=
  bot_le

/-- OT-named alias for `lexFinNat_le_apply_zero` — first-component extraction
from a lexicographic `≤`. -/
theorem ViolationProfile.le_apply_zero
    {a b : ViolationProfile (n + 1)} (h : a ≤ b) : a 0 ≤ b 0 :=
  lexFinNat_le_apply_zero h

/-- Build a `ViolationProfile ranking.length` from a ranked list of named
constraints. The fixed-length analog of the profile computation inside
`OptimalityTheory.mkTableau`, for inspecting violation counts outside a
tableau context. -/
def mkProfile (ranking : List (NamedConstraint C)) (c : C) :
    ViolationProfile ranking.length :=
  buildViolationProfile (fun i => (ranking.get i).eval) c

end Constraints
