import Linglib.Core.Optimization.Evaluation
import Linglib.Phonology.Constraints.Defs

/-!
# Violation Profiles

OT-tradition names for the neutral violation primitives in
`Core.Optimization.Evaluation`, shared by Optimality Theory (lexicographic
comparison) and Harmonic Grammar (weighted aggregation, `[riggle-2009]`).

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
    vector. -/
abbrev buildViolationProfile
    (constraints : Fin n → C → Nat) (c : C) : ViolationProfile n :=
  lexFinNatOf constraints c

/-- The zero profile is the bottom element: `0 ≤ p` for every profile `p`, so a
    candidate with no violations wins under any ranking. -/
theorem ViolationProfile.zero_le (p : ViolationProfile n) :
    (0 : ViolationProfile n) ≤ p :=
  bot_le

/-- OT-named alias for `lexFinNat_le_apply_zero` — first-component extraction
    from a lexicographic `≤`. -/
theorem ViolationProfile.le_apply_zero
    {a b : ViolationProfile (n + 1)} (h : a ≤ b) : a 0 ≤ b 0 :=
  lexFinNat_le_apply_zero h

/-- Build a `ViolationProfile ranking.length` from a ranked `NamedConstraint`
    list — the fixed-length analog of the profile inside `OptimalityTheory.mkTableau`. -/
def mkProfile (ranking : List (NamedConstraint C)) (c : C) :
    ViolationProfile ranking.length :=
  buildViolationProfile (fun i => (ranking.get i).eval) c

end Constraints
