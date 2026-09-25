module

public import Linglib.Core.Order.PiLex
public import Linglib.Phonology.Constraints.Defs
public import Mathlib.Algebra.Order.Group.PiLex

/-!
# Violation Profiles

OT-tradition names for the lexicographically ordered violation vectors of `Mathlib/Order/PiLex`,
shared by Optimality Theory (lexicographic comparison) and Harmonic Grammar (weighted aggregation,
[riggle-2009b]).

## Main definitions

* `ViolationProfile n` — `Lex (Fin n → Nat)`, a fixed-length violation vector.
* `buildViolationProfile` — assemble a profile from a constraint vector.

## Main results

* `ViolationProfile.zero_le` — the zero profile is the bottom element.
* `ViolationProfile.le_apply_zero` — first-component extraction from `≤`.

## References

* [J. Riggle, *Violation semirings in Optimality Theory* (2009)][riggle-2009b]
-/

@[expose] public section

namespace Constraints

/-- OT-named alias for `Lex (Fin n → Nat)` — fixed-length violation profile. -/
abbrev ViolationProfile (n : Nat) := Lex (Fin n → Nat)

variable {C : Type*} {n : Nat}

/-- The profile of a candidate under a constraint set `CON C n`: its violations, in ranking
order. -/
abbrev buildViolationProfile (con : CON C n) (c : C) : ViolationProfile n :=
  toLex fun i ↦ con i c

@[simp] theorem buildViolationProfile_apply (con : CON C n) (c : C) (i : Fin n) :
    buildViolationProfile con c i = con i c := rfl

/-- The zero profile is the bottom element: `0 ≤ p` for every profile `p`, so a
    candidate with no violations wins under any ranking. -/
theorem ViolationProfile.zero_le (p : ViolationProfile n) :
    (0 : ViolationProfile n) ≤ p :=
  bot_le

/-- A profile at most another is at most it on the first constraint. -/
theorem ViolationProfile.le_apply_zero
    {a b : ViolationProfile (n + 1)} (h : a ≤ b) : a 0 ≤ b 0 :=
  Pi.apply_le_of_toLex (x := ofLex a) (y := ofLex b) h fun j hj ↦ absurd hj (Fin.not_lt_zero j)

end Constraints
