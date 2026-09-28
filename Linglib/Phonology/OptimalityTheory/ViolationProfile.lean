/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.PiLex
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Mathlib.Algebra.Order.Group.PiLex

/-!
# Violation profiles

A candidate's violation profile under a constraint set is its violation vector ordered
lexicographically, `Lex (Fin n → ℕ)` from `Mathlib/Order/PiLex` ([riggle-2009b]). The
lexicographic order is Optimality Theory's strict domination, so the profile is OT's. Harmonic
Grammar weights the same vector without ordering it (`HarmonicGrammar.harmonyScore`).

## Main definitions

* `ViolationProfile n` — `Lex (Fin n → Nat)`, a fixed-length violation vector. The profile of a
  candidate `c` under a constraint set `con` read in rank order `r` is `toLex fun p ↦ con (r p) c`.

## Main results

* `ViolationProfile.le_apply_zero` — first-component extraction from `≤`.

## References

* [J. Riggle, *Violation semirings in Optimality Theory* (2009)][riggle-2009b]
-/

@[expose] public section

namespace OptimalityTheory

/-- A fixed-length violation profile, the violation vector `Fin n → ℕ` under its lexicographic
order. -/
abbrev ViolationProfile (n : Nat) := Lex (Fin n → Nat)

variable {n : Nat}

/-- A profile at most another is at most it on the first constraint. -/
theorem ViolationProfile.le_apply_zero
    {a b : ViolationProfile (n + 1)} (h : a ≤ b) : a 0 ≤ b 0 :=
  Pi.apply_le_of_toLex (x := ofLex a) (y := ofLex b) h fun j hj ↦ absurd hj (Fin.not_lt_zero j)

end OptimalityTheory
