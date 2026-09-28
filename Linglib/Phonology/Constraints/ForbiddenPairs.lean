/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Constraints.Defs
public import Linglib.Phonology.Subregular.ForbiddenPairs

/-!
# Forbidden-pair constraints

This file defines the forbidden-pair constraints on strings, which carry genuine adjacency logic:
`Constraint.forbidPairs R`, with one violation for each adjacent pair `(a, b)` satisfying `R a b`,
and its identity and non-identity instances, the OCP ([goldsmith-1976], [mccarthy-1986]) and
AGREE. A constraint on candidates of another type, or on a tier, is not a separate constructor
but the `Constraint.comap` of a string constraint along the candidate's string or along erasure
of the off-tier symbols. Pulled back along the output form of a correspondence candidate, a
string constraint is a markedness constraint (`Correspondence.isMarkedness_iff_exists_comap`).

On a tier, the zero set of `Constraint.forbidPairs R` is the tier-based strictly 2-local language
of `TierStrictlyLocalGrammar.ofForbiddenPairs R p` ([heinz-rawal-tanner-2011]). The OCP and AGREE
instances of this bridge are in `Subregular/OCP.lean` and `Subregular/Agree.lean`.

## Main definitions

* `Constraint.forbidPairs`, `Constraint.ocp`, `Constraint.agree`: the forbidden-pair constraints
  on strings.
* `Constraint.zeroSet`: the zero-violation language of a constraint on strings.

## Main results

* `Constraint.zeroSet_comap`: pulling a constraint back pulls its zero set back.
* `Constraint.zeroSet_comap_filter_forbidPairs`: on a tier, the zero set of the forbidden-pair
  constraint is the TSL₂ language of `ofForbiddenPairs`.

## Implementation notes

`Constraint.ocp` and `Constraint.agree` compare whole symbols. Over segments, `ocp` is the
identity OCP rather than OCP-Place, and `agree` is AGREE[F] only after the string is projected
to the values of the feature `F`.

## References

* [J. A. Goldsmith, *Autosegmental Phonology* (1976)][goldsmith-1976]
* [J. J. McCarthy, *OCP Effects: Gemination and Antigemination* (1986)][mccarthy-1986]
* [J. Heinz, C. Rawal and H. G. Tanner, *Tier-based Strictly Local Constraints for Phonology*
  (2011)][heinz-rawal-tanner-2011]
* [I. Berent, *Three arguments for abstraction in phonology* (2026)][berent-2026]
-/

@[expose] public section

namespace OptimalityTheory

open Subregular (countAdjacent)

variable {α β : Type*}

/-- The forbidden-pair constraint on strings, with one violation for each adjacent pair `(a, b)`
satisfying `R a b`. -/
def Constraint.forbidPairs (R : α → α → Prop) [DecidableRel R] : Constraint (List α) :=
  countAdjacent R

/-- The OCP ([goldsmith-1976], [mccarthy-1986]), the forbidden-pair constraint against adjacent
identical elements, polymorphic over the feature type ([berent-2026]). -/
def Constraint.ocp [DecidableEq α] : Constraint (List α) := Constraint.forbidPairs (· = ·)

/-- AGREE, the forbidden-pair constraint against adjacent distinct elements and the dual of
`Constraint.ocp`. -/
def Constraint.agree [DecidableEq α] : Constraint (List α) := Constraint.forbidPairs (· ≠ ·)

/-- The language of strings that satisfy `c`, with zero violations. It lets the `eval = 0`
predicate compose with `Language.IsRegular` and the subregular classes (`IsTierStrictlyLocal`,
`IsBTC`). -/
def Constraint.zeroSet (c : Constraint (List α)) : Language α :=
  { w | c w = 0 }

namespace Constraint

theorem ocp_cons_self [DecidableEq α] (a : α) (w : List α) :
    ocp (a :: a :: w) = 1 + ocp (a :: w) := by
  simp [ocp, forbidPairs, countAdjacent]

theorem ocp_cons_of_ne [DecidableEq α] {a b : α} (h : a ≠ b) (w : List α) :
    ocp (a :: b :: w) = ocp (b :: w) := by
  simp [ocp, forbidPairs, countAdjacent, h]

/-- The OCP is invariant under an injective relabelling of the elements. -/
theorem ocp_map [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (w : List α) : ocp (w.map f) = ocp w :=
  Subregular.countAdjacent_map (· = ·) (S := (· = ·)) (fun _ _ ↦ hf.eq_iff) w

theorem mem_zeroSet (c : Constraint (List α)) (w : List α) : w ∈ c.zeroSet ↔ c w = 0 := Iff.rfl

/-- Pulling a constraint back along a string map pulls its zero set back. -/
@[simp] theorem zeroSet_comap (f : List α → List β) (c : Constraint (List β)) :
    (c.comap f).zeroSet = f ⁻¹' c.zeroSet := rfl

/-- A string satisfies the forbidden-pair constraint iff no two adjacent elements are
`R`-related. -/
theorem forbidPairs_eq_zero_iff (R : α → α → Prop) [DecidableRel R] (w : List α) :
    forbidPairs R w = 0 ↔ w.IsChain (fun a b ↦ ¬ R a b) :=
  Subregular.countAdjacent_eq_zero_iff_isChain R w

/-- On the tier `p`, the zero set of the forbidden-pair constraint is the language of the TSL₂
grammar `TierStrictlyLocalGrammar.ofForbiddenPairs R p`. -/
theorem zeroSet_comap_filter_forbidPairs (R : α → α → Prop) [DecidableRel R]
    (p : α → Prop) [DecidablePred p] :
    ((forbidPairs R).comap fun w ↦ w.filter (p ·)).zeroSet =
      (Subregular.TierStrictlyLocalGrammar.ofForbiddenPairs R p).language :=
  Set.ext fun w ↦ (forbidPairs_eq_zero_iff R _).trans
    (Subregular.mem_ofForbiddenPairs_language_iff_filter_isChain R p w).symm

end Constraint

end OptimalityTheory
