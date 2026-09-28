/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Constraints.Basic
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.Subregular.ForbiddenPairs

/-!
# Bridge: forbidden-pair markedness and TSL₂

The generic bridge from the forbidden-pair constraint `Constraint.forbidPairs R` of
`Phonology/Constraints/Basic.lean` to the tier-based strictly 2-local languages
`TierStrictlyLocalGrammar.ofForbiddenPairs R p` of `Phonology/Subregular/ForbiddenPairs.lean`
([heinz-rawal-tanner-2011]). On a tier `p` the constraint is the pullback along erasure of the
off-tier symbols, and its zero set is the TSL₂ language, for any forbidden-pair relation `R`. The
OCP and AGREE bridges of `OCP.lean` and `Agree.lean` are its identity and non-identity instances.

## Main definitions

* `Constraints.Constraint.zeroSet`: the zero-violation language of a constraint on strings. It
  lives here, not in `Constraints/Defs.lean`, so the framework-neutral constraint vocabulary stays
  free of `Computability`.

## Main results

* `Constraints.Constraint.zeroSet_comap`: pulling a constraint back pulls its zero set back.
* `Constraints.Constraint.zeroSet_comap_filter_forbidPairs`: on a tier, the zero set of the
  forbidden-pair constraint is the TSL₂ language of `ofForbiddenPairs`.

## References

* [J. Heinz, C. Rawal and H. G. Tanner, *Tier-based Strictly Local Constraints for Phonology*
  (2011)][heinz-rawal-tanner-2011]
-/

@[expose] public section

namespace Constraints

variable {α β : Type*}

/-- The language of strings that satisfy `c`, with zero violations. It lets the `eval = 0`
predicate compose with `Language.IsRegular` and the subregular classes (`IsTierStrictlyLocal`,
`IsBTC`). -/
def Constraint.zeroSet (c : Constraint (List α)) : Language α :=
  { w | c w = 0 }

namespace Constraint

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

end Constraints
