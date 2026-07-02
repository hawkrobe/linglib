/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Constraints.Basic
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Core.Computability.Subregular.Language.ForbiddenPairs

/-!
# Bridge: Forbidden-Pair Markedness ↔ TSL_2

The single generic bridge connecting Optimality-theoretic forbidden-pair
markedness constraints (`mkForbidPairsOnTier`, defined in
`OptimalityTheory/Constraints.lean`) to tier-based strictly 2-local
languages (`TSLGrammar.ofForbiddenPairs`, defined in
`Core/Computability/Subregular/Language/ForbiddenPairs.lean`).

A candidate's `mkForbidPairsOnTier` score is zero iff its raw string
belongs to the corresponding TSL_2 language — for any choice of
forbidden-pair relation `R`. The OCP-specific specialization (with
`R := (· = ·)`) lives in `Subregular/OCP.lean` and is now a one-line
corollary.

## Main definitions

* `Constraints.Constraint.zeroSet` — the zero-violation language of a
  constraint, the `Constraint → Language` primitive these bridges
  characterize. It lives here, not in `Constraints/Defs.lean`, so the
  framework-neutral constraint vocabulary stays free of `Computability`.
-/

namespace Constraints

variable {α : Type*}

/-- The language of list candidates that satisfy `c` (zero violations), as a
    `Language α`. Lets the `eval = 0` predicate compose with `Language.IsRegular`
    and the project's subregular classifiers (`IsTierStrictlyLocal`, `IsBTC`). -/
def Constraint.zeroSet (c : Constraint (List α)) : Language α :=
  { w | c w = 0 }

theorem Constraint.mem_zeroSet (c : Constraint (List α)) (w : List α) :
    w ∈ c.zeroSet ↔ c w = 0 := Iff.rfl

end Constraints

namespace Subregular

open Constraints OptimalityTheory

variable {α : Type}

-- `countAdjacent_eq_zero_iff_isChain` lives in
-- `Subregular.ForbiddenPairs` (alongside `countAdjacent`
-- itself) since it is alphabet-generic.

/-- **Bridge** (relational form): a candidate's forbidden-pair score is zero
iff its raw string projects (under `TierProjection.byClass p`) to a list with no
two adjacent elements related by `R`. The chain-side payoff of the
generic forbidden-pair design. -/
theorem mkForbidPairsOnTier_zero_iff_isChain {C : Type}
    (R : α → α → Prop) [DecidableRel R] (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkForbidPairsOnTier R (TierProjection.byClass p) extract) c = 0 ↔
      ((extract c).filter (fun x => decide (p x))).IsChain (fun a b => ¬ R a b) := by
  show countAdjacent R (TierProjection.apply (TierProjection.byClass p) (extract c)) = 0 ↔ _
  rw [TierProjection.apply_byClass]
  exact countAdjacent_eq_zero_iff_isChain _ _

/-- **Bridge** (TSL_2 language form): a candidate's forbidden-pair score is
zero iff its raw string is in the language of
`TSLGrammar.ofForbiddenPairs R p`. The single generic bridge that every
adjacency-based markedness constraint inherits. Composes the relational
bridge `mkForbidPairsOnTier_zero_iff_isChain` with the carrier-level
language characterization `mem_ofForbiddenPairs_lang_iff_filter_isChain`. -/
theorem mkForbidPairsOnTier_zero_iff_in_lang {C : Type}
    (R : α → α → Prop) [DecidableRel R] (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkForbidPairsOnTier R (TierProjection.byClass p) extract) c = 0 ↔
      extract c ∈ (TSLGrammar.ofForbiddenPairs R p).lang := by
  rw [mkForbidPairsOnTier_zero_iff_isChain,
      mem_ofForbiddenPairs_lang_iff_filter_isChain]

end Subregular
