/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Theories.Phonology.Subregular.ForbidPairs
import Linglib.Theories.Phonology.Subregular.TierProjection

/-!
# AGREE ↔ TSL_2 — the inequality instance (dual of OCP)

AGREE-style markedness in OT phonology is the non-identity dual of the
OCP: tier-adjacent symbols must *agree* (be equal) rather than *differ*.
As an instance of the generic forbidden-pair constructor
`mkForbidPairsOnTier` (see `ForbidPairs.lean`), AGREE is the
specialization with `R := (· ≠ ·)`, just as the OCP is the `R := (· = ·)`
specialization.

The duality is structural, not metaphorical: the OCP penalizes adjacent
*identical* tier elements (the "no double" rule, forcing dissimilation);
AGREE penalizes adjacent *distinct* tier elements (the "no different"
rule, forcing assimilation/harmony). Consonant harmony, vowel harmony,
and tone spreading factor through `TSLGrammar.agree`; dissimilation,
anti-geminate, and Meeussen's rule factor through `TSLGrammar.ocp`. The
generic `TSLGrammar.ofForbiddenPairs` subsumes both — and asymmetric
patterns that are neither pure agreement nor pure dissimilation
(directional harmony driven by morphological geometry, e.g. Kikongo nasal
harmony in `Phenomena/Phonology/Studies/RoseWalker2004.lean`) instantiate
the generic constructor directly with their own asymmetric `R`.

Everything here is a one-line specialization of the generic
forbidden-pair infrastructure to `R := (· ≠ ·)`. The AGREE-specific names
(`agreeForbidden`, `AgreeCleanPair`, `TSLGrammar.agree`,
`mkAgreeOnTier_zero_iff_in_agree_lang`) are the canonical entry points
downstream consumers reference.
-/

namespace Phonology.Subregular

open Phonology.Constraints
open Core Core.Computability.Subregular

-- `α : Type` (rather than `Type*`) is forced by `Phonology.Constraints`
-- and `Core.Constraint.eval`, which are monomorphic in universe 0. See
-- the parallel comment in `OCP.lean`.
variable {α : Type}

/-- Forbidden 2-factors for AGREE: pairs `[some x, some y]` of two distinct
non-boundary symbols. The inequality-relation specialization of
`forbiddenPairsSet`. -/
def agreeForbidden (α : Type) [DecidableEq α] : Set (Augmented α) :=
  forbiddenPairsSet (α := α) (· ≠ ·)

/-- The TSL_2 grammar capturing "no two adjacent distinct symbols on the
tier defined by `p`" — equivalently, every tier-adjacent pair agrees.
The inequality-relation specialization of `TSLGrammar.ofForbiddenPairs`. -/
def TSLGrammar.agree [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    TSLGrammar 2 α :=
  TSLGrammar.ofForbiddenPairs (α := α) (· ≠ ·) p

/-- The AGREE relation on `Option α`: two augmented symbols are *AGREE-clean
as a pair* iff they are not both `some` of distinct values. The
inequality-relation specialization of `CleanPair`. -/
def AgreeCleanPair [DecidableEq α] : Option α → Option α → Prop :=
  CleanPair (α := α) (· ≠ ·)

lemma agreeCleanPair_some_some [DecidableEq α] (a b : α) :
    AgreeCleanPair (some a) (some b) ↔ a = b := by
  rw [show AgreeCleanPair (some a) (some b) ↔ ¬ a ≠ b from
        CleanPair.some_some a b]
  exact not_not

/-- The AGREE relation is boundary-vacuous (inequality-relation instance of
`CleanPair.isBoundaryVacuous`). -/
lemma AgreeCleanPair.isBoundaryVacuous [DecidableEq α] :
    IsBoundaryVacuous (AgreeCleanPair (α := α)) :=
  CleanPair.isBoundaryVacuous

/-- **Bridge** (relational form): a candidate's AGREE score is zero iff its
raw string projects (under `Tier.byClass p`) to a list with no two
adjacent distinct elements — i.e. all on-tier elements are equal.
Inequality-relation specialization of `mkForbidPairsOnTier_zero_iff_isChain`. -/
theorem mkAgreeOnTier_zero_iff_isChain [DecidableEq α] {C : Type}
    (name : String) (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkAgreeOnTier name (Tier.byClass p) extract).eval c = 0 ↔
      ((extract c).filter (fun x => decide (p x))).IsChain (fun a b => ¬ a ≠ b) :=
  mkForbidPairsOnTier_zero_iff_isChain name (· ≠ ·) p extract c

/-- **Bridge** (full TSL_2 language form): a candidate's AGREE score is zero
iff its raw string is in the language of the TSL_2 grammar
`TSLGrammar.agree p`. The two perspectives on AGREE — optimality-theoretic
constraint and subregular-complexity class — are co-extensive.
Inequality-relation specialization of `mkForbidPairsOnTier_zero_iff_in_lang`. -/
theorem mkAgreeOnTier_zero_iff_in_agree_lang [DecidableEq α] {C : Type}
    (name : String) (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkAgreeOnTier name (Tier.byClass p) extract).eval c = 0 ↔
      extract c ∈ (TSLGrammar.agree p).lang :=
  mkForbidPairsOnTier_zero_iff_in_lang name (· ≠ ·) p extract c

end Phonology.Subregular
