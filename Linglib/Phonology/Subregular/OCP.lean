/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Subregular.ForbidPairs
import Linglib.Phonology.Subregular.TierProjection

/-!
# OCP (Obligatory Contour Principle) ↔ TSL_2 — the identity instance

The OCP @cite{goldsmith-1976} @cite{mccarthy-1986} is the identity-relation
instance of the generic forbidden-pair markedness constructor
`mkForbidPairsOnTier` (see `ForbidPairs.lean`): the forbidden 2-factor is
`[some x, some x]`, and the corresponding TSL_2 grammar is
`TSLGrammar.ofForbiddenPairs (· = ·) p`.

Mathematically, the unprojected (single-tier, full-alphabet) case is the
linguistic instance of the classical theory of *square-free words*
@cite{thue-1906}: a word is OCP-clean iff it contains no factor `x x`.
Thue's construction shows infinite square-free words exist over a
3-letter alphabet, while every binary string of length ≥ 4 contains a
square — i.e. binary tonal alphabets cannot satisfy a strict OCP at
length, which is itself a phonological prediction.

Everything in this file is a one-line specialization of the generic
forbidden-pair infrastructure to `R := (· = ·)`. The OCP-specific names
(`ocpForbidden`, `OCPCleanPair`, `TSLGrammar.ocp`,
`mkOCPOnTier_zero_iff_in_ocp_lang`) are kept as the canonical entry
points downstream consumers reference.

## OCP-as-prohibition vs OCP-as-merger

This file formalizes the **prohibition** reading of the OCP — strings
containing adjacent identical (tier-projected) autosegments are *rejected*
by `TSLGrammar.ocp p`. The classical autosegmental tradition
(@cite{goldsmith-1976}) instead reads the OCP as a *merger
transformation*: adjacent identical autosegments are *collapsed* into a
single multiply-linked autosegment. The merger reading is formalized by
`Phonology.Autosegmental.RegisterTier.mergeTRN` (and the underlying
`FeatureBundle.merge`) — a repair operation on representations, not a
language predicate. The two readings are operationally distinct, both
trace to the same body of literature, and coexist in linglib without a
master bridge — the prohibition reading classifies a stringset; the
merger reading fixes a representation.
-/

namespace Phonology.Subregular

open Phonology.Constraints
open Core Core.Computability.Subregular

-- `α : Type` (rather than `Type*`) is forced by `Phonology.Constraints`
-- and `Core.Constraint.eval`, which are monomorphic in universe 0.
variable {α : Type}

/-- Forbidden 2-factors for the OCP: pairs `[some x, some x]` of two identical
non-boundary symbols. The identity-relation specialization of
`forbiddenPairsSet`. -/
def ocpForbidden (α : Type) [DecidableEq α] : Set (Augmented α) :=
  forbiddenPairsSet (α := α) (· = ·)

/-- The TSL_2 grammar capturing "no two adjacent identical symbols on the
tier defined by `p`". The identity-relation specialization of
`TSLGrammar.ofForbiddenPairs`. -/
def TSLGrammar.ocp [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    TSLGrammar 2 α :=
  TSLGrammar.ofForbiddenPairs (α := α) (· = ·) p

/-- The OCP relation on `Option α`: two augmented symbols are *OCP-clean as
a pair* iff they are not both `some` of the same value. The identity-relation
specialization of `CleanPair`. -/
def OCPCleanPair [DecidableEq α] : Option α → Option α → Prop :=
  CleanPair (α := α) (· = ·)

lemma ocpCleanPair_some_some [DecidableEq α] (a b : α) :
    OCPCleanPair (some a) (some b) ↔ a ≠ b :=
  CleanPair.some_some a b

/-- The OCP relation is boundary-vacuous (identity-relation instance of
`CleanPair.isBoundaryVacuous`). -/
lemma OCPCleanPair.isBoundaryVacuous [DecidableEq α] :
    IsBoundaryVacuous (OCPCleanPair (α := α)) :=
  CleanPair.isBoundaryVacuous

/-- **Bridge** (relational form): a candidate's OCP score is zero iff its
raw string projects (under `Tier.byClass p`) to a list with no two
adjacent identical elements. Identity-relation specialization of
`mkForbidPairsOnTier_zero_iff_isChain`. -/
theorem mkOCPOnTier_zero_iff_isChain [DecidableEq α] {C : Type}
    (name : String) (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkOCPOnTier name (Tier.byClass p) extract).eval c = 0 ↔
      ((extract c).filter (fun x => decide (p x))).IsChain (· ≠ ·) :=
  mkForbidPairsOnTier_zero_iff_isChain name (· = ·) p extract c

/-- **Bridge** (full TSL_2 language form): a candidate's OCP score is zero iff
its raw string is in the language of the TSL_2 grammar `TSLGrammar.ocp p`.
The two perspectives on the OCP — optimality-theoretic constraint and
subregular-complexity class — are co-extensive. Identity-relation
specialization of `mkForbidPairsOnTier_zero_iff_in_lang`. -/
theorem mkOCPOnTier_zero_iff_in_ocp_lang [DecidableEq α] {C : Type}
    (name : String) (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkOCPOnTier name (Tier.byClass p) extract).eval c = 0 ↔
      extract c ∈ (TSLGrammar.ocp p).lang :=
  mkForbidPairsOnTier_zero_iff_in_lang name (· = ·) p extract c

/-- **Zero-set bridge** (OCP on tier): the `Language α`-form restatement
of `mkOCPOnTier_zero_iff_in_ocp_lang` (with `extract := id`). The OCP
markedness constraint's zero-set *is* the corresponding OCP-TSL_2
language. Sibling of `mkForbidPairsOnTier_zeroSet_eq` in OTBound.lean. -/
theorem mkOCPOnTier_zeroSet_eq [DecidableEq α]
    (name : String) (p : α → Prop) [DecidablePred p] :
    (mkOCPOnTier name (Tier.byClass p) (id : List α → List α)).zeroSet =
      (TSLGrammar.ocp p).lang := by
  ext w
  exact mkOCPOnTier_zero_iff_in_ocp_lang name p id w

end Phonology.Subregular
