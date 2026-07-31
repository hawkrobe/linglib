/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Subregular.StrictlyPiecewise
import Linglib.Phonology.Subregular.ForbidPairs
import Linglib.Phonology.Subregular.TierProjection

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
harmony in `Studies/RoseWalker2004.lean`) instantiate
the generic constructor directly with their own asymmetric `R`.

Everything here is a one-line specialization of the generic
forbidden-pair infrastructure to `R := (· ≠ ·)`. The AGREE-specific names
(`agreeForbidden`, `AgreeCleanPair`, `TSLGrammar.agree`,
`mkAgreeOnTier_zero_iff_in_agree_lang`) are the canonical entry points
downstream consumers reference.

Unlike the OCP, AGREE is *also* strictly piecewise: `SPGrammar.agree` and
`TSLGrammar.agree_lang_eq_sp` show the tier projection is dispensable
here, because equality is transitive.
-/

namespace Subregular

open Constraints OptimalityTheory

-- `α : Type` (rather than `Type*`) is forced by `OptimalityTheory`
-- and `Core.Optimization`, which are monomorphic in universe 0. See
-- the parallel comment in `OCP.lean`.
variable {α : Type}

/-- Forbidden 2-factors for AGREE: pairs `[some x, some y]` of two distinct
non-boundary symbols. The inequality-relation specialization of
`forbiddenPairs`. -/
def agreeForbidden (α : Type) [DecidableEq α] : Set (Augmented α) :=
  forbiddenPairs (α := α) (· ≠ ·)

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
raw string projects (under `TierProjection.byClass p`) to a list with no two
adjacent distinct elements — i.e. all on-tier elements are equal.
Inequality-relation specialization of `mkForbidPairsOnTier_zero_iff_isChain`. -/
theorem mkAgreeOnTier_zero_iff_isChain [DecidableEq α] {C : Type}
    (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkAgreeOnTier (TierProjection.byClass p) extract) c = 0 ↔
      ((extract c).filter (fun x => decide (p x))).IsChain (fun a b => ¬ a ≠ b) :=
  mkForbidPairsOnTier_zero_iff_isChain (· ≠ ·) p extract c

/-- **Bridge** (full TSL_2 language form): a candidate's AGREE score is zero
iff its raw string is in the language of the TSL_2 grammar
`TSLGrammar.agree p`. The two perspectives on AGREE — optimality-theoretic
constraint and subregular-complexity class — are co-extensive.
Inequality-relation specialization of `mkForbidPairsOnTier_zero_iff_in_lang`. -/
theorem mkAgreeOnTier_zero_iff_in_agree_lang [DecidableEq α] {C : Type}
    (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkAgreeOnTier (TierProjection.byClass p) extract) c = 0 ↔
      extract c ∈ (TSLGrammar.agree p).lang :=
  mkForbidPairsOnTier_zero_iff_in_lang (· ≠ ·) p extract c

/-- **Zero-set bridge** (AGREE on tier): the `Language α`-form
restatement of `mkAgreeOnTier_zero_iff_in_agree_lang` (with
`extract := id`). The AGREE markedness constraint's zero-set *is* the
corresponding AGREE-TSL_2 language. Sibling of
`mkForbidPairsOnTier_zeroSet_eq` in OTBound.lean and
`mkOCPOnTier_zeroSet_eq` in OCP.lean. -/
theorem mkAgreeOnTier_zeroSet_eq [DecidableEq α]
    (p : α → Prop) [DecidablePred p] :
    (mkAgreeOnTier (TierProjection.byClass p) (id : List α → List α)).zeroSet =
      (TSLGrammar.agree p).lang := by
  ext w
  exact mkAgreeOnTier_zero_iff_in_agree_lang p id w

/-! ### AGREE is also strictly piecewise

Equality is transitive, so "every tier-*adjacent* pair agrees" and "every pair of
on-tier symbols agrees, however far apart" are the same condition — and the latter
reads subsequences, which are blind to the intervening material the tier projection
deletes. AGREE languages are therefore SP_2 as well as TSL_2, the coincidence that
lets transparent long-distance harmony be described either way ([mcmullin-2016]).
The OCP has no such reading: `≠` is not transitive. -/

section Piecewise

open List

/-- The SP_2 grammar dual of `TSLGrammar.agree p`: permit every subsequence except a
pair of disagreeing on-tier symbols. Shorter subsequences are permitted outright. -/
def SPGrammar.agree {α : Type*} (p : α → Prop) : SPGrammar α :=
  {s | ∀ a b, s = [a, b] → p a → p b → a = b}

/-- Membership in the AGREE language is agreement of *all* pairs of on-tier symbols,
not just the tier-adjacent ones. -/
theorem mem_agree_lang_iff_forall_sublist_pair [DecidableEq α] (p : α → Prop)
    [DecidablePred p] (w : List α) :
    w ∈ (TSLGrammar.agree p).lang ↔ ∀ a b, [a, b] <+ w → p a → p b → a = b := by
  rw [TSLGrammar.agree, mem_ofForbiddenPairs_lang_iff_filter_isChain]
  simp only [ne_eq, not_not]
  rw [List.isChain_iff_pairwise, List.pairwise_iff_forall_sublist]
  refine ⟨fun h a b hab ha hb => h (by simpa [ha, hb] using hab.filter fun x => decide (p x)),
    fun h a b hab => h a b (hab.trans List.filter_sublist) ?_ ?_⟩
  · exact of_decide_eq_true (List.mem_filter.mp (hab.mem List.mem_cons_self)).2
  · exact of_decide_eq_true
      (List.mem_filter.mp (hab.mem (List.mem_cons_of_mem _ List.mem_cons_self))).2

/-- **AGREE-TSL_2 = AGREE-SP_2**: the tier-based and subsequence-based descriptions of
agreement generate the same language, for any tier predicate. -/
theorem TSLGrammar.agree_lang_eq_sp [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    (TSLGrammar.agree p).lang = (SPGrammar.agree p).language 2 :=
  Set.ext fun w => (mem_agree_lang_iff_forall_sublist_pair p w).trans
    ⟨fun h s _ hs a b hab ha hb => h a b (hab ▸ hs) ha hb,
      fun h a b hab => h [a, b] (by simp) hab a b rfl⟩

/-- Every AGREE language is strictly 2-piecewise. -/
theorem TSLGrammar.agree_lang_isStrictlyPiecewise [DecidableEq α] (p : α → Prop)
    [DecidablePred p] : ((TSLGrammar.agree p).lang).IsStrictlyPiecewise 2 :=
  Language.isStrictlyPiecewise_iff.mpr ⟨SPGrammar.agree p, (TSLGrammar.agree_lang_eq_sp p).symm⟩

end Piecewise

end Subregular
