/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.StrictlyPiecewise
public import Linglib.Phonology.Subregular.ForbidPairs
public import Linglib.Phonology.Subregular.TierProjection

/-!
# AGREE as a tier-based strictly 2-local language

This file characterizes AGREE-style markedness as a tier-based strictly 2-local (TSL₂) language.
AGREE requires tier-adjacent symbols to be equal, so it is the dual of the OCP, which requires
them to differ. Both specialize the forbidden-pair constructor `mkForbidPairsOnTier` of
`ForbidPairs.lean`, AGREE with `R := (· ≠ ·)` and the OCP with `R := (· = ·)`. Consonant harmony,
vowel harmony, and tone spreading factor through `TierStrictlyLocalGrammar.agree`, while
dissimilation, anti-gemination, and Meeussen's rule factor through `TierStrictlyLocalGrammar.ocp`,
and asymmetric patterns instantiate the generic constructor with their own relation.

Because equality is transitive, AGREE is also strictly piecewise, and the tier projection is
dispensable. This lets transparent long-distance harmony be described either way, as McMullin
observes, whereas the OCP has no such reading.

## Main definitions

* `agreeForbidden`, `AgreeCleanPair`, `TierStrictlyLocalGrammar.agree`: the AGREE instances of
  the forbidden-pair constructions.
* `StrictlyPiecewiseGrammar.agree`: the strictly 2-piecewise grammar of AGREE.

## Main results

* `mkAgreeOnTier_zero_iff_in_agree_language`: the AGREE constraint scores zero exactly on the
  language of `TierStrictlyLocalGrammar.agree`.
* `TierStrictlyLocalGrammar.agree_language_eq_sp`: the tier-based and subsequence-based
  grammars of AGREE generate the same language.

## References

* [K. J. McMullin, *Tier-based locality in long-distance phonotactics: Learnability and
  typology* (2016)][mcmullin-2016]
-/

@[expose] public section

namespace Subregular

open Constraints OptimalityTheory

-- `α : Type` (rather than `Type*`) is forced by `OptimalityTheory`, which is monomorphic in
-- universe 0. See the parallel comment in `OCP.lean`.
variable {α : Type}

/-- The forbidden 2-factors for AGREE are the pairs `[some x, some y]` of two distinct
non-boundary symbols, the inequality instance of `forbiddenPairs`. -/
def agreeForbidden (α : Type) [DecidableEq α] : Set (Augmented α) :=
  forbiddenPairs (α := α) (· ≠ ·)

/-- The TSL₂ grammar of AGREE forbids two adjacent distinct symbols on the tier defined by `p`,
so every tier-adjacent pair agrees. It is the inequality instance of
`TierStrictlyLocalGrammar.ofForbiddenPairs`. -/
def TierStrictlyLocalGrammar.agree [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    TierStrictlyLocalGrammar 2 α :=
  TierStrictlyLocalGrammar.ofForbiddenPairs (α := α) (· ≠ ·) p

/-- Two augmented symbols are *AGREE-clean as a pair* iff they are not both `some` of distinct
values. This is the inequality instance of `CleanPair`. -/
def AgreeCleanPair [DecidableEq α] : Option α → Option α → Prop :=
  CleanPair (α := α) (· ≠ ·)

lemma agreeCleanPair_some_some [DecidableEq α] (a b : α) :
    AgreeCleanPair (some a) (some b) ↔ a = b := by
  rw [show AgreeCleanPair (some a) (some b) ↔ ¬ a ≠ b from
        CleanPair.some_some a b]
  exact not_not

/-- The AGREE relation is boundary-vacuous, the inequality instance of
`CleanPair.isBoundaryVacuous`. -/
lemma AgreeCleanPair.isBoundaryVacuous [DecidableEq α] :
    IsBoundaryVacuous (AgreeCleanPair (α := α)) :=
  CleanPair.isBoundaryVacuous

/-- A candidate's AGREE score is zero iff its raw string projects under
`TierProjection.byClass p` to a list with no two adjacent distinct elements, so that all on-tier
elements are equal. This is the inequality instance of `mkForbidPairsOnTier_zero_iff_isChain`. -/
theorem mkAgreeOnTier_zero_iff_isChain [DecidableEq α] {C : Type}
    (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkAgreeOnTier (TierProjection.byClass p) extract) c = 0 ↔
      ((extract c).filter (fun x => decide (p x))).IsChain (fun a b => ¬ a ≠ b) :=
  mkForbidPairsOnTier_zero_iff_isChain (· ≠ ·) p extract c

/-- A candidate's AGREE score is zero iff its raw string lies in the language of the TSL₂
grammar `TierStrictlyLocalGrammar.agree p`, so the optimality-theoretic constraint and the
subregular class are co-extensive. This is the inequality instance of
`mkForbidPairsOnTier_zero_iff_in_language`. -/
theorem mkAgreeOnTier_zero_iff_in_agree_language [DecidableEq α] {C : Type}
    (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkAgreeOnTier (TierProjection.byClass p) extract) c = 0 ↔
      extract c ∈ (TierStrictlyLocalGrammar.agree p).language :=
  mkForbidPairsOnTier_zero_iff_in_language (· ≠ ·) p extract c

/-- The zero set of the AGREE markedness constraint is the corresponding TSL₂ language. This
restates `mkAgreeOnTier_zero_iff_in_agree_language` in `Language α` form, with `extract := id`,
as `mkOCPOnTier_zeroSet_eq` does for the OCP. -/
theorem mkAgreeOnTier_zeroSet_eq [DecidableEq α]
    (p : α → Prop) [DecidablePred p] :
    (mkAgreeOnTier (TierProjection.byClass p) (id : List α → List α)).zeroSet =
      (TierStrictlyLocalGrammar.agree p).language := by
  ext w
  exact mkAgreeOnTier_zero_iff_in_agree_language p id w

/-! ### AGREE is also strictly piecewise

Equality is transitive, so "every tier-*adjacent* pair agrees" and "every pair of on-tier
symbols agrees, however far apart" are the same condition. The latter reads subsequences, which
are blind to the intervening material the tier projection deletes, so AGREE languages are SP₂ as
well as TSL₂ ([mcmullin-2016]). The OCP has no such reading, since `≠` is not transitive. -/

section Piecewise

open List

/-- The SP₂ grammar dual to `TierStrictlyLocalGrammar.agree p` permits every subsequence except
a pair of disagreeing on-tier symbols, and permits shorter subsequences outright. -/
def StrictlyPiecewiseGrammar.agree {α : Type*} (p : α → Prop) : StrictlyPiecewiseGrammar α :=
  {s | ∀ a b, s = [a, b] → p a → p b → a = b}

/-- Membership in the AGREE language is agreement of *all* pairs of on-tier symbols,
not just the tier-adjacent ones. -/
theorem mem_agree_lang_iff_forall_sublist_pair [DecidableEq α] (p : α → Prop)
    [DecidablePred p] (w : List α) :
    w ∈ (TierStrictlyLocalGrammar.agree p).language ↔ ∀ a b, [a, b] <+ w → p a → p b → a = b := by
  rw [TierStrictlyLocalGrammar.agree, mem_ofForbiddenPairs_language_iff_filter_isChain]
  simp only [ne_eq, not_not]
  rw [List.isChain_iff_pairwise, List.pairwise_iff_forall_sublist]
  refine ⟨fun h a b hab ha hb => h (by simpa [ha, hb] using hab.filter fun x => decide (p x)),
    fun h a b hab => h a b (hab.trans List.filter_sublist) ?_ ?_⟩
  · exact of_decide_eq_true (List.mem_filter.mp (hab.mem List.mem_cons_self)).2
  · exact of_decide_eq_true
      (List.mem_filter.mp (hab.mem (List.mem_cons_of_mem _ List.mem_cons_self))).2

/-- The tier-based and subsequence-based descriptions of agreement generate the same language,
for any tier predicate. -/
theorem TierStrictlyLocalGrammar.agree_language_eq_sp [DecidableEq α] (p : α → Prop)
    [DecidablePred p] :
    (TierStrictlyLocalGrammar.agree p).language = (StrictlyPiecewiseGrammar.agree p).language 2 :=
  Set.ext fun w => (mem_agree_lang_iff_forall_sublist_pair p w).trans
    ⟨fun h s _ hs a b hab ha hb => h a b (hab ▸ hs) ha hb,
      fun h a b hab => h [a, b] (by simp) hab a b rfl⟩

/-- Every AGREE language is strictly 2-piecewise. -/
theorem TierStrictlyLocalGrammar.agree_language_isStrictlyPiecewise [DecidableEq α] (p : α → Prop)
    [DecidablePred p] : ((TierStrictlyLocalGrammar.agree p).language).IsStrictlyPiecewise 2 :=
  Language.isStrictlyPiecewise_iff.mpr
    ⟨StrictlyPiecewiseGrammar.agree p, (TierStrictlyLocalGrammar.agree_language_eq_sp p).symm⟩

end Piecewise

end Subregular
