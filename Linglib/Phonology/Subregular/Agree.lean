/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.StrictlyPiecewise
public import Linglib.Phonology.OptimalityTheory.Constraint.ForbiddenPairs

/-!
# AGREE as a tier-based strictly 2-local language

This file characterizes AGREE-style markedness as a tier-based strictly 2-local (TSL₂) language.
AGREE requires tier-adjacent symbols to be equal, so it is the dual of the OCP, which requires them
to differ. Both specialize the forbidden-pair constraint `Constraint.forbidPairs` of
`OptimalityTheory/Constraint/ForbiddenPairs.lean`, AGREE with `R := (· ≠ ·)` and the OCP with
`R := (· = ·)`. Consonant harmony, vowel harmony, and tone spreading factor through
`TierStrictlyLocalGrammar.agree`, while dissimilation, anti-gemination, and Meeussen's rule factor
through `TierStrictlyLocalGrammar.ocp`, and asymmetric patterns instantiate the generic constructor
with their own relation.

Because equality is transitive, AGREE is also strictly piecewise, and the tier projection is
dispensable. So is any forbidden-pair grammar whose permitted pairs are transitive on the tier,
such as agreement in a feature value. This lets transparent long-distance harmony be described
either way, as McMullin observes, whereas the OCP has no such reading.

## Main definitions

* `agreeForbidden`, `AgreeCleanPair`, `TierStrictlyLocalGrammar.agree`: the AGREE instances of
  the forbidden-pair constructions.
* `StrictlyPiecewiseGrammar.ofForbiddenPairs`, `StrictlyPiecewiseGrammar.agree`: the strictly
  2-piecewise grammars banning a pair of on-tier symbols however far apart.

## Main results

* `Constraint.zeroSet_comap_filter_agree`: on a tier, the zero set of the AGREE constraint is
  the language of `TierStrictlyLocalGrammar.agree`.
* `TierStrictlyLocalGrammar.ofForbiddenPairs_language_eq_sp`: when the permitted pairs are
  transitive on the tier, the tier-based and subsequence-based grammars generate the same
  language; `TierStrictlyLocalGrammar.agree_language_eq_sp` is the AGREE instance.

## References

* [mcmullin-2016]
-/

@[expose] public section

namespace Subregular

variable {α : Type*}

/-- The forbidden 2-factors for AGREE are the pairs `[some x, some y]` of two distinct
non-boundary symbols, the inequality instance of `forbiddenPairs`. -/
def agreeForbidden (α : Type*) [DecidableEq α] : Set (Augmented α) :=
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
    AgreeCleanPair (some a) (some b) ↔ a = b :=
  (CleanPair.some_some a b).trans not_not

/-- The AGREE relation is boundary-vacuous, the inequality instance of
`CleanPair.isBoundaryVacuous`. -/
lemma AgreeCleanPair.isBoundaryVacuous [DecidableEq α] :
    IsBoundaryVacuous (AgreeCleanPair (α := α)) :=
  CleanPair.isBoundaryVacuous

/-! ### Transitive agreement is strictly piecewise

When the permitted pairs `¬ R` are transitive on the tier, "every tier-*adjacent* pair is
permitted" and "every pair of on-tier symbols is permitted, however far apart" are the same
condition. The latter reads subsequences, which are blind to the intervening material the tier
projection deletes, so the language is SP₂ as well as TSL₂. Equality is transitive, so AGREE
languages are SP₂ ([mcmullin-2016]), as is agreement in any feature value. The OCP has no such
reading, since `≠` is not transitive. -/

section Piecewise

open List

/-- The SP₂ grammar dual to `TierStrictlyLocalGrammar.ofForbiddenPairs R p` permits every
subsequence except an `R`-related pair of on-tier symbols, and permits shorter subsequences
outright. -/
def StrictlyPiecewiseGrammar.ofForbiddenPairs (R : α → α → Prop) (p : α → Prop) :
    StrictlyPiecewiseGrammar α :=
  {s | ∀ a b, s = [a, b] → p a → p b → ¬ R a b}

/-- The SP₂ grammar dual to `TierStrictlyLocalGrammar.agree p` permits every subsequence except
a pair of disagreeing on-tier symbols. -/
def StrictlyPiecewiseGrammar.agree (p : α → Prop) : StrictlyPiecewiseGrammar α :=
  StrictlyPiecewiseGrammar.ofForbiddenPairs (· ≠ ·) p

section Transitive

variable {R : α → α → Prop} {p : α → Prop} [DecidablePred p]
  (hR : ∀ a b c, p a → p b → p c → ¬ R a b → ¬ R b c → ¬ R a c)
include hR

/-- If the permitted pairs are transitive on the tier, membership is permission of *all* pairs
of on-tier symbols, not just the tier-adjacent ones. -/
theorem mem_ofForbiddenPairs_language_iff_forall_sublist_pair (w : List α) :
    w ∈ (TierStrictlyLocalGrammar.ofForbiddenPairs R p).language ↔
      ∀ a b, [a, b] <+ w → p a → p b → ¬ R a b := by
  rw [mem_ofForbiddenPairs_language_iff_filter_isChain]
  have hp : ∀ x ∈ w.filter (p ·), p x := fun x hx ↦ of_decide_eq_true (mem_filter.mp hx).2
  have hchain : (w.filter (p ·)).IsChain (¬ R · ·) ↔ (w.filter (p ·)).Pairwise (¬ R · ·) := by
    refine ⟨fun h ↦ ?_, Pairwise.isChain⟩
    have : IsTrans (Subtype p) (fun x y ↦ ¬ R x y) := ⟨fun a b c ↦ hR a b c a.2 b.2 c.2⟩
    rw [← unattach_attachWith (p := p) (H := hp), unattach, isChain_map] at h
    rw [← unattach_attachWith (p := p) (H := hp), unattach, pairwise_map]
    exact h.pairwise
  rw [hchain, pairwise_iff_forall_sublist]
  refine ⟨fun h a b hab ha hb ↦ h (by simpa [ha, hb] using hab.filter fun x ↦ decide (p x)),
    fun h a b hab ↦ h a b (hab.trans filter_sublist) ?_ ?_⟩
  · exact hp a (hab.mem mem_cons_self)
  · exact hp b (hab.mem (mem_cons_of_mem _ mem_cons_self))

/-- The tier-based and subsequence-based descriptions generate the same language when the
permitted pairs are transitive on the tier. -/
theorem TierStrictlyLocalGrammar.ofForbiddenPairs_language_eq_sp :
    (TierStrictlyLocalGrammar.ofForbiddenPairs R p).language =
      (StrictlyPiecewiseGrammar.ofForbiddenPairs R p).language 2 :=
  Set.ext fun w ↦ (mem_ofForbiddenPairs_language_iff_forall_sublist_pair hR w).trans
    ⟨fun h s _ hs a b hab ha hb ↦ h a b (hab ▸ hs) ha hb,
      fun h a b hab ↦ h [a, b] (by simp) hab a b rfl⟩

theorem TierStrictlyLocalGrammar.ofForbiddenPairs_language_isStrictlyPiecewise :
    (TierStrictlyLocalGrammar.ofForbiddenPairs R p).language.IsStrictlyPiecewise 2 :=
  Language.isStrictlyPiecewise_iff.mpr ⟨_, (ofForbiddenPairs_language_eq_sp hR).symm⟩

end Transitive

private theorem not_ne_trans {p : α → Prop} (a b c : α) (_ : p a) (_ : p b) (_ : p c)
    (hab : ¬ a ≠ b) (hbc : ¬ b ≠ c) : ¬ a ≠ c :=
  not_ne_iff.2 ((not_ne_iff.1 hab).trans (not_ne_iff.1 hbc))

section Agree

variable [DecidableEq α] (p : α → Prop) [DecidablePred p]

/-- Membership in the AGREE language is agreement of *all* pairs of on-tier symbols,
not just the tier-adjacent ones. -/
theorem mem_agree_lang_iff_forall_sublist_pair (w : List α) :
    w ∈ (TierStrictlyLocalGrammar.agree p).language ↔ ∀ a b, [a, b] <+ w → p a → p b → a = b :=
  (mem_ofForbiddenPairs_language_iff_forall_sublist_pair not_ne_trans w).trans <| by
    simp only [ne_eq, not_not]

/-- The tier-based and subsequence-based descriptions of agreement generate the same language,
for any tier predicate. -/
theorem TierStrictlyLocalGrammar.agree_language_eq_sp :
    (TierStrictlyLocalGrammar.agree p).language = (StrictlyPiecewiseGrammar.agree p).language 2 :=
  ofForbiddenPairs_language_eq_sp not_ne_trans

/-- Every AGREE language is strictly 2-piecewise. -/
theorem TierStrictlyLocalGrammar.agree_language_isStrictlyPiecewise :
    ((TierStrictlyLocalGrammar.agree p).language).IsStrictlyPiecewise 2 :=
  ofForbiddenPairs_language_isStrictlyPiecewise not_ne_trans

end Agree

end Piecewise

end Subregular

namespace OptimalityTheory.Constraint

variable {α : Type*} [DecidableEq α]

/-- A string satisfies AGREE iff its adjacent elements are equal, so that all its elements are
equal. -/
theorem agree_eq_zero_iff (w : List α) : agree w = 0 ↔ w.IsChain (· = ·) :=
  (forbidPairs_eq_zero_iff (· ≠ ·) w).trans (by simp only [ne_eq, not_not])

/-- On the tier `p`, the zero set of AGREE is the language of the TSL₂ grammar
`TierStrictlyLocalGrammar.agree p`, so the optimality-theoretic constraint and the subregular
class are co-extensive. -/
theorem zeroSet_comap_filter_agree (p : α → Prop) [DecidablePred p] :
    (agree.comap fun w ↦ w.filter (p ·)).zeroSet =
      (Subregular.TierStrictlyLocalGrammar.agree p).language :=
  zeroSet_comap_filter_forbidPairs (· ≠ ·) p

end OptimalityTheory.Constraint

