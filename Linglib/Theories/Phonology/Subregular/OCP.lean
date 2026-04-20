/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Theories.Phonology.OptimalityTheory.Constraints
import Linglib.Theories.Phonology.Subregular.TierProjection

/-!
# Bridge: OCP (Obligatory Contour Principle) ↔ TSL_2

The OCP @cite{leben-1973} @cite{goldsmith-1976} is the prototypical
phonological constraint enforcing dissimilarity between adjacent elements on a
designated tier. Optimality theory expresses it as a markedness constraint
penalizing each adjacent identical pair (`mkOCPOnTier` in
`OptimalityTheory/Constraints.lean`); subregular complexity theory expresses
it as a tier-based strictly 2-local language @cite{heinz-rawal-tabor-2011}
@cite{lambert-2022} forbidding the 2-factor `[some x, some x]` for any
non-boundary symbol `x`.

This file shows the two are co-extensive: a candidate's OCP score is zero iff
its raw string is in the corresponding TSL_2 language. Establishing the
bridge has two payoffs — every OCP-style markedness constraint inherits the
subregular complexity classification, and every TSL_2 grammar of this
"no-adjacent-identical" form can be plugged into an OT/HG ranking as a
ready-made markedness constraint.
-/

namespace Phonology.Subregular

open Phonology.Constraints
open Core Core.Computability.Subregular

-- `α : Type` (rather than `Type*`) is forced by `Phonology.Constraints`
-- and `Core.Constraint.eval`, which are monomorphic in universe 0.
variable {α : Type}

/-- Forbidden 2-factors for the OCP: pairs `[some x, some x]` of two identical
non-boundary symbols. Boundary-adjacent factors `[none, some x]` and
`[some x, none]` are never forbidden — the OCP penalizes only interior
adjacent identicals. -/
def ocpForbidden (α : Type) : Set (Augmented α) :=
  { f | ∃ x : α, f = [some x, some x] }

/-- The TSL_2 grammar capturing "no two adjacent identical symbols on the
tier defined by the predicate `p`". This is the OCP @cite{leben-1973}
@cite{goldsmith-1976} expressed as a tier-based subregular language: tier
projection (via `Tier.byClass p`) followed by the SL_2 ban on `[some x, some x]`
substrings. -/
def TSLGrammar.ocp (p : α → Prop) [DecidablePred p] : TSLGrammar 2 α where
  tier := p
  permitted := (ocpForbidden α)ᶜ

/-- `adjacentIdentical xs = 0` iff no two consecutive elements of `xs` are
equal. Reformulates the OCP's 0-violation condition as the mathlib-idiomatic
relational chain `List.IsChain (· ≠ ·)`. -/
lemma adjacentIdentical_eq_zero_iff_isChain
    [BEq α] [LawfulBEq α] (xs : List α) :
    adjacentIdentical xs = 0 ↔ xs.IsChain (· ≠ ·) := by
  induction xs with
  | nil => exact ⟨fun _ => List.isChain_nil, fun _ => rfl⟩
  | cons a rest ih =>
    cases rest with
    | nil => exact ⟨fun _ => List.isChain_singleton _, fun _ => rfl⟩
    | cons b rest' =>
      show (if a == b then 1 else 0) + adjacentIdentical (b :: rest') = 0 ↔ _
      rw [List.isChain_cons_cons]
      by_cases hab : a = b
      · subst hab
        simp
      · have hbeq : (a == b) = false := by simp [hab]
        rw [hbeq]
        simp [ih, hab]

/-- **Bridge**: a candidate's OCP score is zero iff its raw string projects
(under `Tier.byClass p`) to a list with no two adjacent identical elements.
This is the relational/chain side of the OCP-as-TSL_2 correspondence; the
full language characterization (`mkOCPOnTier_zero_iff_in_ocp_lang`) layers
the boundary/kFactors decomposition on top. -/
theorem mkOCPOnTier_zero_iff_isChain [BEq α] [LawfulBEq α] {C : Type}
    (name : String) (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkOCPOnTier name (Tier.byClass p) extract).eval c = 0 ↔
      ((extract c).filter (fun x => decide (p x))).IsChain (· ≠ ·) := by
  show adjacentIdentical (Tier.apply (Tier.byClass p) (extract c)) = 0 ↔ _
  rw [Tier.apply_byClass]
  exact adjacentIdentical_eq_zero_iff_isChain _

-- ---- Language-form bridge ------------------------------------------------

/-- The OCP relation on `Option α`: two augmented symbols are *OCP-clean as
a pair* iff they are not both `some` of the same value. Boundary symbols
are vacuously admitted on either side, so this is `IsBoundaryVacuous`
(`OCPCleanPair.isBoundaryVacuous`).

Used as the chain relation characterizing OCP-clean strings:
`xs.IsChain OCPCleanPair` iff no two adjacent `some` symbols of `xs`
are identical. -/
def OCPCleanPair : Option α → Option α → Prop
  | some a, some b => a ≠ b
  | _, _ => True

@[simp] lemma ocpCleanPair_none_left (u : Option α) :
    OCPCleanPair (none : Option α) u := by cases u <;> exact True.intro

@[simp] lemma ocpCleanPair_none_right (u : Option α) :
    OCPCleanPair u (none : Option α) := by cases u <;> exact True.intro

lemma ocpCleanPair_some_some (a b : α) :
    OCPCleanPair (some a) (some b) ↔ a ≠ b := Iff.rfl

/-- The OCP relation is boundary-vacuous: `none` always satisfies it on
either side. Inherits the generic chain-on-boundary lemmas from
`Core.Computability.Subregular.IsBoundaryVacuous`. -/
lemma OCPCleanPair.isBoundaryVacuous :
    IsBoundaryVacuous (OCPCleanPair (α := α)) :=
  ⟨ocpCleanPair_none_left, ocpCleanPair_none_right⟩

/-- A list of `Option α` has no `[some x, some x]` 2-factor iff it is a
chain for `OCPCleanPair`. The factor-membership/chain-membership bridge:
`OCPCleanPair a b` is by definition `[a, b] ∉ ocpForbidden α`. -/
lemma forall_kFactors_two_not_ocpForbidden_iff_isChain (xs : List (Option α)) :
    (∀ f ∈ kFactors 2 xs, f ∉ ocpForbidden α) ↔
      xs.IsChain OCPCleanPair := by
  induction xs with
  | nil =>
    refine ⟨fun _ => List.isChain_nil, ?_⟩
    intro _ f hf
    simp [kFactors] at hf
  | cons a rest ih =>
    cases rest with
    | nil =>
      refine ⟨fun _ => List.isChain_singleton _, ?_⟩
      intro _ f hf
      simp [kFactors] at hf
    | cons b rest' =>
      rw [kFactors_two_cons_cons, List.forall_mem_cons, List.isChain_cons_cons,
          ih]
      refine and_congr_left' ?_
      constructor
      · intro h1
        cases a with
        | none => exact ocpCleanPair_none_left _
        | some a' =>
          cases b with
          | none => exact ocpCleanPair_none_right _
          | some b' =>
            rw [ocpCleanPair_some_some]
            intro hab
            exact h1 ⟨a', by rw [hab]⟩
      · intro h1
        rintro ⟨z, hz⟩
        simp only [List.cons.injEq, and_true] at hz
        obtain ⟨rfl, rfl⟩ := hz
        exact h1 rfl

/-- The OCP-language membership reduces to an `IsChain (· ≠ ·)` check on the
projected string. Composes (i) the factor/chain bridge
`forall_kFactors_two_not_ocpForbidden_iff_isChain`, (ii) the boundary-vacuity
of `OCPCleanPair`, and (iii) `List.isChain_map` to drop the `some`. -/
lemma mem_ocp_lang_iff_filter_isChain (p : α → Prop) [DecidablePred p]
    (w : List α) :
    w ∈ (TSLGrammar.ocp p).lang ↔
      (w.filter (fun x => decide (p x))).IsChain (· ≠ ·) := by
  rw [TSLGrammar.mem_lang]
  simp only [TSLGrammar.ocp, Set.mem_compl_iff]
  rw [forall_kFactors_two_not_ocpForbidden_iff_isChain,
      OCPCleanPair.isBoundaryVacuous.isChain_boundary_two_iff,
      tierProject_eq_filter, List.isChain_map]
  rfl

/-- **Bridge** (full TSL_2 language form): a candidate's OCP score is zero iff
its raw string is in the language of the TSL_2 grammar `TSLGrammar.ocp p`.
The two perspectives on the OCP — optimality-theoretic constraint and
subregular-complexity class — are co-extensive. Composes the relational
bridge `mkOCPOnTier_zero_iff_isChain` with the carrier-level language
characterisation `mem_ocp_lang_iff_filter_isChain`. -/
theorem mkOCPOnTier_zero_iff_in_ocp_lang [BEq α] [LawfulBEq α] {C : Type}
    (name : String) (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkOCPOnTier name (Tier.byClass p) extract).eval c = 0 ↔
      extract c ∈ (TSLGrammar.ocp p).lang := by
  rw [mkOCPOnTier_zero_iff_isChain, mem_ocp_lang_iff_filter_isChain]

end Phonology.Subregular
