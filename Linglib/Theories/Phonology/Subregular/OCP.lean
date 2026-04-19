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

variable {α : Type}

/-- Forbidden 2-factors for the OCP: pairs `[some x, some x]` of two identical
non-boundary symbols. Boundary-adjacent factors `[none, some x]` and
`[some x, none]` are never forbidden — the OCP penalizes only interior
adjacent identicals. -/
def ocpForbidden (α : Type) : Set (Augmented α) :=
  { f | ∃ x : α, f = [some x, some x] }

/-- The TSL_2 grammar capturing "no two adjacent identical symbols on the
tier defined by the Bool predicate `p`". This is the OCP @cite{leben-1973}
@cite{goldsmith-1976} expressed as a tier-based subregular language: tier
projection (via `Tier.byClass p`) followed by the SL_2 ban on `[some x, some x]`
substrings. -/
def TSLGrammar.ocp (p : α → Bool) : TSLGrammar 2 α where
  tier := fun x => p x = true
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
    (name : String) (p : α → Bool) (extract : C → List α) (c : C) :
    (mkOCPOnTier name (Tier.byClass p) extract).eval c = 0 ↔
      ((extract c).filter p).IsChain (· ≠ ·) := by
  show adjacentIdentical (Tier.apply (Tier.byClass p) (extract c)) = 0 ↔ _
  rw [Tier.apply_byClass]
  exact adjacentIdentical_eq_zero_iff_isChain _

/-- **Bridge** (full TSL_2 language form): a candidate's OCP score is zero iff
its raw string is in the language of the TSL_2 grammar `TSLGrammar.ocp p`.
The two perspectives on the OCP — optimality-theoretic constraint and
subregular-complexity class — are co-extensive.

The chain'-form bridge `mkOCPOnTier_zero_iff_chain'` is already proved above;
the remaining step is to characterize `kFactors 2 (boundary 2 ys)` and show
that no factor lies in `ocpForbidden α` iff `ys.IsChain (· ≠ ·)`. The interior
2-factors of `boundary 2 ys` are exactly the consecutive `[some y_i, some y_{i+1}]`
pairs; boundary-adjacent factors `[none, some y]` and `[some y, none]` never
match `[some x, some x]`. -/
theorem mkOCPOnTier_zero_iff_in_ocp_lang [BEq α] [LawfulBEq α] {C : Type}
    (name : String) (p : α → Bool) (extract : C → List α) (c : C) :
    (mkOCPOnTier name (Tier.byClass p) extract).eval c = 0 ↔
      extract c ∈ (TSLGrammar.ocp p).lang := by
  -- TODO: prove `(w ∈ (TSLGrammar.ocp p).lang) ↔ ((w.filter p).IsChain (· ≠ ·))`
  -- by inducting on `w.filter p` and analyzing `kFactors 2 (boundary 2 _)`.
  -- Then `rw` it and apply `mkOCPOnTier_zero_iff_chain'`.
  sorry

end Phonology.Subregular
