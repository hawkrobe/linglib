/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Theories.Phonology.OptimalityTheory.Constraints
import Linglib.Core.Computability.Subregular.ForbiddenPairs

/-!
# Bridge: Forbidden-Pair Markedness ↔ TSL_2

The single generic bridge connecting Optimality-theoretic forbidden-pair
markedness constraints (`mkForbidPairsOnTier`, defined in
`OptimalityTheory/Constraints.lean`) to tier-based strictly 2-local
languages (`TSLGrammar.ofForbiddenPairs`, defined in
`Core/Computability/Subregular/ForbiddenPairs.lean`).

A candidate's `mkForbidPairsOnTier` score is zero iff its raw string
belongs to the corresponding TSL_2 language — for any choice of
forbidden-pair relation `R`. The OCP-specific specialization (with
`R := (· = ·)`) lives in `Subregular/OCP.lean` and is now a one-line
corollary.
-/

namespace Phonology.Subregular

open Phonology.Constraints
open Core Core.Computability.Subregular

variable {α : Type}

/-- `countAdjacent R xs = 0` iff no two consecutive elements of `xs` are
related by `R`. The chain-form characterization of zero-violation
forbidden-pair candidates. -/
lemma countAdjacent_eq_zero_iff_isChain (R : α → α → Prop) [DecidableRel R]
    (xs : List α) :
    countAdjacent R xs = 0 ↔ xs.IsChain (fun a b => ¬ R a b) := by
  induction xs with
  | nil => exact ⟨fun _ => List.isChain_nil, fun _ => rfl⟩
  | cons a rest ih =>
    cases rest with
    | nil => exact ⟨fun _ => List.isChain_singleton _, fun _ => rfl⟩
    | cons b rest' =>
      show (if R a b then 1 else 0) + countAdjacent R (b :: rest') = 0 ↔ _
      rw [List.isChain_cons_cons]
      by_cases hRab : R a b
      · simp [hRab]
      · simp [hRab, ih]

/-- **Bridge** (relational form): a candidate's forbidden-pair score is zero
iff its raw string projects (under `Tier.byClass p`) to a list with no
two adjacent elements related by `R`. The chain-side payoff of the
generic forbidden-pair design. -/
theorem mkForbidPairsOnTier_zero_iff_isChain {C : Type} (name : String)
    (R : α → α → Prop) [DecidableRel R] (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkForbidPairsOnTier name R (Tier.byClass p) extract).eval c = 0 ↔
      ((extract c).filter (fun x => decide (p x))).IsChain (fun a b => ¬ R a b) := by
  show countAdjacent R (Tier.apply (Tier.byClass p) (extract c)) = 0 ↔ _
  rw [Tier.apply_byClass]
  exact countAdjacent_eq_zero_iff_isChain _ _

/-- **Bridge** (TSL_2 language form): a candidate's forbidden-pair score is
zero iff its raw string is in the language of
`TSLGrammar.ofForbiddenPairs R p`. The single generic bridge that every
adjacency-based markedness constraint inherits. Composes the relational
bridge `mkForbidPairsOnTier_zero_iff_isChain` with the carrier-level
language characterization `mem_ofForbiddenPairs_lang_iff_filter_isChain`. -/
theorem mkForbidPairsOnTier_zero_iff_in_lang {C : Type} (name : String)
    (R : α → α → Prop) [DecidableRel R] (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkForbidPairsOnTier name R (Tier.byClass p) extract).eval c = 0 ↔
      extract c ∈ (TSLGrammar.ofForbiddenPairs R p).lang := by
  rw [mkForbidPairsOnTier_zero_iff_isChain,
      mem_ofForbiddenPairs_lang_iff_filter_isChain]

end Phonology.Subregular
