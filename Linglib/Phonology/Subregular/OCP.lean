/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Subregular.ForbidPairs
import Linglib.Core.Computability.TierProjection
import Linglib.Phonology.OCP
import Linglib.Core.Computability.Subregular.Function.ISL

/-!
# OCP (Obligatory Contour Principle) ↔ TSL_2 — the identity instance

The OCP [goldsmith-1976] [mccarthy-1986] is the identity-relation
instance of the generic forbidden-pair markedness constructor
`mkForbidPairsOnTier` (see `ForbidPairs.lean`): the forbidden 2-factor is
`[some x, some x]`, and the corresponding TSL_2 grammar is
`TSLGrammar.ofForbiddenPairs (· = ·) p`.

Mathematically, the unprojected (single-tier, full-alphabet) case is the
linguistic instance of the classical theory of *square-free words*
[thue-1906]: a word is OCP-clean iff it contains no factor `x x`.
Thue's construction shows infinite square-free words exist over a
3-letter alphabet, while every binary string of length ≥ 4 contains a
square — i.e. binary tonal alphabets cannot satisfy a strict OCP at
length, which is itself a phonological prediction.

Everything in this file is a one-line specialization of the generic
forbidden-pair infrastructure to `R := (· = ·)`. The OCP-specific names
(`ocpForbidden`, `OCPCleanPair`, `TSLGrammar.ocp`,
`mkOCPOnTier_zero_iff_in_ocp_lang`) are kept as the canonical entry
points downstream consumers reference.

## The subregular face of the OCP

This file is the **subregular characterization** of the OCP — one face of the
unified `OCP` principle. It proves that the prohibition reading (a
stringset rejecting adjacent identical tier-projected autosegments) is a TSL₂
language, and that its satisfaction predicate is exactly `OCP.IsClean`
(`mkOCPOnTier_zero_iff_isClean`). The dual fusion repair `OCP.collapse`
lands in the same `IsClean` set, and is itself a 2-Input-Strictly-Local map
(`collapse_isISL`) — so prohibition and merger are not two coexisting
formalisations but the constraint and a retraction onto it, both characterising
`OCP.IsClean`, both subregular.
-/

namespace Subregular

open Constraints OptimalityTheory

-- `α : Type` (rather than `Type*`) is forced by `OptimalityTheory`
-- and `Core.Optimization`, which are monomorphic in universe 0.
variable {α : Type}

/-- Forbidden 2-factors for the OCP: pairs `[some x, some x]` of two identical
non-boundary symbols. The identity-relation specialization of
`forbiddenPairs`. -/
def ocpForbidden (α : Type) [DecidableEq α] : Set (Augmented α) :=
  forbiddenPairs (α := α) (· = ·)

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
raw string projects (under `TierProjection.byClass p`) to a list with no two
adjacent identical elements. Identity-relation specialization of
`mkForbidPairsOnTier_zero_iff_isChain`. -/
theorem mkOCPOnTier_zero_iff_isChain [DecidableEq α] {C : Type}
    (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkOCPOnTier (TierProjection.byClass p) extract) c = 0 ↔
      ((extract c).filter (fun x => decide (p x))).IsChain (· ≠ ·) :=
  mkForbidPairsOnTier_zero_iff_isChain (· = ·) p extract c

/-- **Shared satisfaction predicate**: a candidate's OCP score is zero iff its
tier-projection is `OCP.IsClean`. This is what makes the prohibition
reading (here) and the fusion repair (`OCP.collapse`) two faces of
one principle rather than parallel formalisations — both characterise
`OCP.IsClean`. -/
theorem mkOCPOnTier_zero_iff_isClean [DecidableEq α] {C : Type}
    (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkOCPOnTier (TierProjection.byClass p) extract) c = 0 ↔
      OCP.IsClean ((extract c).filter (fun x => decide (p x))) :=
  mkOCPOnTier_zero_iff_isChain p extract c

/-- **Shared satisfaction predicate** (off-tier): the optimality-theoretic OCP
markedness constraint `mkOCP` scores zero iff its projection is
`OCP.IsClean` — routing `OptimalityTheory.adjacentIdentical` (the
`countAdjacent` form behind `mkOCP`, consumed by Berent2026/Belth2026) through the
unified predicate. The flat-string companion of `mkOCPOnTier_zero_iff_isClean`. -/
theorem mkOCP_zero_iff_isClean {C : Type} [DecidableEq α]
    (project : C → List α) (c : C) :
    (mkOCP project) c = 0 ↔ OCP.IsClean (project c) := by
  show countAdjacent (· = ·) (project c) = 0 ↔ _
  rw [countAdjacent_eq_zero_iff_isChain (· = ·)]

/-- **Bridge** (full TSL_2 language form): a candidate's OCP score is zero iff
its raw string is in the language of the TSL_2 grammar `TSLGrammar.ocp p`.
The two perspectives on the OCP — optimality-theoretic constraint and
subregular-complexity class — are co-extensive. Identity-relation
specialization of `mkForbidPairsOnTier_zero_iff_in_lang`. -/
theorem mkOCPOnTier_zero_iff_in_ocp_lang [DecidableEq α] {C : Type}
    (p : α → Prop) [DecidablePred p]
    (extract : C → List α) (c : C) :
    (mkOCPOnTier (TierProjection.byClass p) extract) c = 0 ↔
      extract c ∈ (TSLGrammar.ocp p).lang :=
  mkForbidPairsOnTier_zero_iff_in_lang (· = ·) p extract c

/-- **Zero-set bridge** (OCP on tier): the `Language α`-form restatement
of `mkOCPOnTier_zero_iff_in_ocp_lang` (with `extract := id`). The OCP
markedness constraint's zero-set *is* the corresponding OCP-TSL_2
language. Sibling of `mkForbidPairsOnTier_zeroSet_eq` in OTBound.lean. -/
theorem mkOCPOnTier_zeroSet_eq [DecidableEq α]
    (p : α → Prop) [DecidablePred p] :
    (mkOCPOnTier (TierProjection.byClass p) (id : List α → List α)).zeroSet =
      (TSLGrammar.ocp p).lang := by
  ext w
  exact mkOCPOnTier_zero_iff_in_ocp_lang p id w

/-! ### The repair is subregular -/

/-- The OCP fusion repair `OCP.collapse` is a **2-Input-Strictly-Local**
string function ([chandlee-heinz-2018]): scanning left-to-right with a one-symbol
window, delete a symbol iff it equals its predecessor. This completes the subregular
*repair* face (the constraint side is the TSL₂ result above); cf. the autosegmental
A-ISL classification of tonal OCP processes in [chandlee-jardine-2019]. -/
theorem collapse_isISL [DecidableEq α] :
    IsLeftInputStrictlyLocal 2 (OCP.collapse (α := α)) := by
  refine ⟨{ windowOutput := fun window x => if window = [x] then [] else [x] }, ?_⟩
  set r : ISLRule 2 α α :=
    { windowOutput := fun window x => if window = [x] then [] else [x] } with hr
  funext xs
  -- The window after reading one symbol is always the singleton of that symbol,
  -- so the rule emits `[]` exactly when the current symbol equals its predecessor.
  have key : ∀ (a : α) (rest : List α),
      a :: r.applyAux [a] rest = List.destutter' (· ≠ ·) a rest := by
    intro a rest
    induction rest generalizing a with
    | nil => simp [ISLRule.applyAux, List.destutter'_nil]
    | cons b l ih =>
      rw [ISLRule.applyAux_cons]
      have hwin : ([a] ++ [b]).rtake (2 - 1) = [b] := by
        simp [List.rtake]
      rw [hwin, List.destutter'_cons]
      show a :: ((if [a] = [b] then [] else [b]) ++ r.applyAux [b] l) = _
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, List.nil_append, if_neg (by simp : ¬ (a ≠ a))]
        exact ih a
      · rw [if_neg (by simpa using hab), if_pos (by simpa using hab)]
        rw [List.cons_append, List.nil_append]
        exact congrArg (a :: ·) (ih b)
  cases xs with
  | nil => simp [OCP.collapse]
  | cons x rest =>
    show r.applyAux [] (x :: rest) = OCP.collapse (x :: rest)
    rw [ISLRule.applyAux_cons]
    have hwin : ([] ++ [x]).rtake (2 - 1) = [x] := by
      simp [List.rtake]
    rw [hwin]
    show ((if ([] : List α) = [x] then [] else [x]) ++ r.applyAux [x] rest) = _
    rw [if_neg (by simp), List.cons_append, List.nil_append]
    rw [OCP.collapse_eq_destutter, List.destutter_cons']
    exact key x rest

end Subregular
