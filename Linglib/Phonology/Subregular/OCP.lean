/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.ForbidPairs
public import Linglib.Phonology.OCP
public import Linglib.Phonology.Subregular.ISL

/-!
# The OCP as a tier-based strictly 2-local language

This file characterizes the Obligatory Contour Principle (OCP) of Goldsmith and McCarthy as a
tier-based strictly 2-local (TSL₂) language. The OCP constraint `Constraint.ocp` is the identity
instance of the forbidden-pair constraint `Constraint.forbidPairs` of `ForbidPairs.lean`. Its
forbidden 2-factor is `[some x, some x]`, and its TSL₂ grammar is
`TierStrictlyLocalGrammar.ofForbiddenPairs (· = ·) p`. Without a tier, the OCP is the linguistic
instance of Thue's square-free words. Thue showed that infinite square-free words exist over
three letters, while every binary string of length at least 4 contains a square, so a binary
tonal alphabet cannot satisfy a strict OCP at length.

The satisfaction predicate of the TSL₂ language is exactly `OCP.IsClean`, which the fusion
repair `OCP.collapse` also lands in, and the repair is itself a 2-input strictly local map
(Chandlee and Heinz). The prohibition and the merger are therefore the constraint and a
retraction onto it, both subregular.

## Main definitions

* `ocpForbidden`, `OCPCleanPair`, `TierStrictlyLocalGrammar.ocp`: the OCP instances of the
  forbidden-pair constructions.

## Main results

* `Constraint.ocp_eq_zero_iff_isClean`: the OCP constraint scores zero exactly on `OCP.IsClean`
  strings.
* `Constraint.zeroSet_comap_filter_ocp`: on a tier, its zero set is the language of
  `TierStrictlyLocalGrammar.ocp`.
* `collapse_isISL`: the fusion repair `OCP.collapse` is 2-input strictly local.

## References

* [J. A. Goldsmith, *Autosegmental Phonology* (1976)][goldsmith-1976]
* [J. J. McCarthy, *OCP Effects: Gemination and Antigemination* (1986)][mccarthy-1986]
* [A. Thue, *Über unendliche Zeichenreihen* (1906)][thue-1906]
* [J. Chandlee and J. Heinz, *Strict Locality and Phonological Maps* (2018)][chandlee-heinz-2018]
* [J. Chandlee and A. Jardine, *Autosegmental Input Strictly Local Functions*
  (2019)][chandlee-jardine-2019]
-/

@[expose] public section

namespace Subregular

open Constraints OptimalityTheory

-- `α : Type` (rather than `Type*`) is forced by `OptimalityTheory`, which is monomorphic in
-- universe 0.
variable {α : Type}

/-- The forbidden 2-factors for the OCP are the pairs `[some x, some x]` of two identical
non-boundary symbols, the identity instance of `forbiddenPairs`. -/
def ocpForbidden (α : Type) [DecidableEq α] : Set (Augmented α) :=
  forbiddenPairs (α := α) (· = ·)

/-- The TSL₂ grammar of the OCP forbids two adjacent identical symbols on the tier defined by
`p`. It is the identity instance of `TierStrictlyLocalGrammar.ofForbiddenPairs`. -/
def TierStrictlyLocalGrammar.ocp [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    TierStrictlyLocalGrammar 2 α :=
  TierStrictlyLocalGrammar.ofForbiddenPairs (α := α) (· = ·) p

/-- Two augmented symbols are *OCP-clean as a pair* iff they are not both `some` of the same
value. This is the identity instance of `CleanPair`. -/
def OCPCleanPair [DecidableEq α] : Option α → Option α → Prop :=
  CleanPair (α := α) (· = ·)

lemma ocpCleanPair_some_some [DecidableEq α] (a b : α) :
    OCPCleanPair (some a) (some b) ↔ a ≠ b :=
  CleanPair.some_some a b

/-- The OCP relation is boundary-vacuous, the identity instance of `CleanPair.isBoundaryVacuous`. -/
lemma OCPCleanPair.isBoundaryVacuous [DecidableEq α] :
    IsBoundaryVacuous (OCPCleanPair (α := α)) :=
  CleanPair.isBoundaryVacuous

/-! ### The repair is subregular -/

/-- The OCP fusion repair `OCP.collapse` is a **2-input strictly local** string function
([chandlee-heinz-2018]), which scans left to right with a one-symbol window and deletes a symbol
iff it equals its predecessor. [chandlee-jardine-2019] classify tonal OCP processes as
autosegmental input strictly local. -/
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
    | nil => simp
    | cons b l ih =>
      rw [ISLRule.applyAux_cons]
      have hwin : ([a] ++ [b]).rtake (2 - 1) = [b] := by
        simp [List.rtake]
      rw [hwin, List.destutter'_cons]
      show a :: ((if [a] = [b] then [] else [b]) ++ r.applyAux [b] l) = _
      by_cases hab : a = b
      · subst hab
        rw [ite_eq_left rfl, List.nil_append, ite_eq_right (by simp : ¬ (a ≠ a))]
        exact ih a
      · rw [ite_eq_right (by simpa using hab), ite_eq_left (by simpa using hab)]
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
    rw [ite_eq_right (by simp), List.cons_append, List.nil_append]
    rw [OCP.collapse_eq_destutter, List.destutter_cons']
    exact key x rest

end Subregular

namespace Constraints.Constraint

variable {α : Type} [DecidableEq α]

/-- A string satisfies the OCP iff it is `OCP.IsClean`. Since the fusion repair `OCP.collapse`
also characterizes `OCP.IsClean`, the prohibition and the repair are two faces of one principle
rather than parallel formalizations. -/
theorem ocp_eq_zero_iff_isClean (w : List α) : ocp w = 0 ↔ OCP.IsClean w :=
  forbidPairs_eq_zero_iff (· = ·) w

/-- On the tier `p`, the zero set of the OCP is the language of the TSL₂ grammar
`TierStrictlyLocalGrammar.ocp p`, so the optimality-theoretic constraint and the subregular class
are co-extensive. -/
theorem zeroSet_comap_filter_ocp (p : α → Prop) [DecidablePred p] :
    (ocp.comap fun w ↦ w.filter (p ·)).zeroSet =
      (Subregular.TierStrictlyLocalGrammar.ocp p).language :=
  zeroSet_comap_filter_forbidPairs (· = ·) p

end Constraints.Constraint
