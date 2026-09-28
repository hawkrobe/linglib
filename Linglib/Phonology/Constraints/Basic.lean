/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Constraints.Defs
public import Linglib.Phonology.Subregular.ForbiddenPairs

/-!
# Tier-based markedness constraint library

Constructors for the framework-neutral `Constraint C = C → ℕ` of Optimality Theory
([prince-smolensky-1993]) and Harmonic Grammar whose content goes beyond a single predicate.

**Binary constraints are just `Constraint.binary P`** (`Defs`): MAX, DEP, IDENT,
ALIGN, \*STRUC differ only in the predicate you pass and the `def` name you give —
post-`family`-deletion they are the *same* function, so there is no `mkMax`/`mkDep`/…
The faithfulness/markedness family is recovered structurally
(`OptimalityTheory.Correspondence`), not from a constructor. Contextual
faithfulness ([coetzee-pater-2011]) is `Constraint.binary (fun c => deleted c ∧ ctx c)`.

This file provides the **gradient, tier-projected markedness** constructors (OCP
[mccarthy-1986], AGREE, forbidden pairs), which carry genuine adjacency logic. A tier is a
decidable predicate on symbols, and projection onto it erases the symbols off it
([heinz-rawal-tanner-2011]), `List.filter` of the candidate's symbols.

## References

* [A. Prince and P. Smolensky, *Optimality Theory: Constraint Interaction in Generative
  Grammar* (1993)][prince-smolensky-1993]
* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
* [A. W. Coetzee and J. Pater, *The Place of Variation in Phonological Theory*
  (2011)][coetzee-pater-2011]
* [J. A. Goldsmith, *Autosegmental Phonology* (1976)][goldsmith-1976]
* [J. J. McCarthy, *OCP Effects: Gemination and Antigemination* (1986)][mccarthy-1986]
* [J. Heinz, C. Rawal and H. G. Tanner, *Tier-based Strictly Local Constraints for Phonology*
  (2011)][heinz-rawal-tanner-2011]
* [I. Berent, *Three arguments for abstraction in phonology* (2026)][berent-2026]
-/

@[expose] public section

namespace Constraints

-- `countAdjacent` is alphabet-generic list combinatorics living in `Subregular`;
-- open it file-locally (don't relay a Core name through `Constraints`).
open Subregular (countAdjacent)

/-- A markedness constraint counting the adjacent pairs `(a, b)` with `R a b` that remain once
the candidate's symbols off the tier `p` are erased. Its TSL₂ bridge is
`mkForbidPairsOnTier_zero_iff_in_language`. -/
def mkForbidPairsOnTier {C α : Type*} (R : α → α → Prop) [DecidableRel R]
    (p : α → Prop) [DecidablePred p] (extract : C → List α) : Constraint C :=
  fun c => countAdjacent R ((extract c).filter (p ·))

/-- Count adjacent identical pairs — `countAdjacent (· = ·)`, under the OCP name. -/
def adjacentIdentical {α : Type*} [DecidableEq α] : List α → Nat :=
  countAdjacent (· = ·)

theorem adjacentIdentical_cons_self {α : Type*} [DecidableEq α] (a : α) (rest : List α) :
    adjacentIdentical (a :: a :: rest) = 1 + adjacentIdentical (a :: rest) := by
  simp [adjacentIdentical, countAdjacent]

theorem adjacentIdentical_cons_of_ne {α : Type*} [DecidableEq α] {a b : α}
    (h : a ≠ b) (rest : List α) :
    adjacentIdentical (a :: b :: rest) = adjacentIdentical (b :: rest) := by
  simp [adjacentIdentical, countAdjacent, h]

/-- Adjacent identity is invariant under an injective relabelling of the elements. -/
theorem adjacentIdentical_map {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (xs : List α) :
    adjacentIdentical (xs.map f) = adjacentIdentical xs :=
  Subregular.countAdjacent_map (· = ·) (S := (· = ·)) (fun _ _ ↦ hf.eq_iff) xs

/-- An OCP constraint ([mccarthy-1986]): penalizes adjacent identical elements on
the tier extracted by `project`. Polymorphic over the feature type ([berent-2026]). -/
def mkOCP {C α : Type*} [DecidableEq α] (project : C → List α) : Constraint C :=
  fun c => adjacentIdentical (project c)

/-- An OCP constraint on the tier `p`, the `R := (· = ·)` instance of `mkForbidPairsOnTier`
([goldsmith-1976] [mccarthy-1986] [berent-2026]). -/
def mkOCPOnTier {C α : Type*} [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (extract : C → List α) : Constraint C :=
  mkForbidPairsOnTier (· = ·) p extract

/-- An AGREE constraint — the `R := (· ≠ ·)` instance of `mkForbidPairsOnTier`,
the non-identity dual of `mkOCPOnTier`. -/
def mkAgreeOnTier {C α : Type*} [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (extract : C → List α) : Constraint C :=
  mkForbidPairsOnTier (· ≠ ·) p extract

end Constraints
