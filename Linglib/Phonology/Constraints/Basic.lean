/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Constraints.Defs
import Linglib.Core.Computability.TierProjection
import Linglib.Core.Computability.Subregular.Language.ForbiddenPairs

/-!
# Tier-based markedness constraint library
[prince-smolensky-1993] [mccarthy-prince-1995] [goldsmith-1976] [mccarthy-1986]

Constructors for the framework-neutral `Constraint C = C → ℕ` (shared by OT and
Harmonic Grammar) whose content goes beyond a single predicate.

**Binary constraints are just `Constraint.binary P`** (`Defs`): MAX, DEP, IDENT,
ALIGN, \*STRUC differ only in the predicate you pass and the `def` name you give —
post-`family`-deletion they are the *same* function, so there is no `mkMax`/`mkDep`/…
The faithfulness/markedness family is recovered structurally
(`OptimalityTheory.Correspondence`), not from a constructor. Contextual
faithfulness ([coetzee-pater-2011]) is `Constraint.binary (fun c => deleted c ∧ ctx c)`.

This file provides the **gradient, tier-projected markedness** constructors —
OCP, AGREE, forbidden pairs/singletons — which carry genuine adjacency logic.
-/

namespace Constraints

-- `countAdjacent` is alphabet-generic list combinatorics living in `Subregular`;
-- open it file-locally (don't relay a Core name through `Constraints`).
open Subregular (countAdjacent)

/-- A markedness constraint penalizing tier-adjacent forbidden pairs: project the
candidate's symbols onto tier `T`, then count tier-adjacent pairs `(a, b)` with
`R a b` ([goldsmith-1976]; the TSL₂ bridge is `mkForbidPairsOnTier_zero_iff_in_lang`). -/
def mkForbidPairsOnTier {C α β : Type*} (R : β → β → Prop) [DecidableRel R]
    (T : TierProjection α β) (extract : C → List α) : Constraint C :=
  fun c => countAdjacent R (TierProjection.apply T (extract c))

/-- A markedness constraint penalizing tier elements satisfying `P` (the SL₁
sibling of `mkForbidPairsOnTier`; e.g. \*Coda). -/
def mkForbidSingletonOnTier {C α β : Type*} (P : β → Prop) [DecidablePred P]
    (T : TierProjection α β) (extract : C → List α) : Constraint C :=
  fun c => (TierProjection.apply T (extract c)).countP (fun x => decide (P x))

/-- Count adjacent identical pairs — `countAdjacent (· = ·)`, under the OCP name. -/
def adjacentIdentical {α : Type*} [DecidableEq α] : List α → Nat :=
  countAdjacent (· = ·)

/-- An OCP constraint ([mccarthy-1986]): penalizes adjacent identical elements on
the tier extracted by `project`. Polymorphic over the feature type ([berent-2026]). -/
def mkOCP {C α : Type*} [DecidableEq α] (project : C → List α) : Constraint C :=
  fun c => adjacentIdentical (project c)

/-- An OCP constraint from a `TierProjection` — the `R := (· = ·)` instance of
`mkForbidPairsOnTier` ([goldsmith-1976] [mccarthy-1986] [berent-2026]). -/
def mkOCPOnTier {C α β : Type*} [DecidableEq β]
    (T : TierProjection α β) (extract : C → List α) : Constraint C :=
  mkForbidPairsOnTier (· = ·) T extract

/-- An AGREE constraint — the `R := (· ≠ ·)` instance of `mkForbidPairsOnTier`,
the non-identity dual of `mkOCPOnTier`. -/
def mkAgreeOnTier {C α β : Type*} [DecidableEq β]
    (T : TierProjection α β) (extract : C → List α) : Constraint C :=
  mkForbidPairsOnTier (· ≠ ·) T extract

end Constraints
