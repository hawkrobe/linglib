/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Tier
import Linglib.Core.Computability.Subregular.Tier

/-!
# Bridge: Autosegmental Tier ↔ TSL Tier Projection

The autosegmental tier formalism (`Core.Tier`, the Kleisli morphism
`α → Option β` lifted via `List.filterMap`) and the subregular TSL
formalism (`Core.Computability.Subregular.tierProject`) share a single
underlying primitive: `tierProject T` is literally
`Core.Tier.apply (Core.Tier.byClass T)`, so the two reduce to one
another by definition.

This file records the resulting `rfl` identity and provides a thin
adapter for building a TSL_k grammar directly from a `Bool`-valued
class predicate (the autosegmental constructor shape), so a
phonological tier (tonal tier, sibilant tier, nasal tier) plugs into
TSL machinery without restating projection or filtering.

## What this enables

Phonological constraints already in the codebase (`mkOCPOnTier` in
`Phonology/OptimalityTheory/Constraints.lean`, the tonal tier `tonalTier`
in `Studies/Rolle2018.lean`) reuse the same
`Tier.apply` machinery as TSL grammars — the bridge is no longer a theorem
to discharge but a definitional consequence.
-/

namespace Phonology.Subregular

open Core Core.Computability.Subregular

variable {α : Type*}

/-- **Bridge identity** (definitional): `tierProject T` is by definition
`Tier.apply (Tier.byClass T)`. After the 0.230.x consolidation onto
`Core.Tier` and the subsequent `Tier.byClass` migration to
`Prop`+`Decidable`, this is `rfl`. -/
theorem apply_byClass_eq_tierProject (T : α → Prop) [DecidablePred T]
    (xs : List α) :
    Tier.apply (Tier.byClass T) xs = tierProject T xs := rfl

/-- **Adapter**: build a TSL_k grammar from a class-membership autosegmental
tier given as a `Bool` predicate. The TSL tier predicate is `(p · = true)`,
giving the TSL projection that matches `Tier.apply (Tier.byClass p)` on
every input. Provided as a convenience for callers whose class predicates
arise from `FeatureSpec`-style Bool lookups; native `Prop`-valued
predicates can construct `TSLGrammar` records directly. -/
def TSLGrammar.ofByClass (k : ℕ) (p : α → Bool)
    (permitted : Set (Augmented α)) :
    TSLGrammar k α where
  tier := fun x => p x = true
  permitted := permitted

/-- The TSL grammar built from `byClass` projects via the same filter as
`Tier.apply (Tier.byClass p)`. -/
@[simp] theorem tierProject_ofByClass (k : ℕ) (p : α → Bool) (xs : List α) :
    tierProject (TSLGrammar.ofByClass (α := α) k p ∅).tier xs =
      xs.filter p := by
  rw [tierProject_eq_filter]
  congr 1
  funext x
  show decide (p x = true) = p x
  cases p x <;> rfl

end Phonology.Subregular
