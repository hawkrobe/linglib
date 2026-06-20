/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Tier
import Linglib.Core.Computability.Subregular.Tier

/-!
# Bridge: Autosegmental Tier ↔ TSL Tier Projection

The autosegmental tier formalism (`Tier`, the Kleisli morphism
`α → Option β` lifted via `List.filterMap`, now in `Phonology/Tier.lean`) and
the subregular TSL formalism (`Core.Computability.Subregular.tierProject`,
`List.filter`) compute the same projection. Since the two now live in different
layers (Phonology vs Core) they no longer coincide *by definition*, so this file
records the bridge as an explicit lemma and provides a thin adapter for building
a TSL_k grammar directly from a `Bool`-valued class predicate (the autosegmental
constructor shape), so a phonological tier (tonal tier, sibilant tier, nasal
tier) plugs into TSL machinery without restating projection or filtering.

## What this enables

Phonological constraints already in the codebase (`mkOCPOnTier` in
`Phonology/OptimalityTheory/Constraints.lean`, the tonal tier `tonalTier`
in `Studies/Rolle2018.lean`) reuse the same `Tier.apply` machinery as TSL
grammars — the bridge `apply_byClass_eq_tierProject` reconnects the two
projections in one line.
-/

namespace Phonology.Subregular

open Core Core.Computability.Subregular

variable {α : Type*}

/-- **Bridge identity**: the autosegmental projection `Tier.apply (Tier.byClass T)`
and the subregular `tierProject T` are the same map — both reduce to `List.filter`.
Now that the `Tier` projection morphism lives in `Phonology/` and `tierProject` is
de-coupled to `List.filter` directly, this is an explicit lemma (via
`Tier.apply_byClass` and `tierProject_eq_filter`) rather than `rfl`. -/
theorem apply_byClass_eq_tierProject (T : α → Prop) [DecidablePred T]
    (xs : List α) :
    Tier.apply (Tier.byClass T) xs = tierProject T xs :=
  (Tier.apply_byClass T xs).trans (tierProject_eq_filter T xs).symm

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
