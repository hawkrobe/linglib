/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.TierProjection
import Linglib.Core.Computability.Subregular.Language.TierStrictlyLocal

/-!
# Bridge: Autosegmental TierProjection ↔ TSL TierProjection Projection

The autosegmental tier formalism (`TierProjection`, the Kleisli morphism
`α → Option β` lifted via `List.filterMap`, now in `Phonology/TierProjection.lean`) and
the subregular TSL formalism (`Subregular.tierProject`,
`List.filter`) compute the same projection. Since the two now live in different
layers (Phonology vs Core) they no longer coincide *by definition*, so this file
records the bridge as an explicit lemma and provides a thin adapter for building
a TSL_k grammar directly from a `Bool`-valued class predicate (the autosegmental
constructor shape), so a phonological tier (tonal tier, sibilant tier, nasal
tier) plugs into TSL machinery without restating projection or filtering.

## What this enables

Phonological constraints already in the codebase (`mkOCPOnTier` in
`Phonology/OptimalityTheory/Constraints.lean`, the tonal tier `tonalTier`
in `Studies/Rolle2018.lean`) reuse the same `TierProjection.apply` machinery as TSL
grammars — the bridge `apply_byClass_eq_tierProject` reconnects the two
projections in one line.
-/

namespace Subregular

variable {α : Type*}

/-- **Bridge identity**: the autosegmental projection `TierProjection.apply (TierProjection.byClass T)`
and the subregular `tierProject T` are the same map — both reduce to `List.filter`.
Now that the `TierProjection` projection morphism lives in `Phonology/` and `tierProject` is
de-coupled to `List.filter` directly, this is an explicit lemma (via
`TierProjection.apply_byClass` and `tierProject_eq_filter`) rather than `rfl`. -/
theorem apply_byClass_eq_tierProject (T : α → Prop) [DecidablePred T]
    (xs : List α) :
    TierProjection.apply (TierProjection.byClass T) xs = tierProject T xs :=
  (TierProjection.apply_byClass T xs).trans (tierProject_eq_filter T xs).symm

/-- **Adapter**: build a TSL_k grammar from a class-membership autosegmental
tier given as a `Bool` predicate. The TSL tier predicate is `(p · = true)`,
giving the TSL projection that matches `TierProjection.apply (TierProjection.byClass p)` on
every input. Provided as a convenience for callers whose class predicates
arise from `FeatureSpec`-style Bool lookups; native `Prop`-valued
predicates can construct `TSLGrammar` records directly. -/
def TSLGrammar.ofByClass (k : ℕ) (p : α → Bool)
    (permitted : Set (Augmented α)) :
    TSLGrammar k α where
  tier := fun x => p x = true
  permitted := permitted

/-- The TSL grammar built from `byClass` projects via the same filter as
`TierProjection.apply (TierProjection.byClass p)`. -/
@[simp] theorem tierProject_ofByClass (k : ℕ) (p : α → Bool) (xs : List α) :
    tierProject (TSLGrammar.ofByClass (α := α) k p ∅).tier xs =
      xs.filter p := by
  rw [tierProject_eq_filter]
  congr 1
  funext x
  show decide (p x = true) = p x
  cases p x <;> rfl

end Subregular
