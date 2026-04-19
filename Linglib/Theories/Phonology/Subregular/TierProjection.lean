/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.StringHom
import Linglib.Core.Computability.Subregular.Tier

/-!
# Bridge: Autosegmental Tier ↔ TSL Tier Projection

The autosegmental tier formalism (`Core.Tier`, the Kleisli morphism
`α → Option β` lifted via `List.filterMap`) and the subregular TSL
formalism (`Core.Computability.Subregular.tierProject`, the
predicate-filter `xs.filter (decide ∘ T)`) are operationally identical
in their shared common case: a class-membership tier that keeps symbols
of one type without relabeling.

Specifically, for any decidable predicate `T : α → Prop` and the
corresponding `Tier α α` built via `Tier.byClass (decide ∘ T)`, the two
projections produce the same list — definitionally, since both reduce
to `List.filter`. This bridge makes the connection explicit, so a
phonological tier (autosegmental tonal tier, sibilant tier, nasal tier)
can be reused as the segmental tier of a TSL_k grammar without
restating the projection.

## The two formalisms

* **`Core.Tier α β`** (`Core/StringHom.lean`): a per-symbol partial map
  `α → Option β`, lifted to `List α → List β` via `List.filterMap`. It
  is the morphism `α → β` in the Kleisli category of `Option`.
  `Tier.byClass : (α → Bool) → Tier α α` is the special case that keeps
  symbols satisfying a Bool predicate (no relabeling).

* **`Subregular.tierProject T`** (`Core/Computability/Subregular/Tier.lean`):
  the segmental tier of Lambert (@cite{lambert-2022} §3.4) — a predicate
  `T : α → Prop` with `[DecidablePred T]` filtering `List α → List α`
  via `xs.filter (decide ∘ T)`.

The two coincide on `byClass`-style tiers; `Tier α β` with `β ≠ α` is a
proper generalization (it relabels) that has no TSL counterpart, while
TSL has no relabeling primitive.

## What this enables

Phonological constraints already in the codebase (`mkOCPOnTier` in
`Theories/Phonology/OptimalityTheory/Constraints.lean`, the tonal tier
in `Theories/Phonology/Tier.lean`) can now be reused as the projection
step of a TSL_k grammar without re-stipulating the filter operation.
-/

namespace Phonology.Subregular

open Core Core.Computability.Subregular

variable {α : Type*}

/-- **Bridge lemma**: a class-membership autosegmental tier (`Tier.byClass`,
applied via `Tier.apply` as `List.filterMap`) and the TSL segmental
tier (`tierProject`, a predicate-filtered `List.filter`) produce the
same projection on the same predicate. Both reduce to `List.filter`. -/
theorem apply_byClass_eq_tierProject (T : α → Prop) [DecidablePred T]
    (xs : List α) :
    Tier.apply (Tier.byClass (fun x => decide (T x))) xs =
      tierProject T xs := by
  rw [Tier.apply_byClass]
  rfl

/-- **Adapter**: build a TSL_k grammar from a class-membership autosegmental
tier (a `Bool` predicate). The TSL tier predicate is `(p · = true)`,
giving the TSL projection that matches `Tier.apply (Tier.byClass p)`
on every input. -/
def TSLGrammar.ofByClass (k : ℕ) (p : α → Bool)
    (permitted : Set (Augmented α)) :
    TSLGrammar k α where
  tier := fun x => p x = true
  permitted := permitted

/-- The TSL grammar built from `byClass` projects via the same filter as
`Tier.apply (Tier.byClass p)`. -/
@[simp] theorem tierProject_ofByClass (k : ℕ) (p : α → Bool) (xs : List α) :
    tierProject (TSLGrammar.ofByClass (α := α) k p ∅).tier xs =
      Tier.apply (Tier.byClass p) xs := by
  rw [Tier.apply_byClass]
  show xs.filter _ = xs.filter p
  congr 1
  funext x
  show decide (p x = true) = p x
  cases p x <;> rfl

end Phonology.Subregular
