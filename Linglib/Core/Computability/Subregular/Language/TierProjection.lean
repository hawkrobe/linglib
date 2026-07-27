/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Tier Projections (erasing letterwise homomorphisms)

A **tier projection** in autosegmental phonology ([goldsmith-1976]) and in
tier-based learning ([belth-2026]) is a letterwise *erasing* string
homomorphism: a per-symbol partial map `α → Option β`, lifted to `α* → β*`
via `List.filterMap`. This is the morphism `α → β` in the Kleisli category of
`Option` over the free-monoid functor.

General (non-erasing) string homomorphisms need no bespoke wrapper: a per-symbol
map is just `α → List β`, and the string action is `List.flatMap` — which, since
`List α = FreeMonoid α`, *is* the free-monoid lift `FreeMonoid.lift`. CFL closure
under string homomorphism lives in
`Linglib.Core.Computability.ContextFreeGrammar.Map`.

This module provides:

- `TierProjection α β := α → Option β` — the erasing case.
- `TierProjection.apply` — lift to `List α → List β` (the projection itself).
- `TierProjection.applyHom` — that lift bundled as a `FreeMonoid α →* FreeMonoid β`.
- `id`, `empty`, `byClass`, `total` — constructors.

The monoid-homomorphism law (`TierProjection.apply_append`) holds **definitionally**
via `List.filterMap_append`; this is what licenses tier projections in OT
and HG constraint evaluation (`mkForbidPairsOnTier` in
`Phonology/OptimalityTheory/Constraints.lean` takes a generic `TierProjection`, so
`TierProjection.apply T` plugs in directly).

Home: `Core/Computability/` — the content is pure `List`/`Option` combinatorics
(the `Option`-Kleisli morphism on free monoids), with no linguistic content in
any type signature; the linguistic interpretation lives entirely in the
`Phonology/` and `Studies/` consumers. The subregular projection
`Subregular.tierProject` (`List.filter`) and its monoid-hom packaging
`Subregular.tierProjectHom`, both in
`Core/Computability/Subregular/Language/`, are the single-alphabet `byClass`
specialization of this morphism; unifying the three onto this keystone (so they
coincide by `rfl`) is a follow-up.

[goldsmith-1976] [belth-2026]
-/

universe u v

/-- A **tier projection** `α* → β*`: a per-symbol partial map.
    Each input symbol either projects to one tier symbol or is erased.

    This is the morphism `α → β` in the Kleisli category of `Option`, and
    equivalently a letterwise erasing string homomorphism. The lift to
    `List α → List β` is `List.filterMap`. -/
abbrev TierProjection (α : Type u) (β : Type v) : Type _ := α → Option β

namespace TierProjection

variable {α : Type u} {β : Type v}

/-- The identity tier: every symbol projects to itself. -/
protected def id : TierProjection α α := some

/-- The empty tier: no symbol projects. -/
def empty : TierProjection α β := fun _ => none

/-- A tier projection defined by a class predicate: keep symbols satisfying `p`, erase
    the rest. The standard form for autosegmental tonal/featural tiers.

    Following mathlib's `Finset.filter` / `Multiset.filter` convention,
    `p` is `Prop`-valued with `[DecidablePred]`, so call sites can pass
    structural predicates (`fun x => x = .l`, `fun x => IsCons x`)
    without inserting `decide` wrappers. -/
def byClass (p : α → Prop) [DecidablePred p] : TierProjection α α :=
  fun x => if p x then some x else none

/-- A tier projection defined by a total function: every symbol projects to its image. -/
def total (f : α → β) : TierProjection α β := some ∘ f

/-- Lift a tier to `List α → List β`. This is the canonical projection. -/
def apply (T : TierProjection α β) : List α → List β := List.filterMap T

-- ---- Monoid-homomorphism laws ----------------------------------------------

/-- Tier projection distributes over concatenation. This is the
    monoid-homomorphism property — load-bearing for compositional
    tier-based constraint evaluation. -/
@[simp] theorem apply_append (T : TierProjection α β) (xs ys : List α) :
    apply T (xs ++ ys) = apply T xs ++ apply T ys :=
  List.filterMap_append

/-- Tier projection sends the empty word to the empty word. -/
@[simp] theorem apply_nil (T : TierProjection α β) : apply T [] = [] := rfl

/-- The tier projection bundled as a **monoid homomorphism** `FreeMonoid α →* FreeMonoid β`
of strings: `apply` preserves `1` (`apply_nil`) and `*` (`apply_append`). Named
specializations — e.g. `Subregular.tierProjectHom` — are defined as `applyHom` of a
particular projection, inheriting the hom laws by construction rather than re-proving them. -/
def applyHom (T : TierProjection α β) : FreeMonoid α →* FreeMonoid β where
  toFun := apply T
  map_one' := apply_nil T
  map_mul' := apply_append T

@[simp] theorem applyHom_apply (T : TierProjection α β) (w : FreeMonoid α) :
    applyHom T w = apply T w := rfl

-- ---- Constructor lemmas ----------------------------------------------------

/-- The identity tier is the identity on lists. -/
@[simp] theorem apply_id (xs : List α) : apply (TierProjection.id : TierProjection α α) xs = xs :=
  List.filterMap_some

/-- The empty tier projects every list to the empty list. -/
@[simp] theorem apply_empty (xs : List α) :
    apply (TierProjection.empty : TierProjection α β) xs = [] := by
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    show List.filterMap (fun _ => none) (_ :: _) = []
    rw [List.filterMap_cons]; exact ih

/-- A class-predicate tier acts as `List.filter`. The right-hand side
    inserts `decide` because `List.filter` is `Bool`-valued; consumers
    that already work in `Bool` should use this lemma directly. -/
theorem apply_byClass (p : α → Prop) [DecidablePred p] (xs : List α) :
    apply (TierProjection.byClass p) xs = xs.filter (fun x => decide (p x)) := by
  show List.filterMap (TierProjection.byClass p) xs = _
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.filterMap_cons, List.filter_cons]
    by_cases hpx : p x
    · have hbc : TierProjection.byClass p x = some x := by simp [TierProjection.byClass, hpx]
      rw [hbc, ih, decide_eq_true hpx]; rfl
    · have hbc : TierProjection.byClass p x = none := by simp [TierProjection.byClass, hpx]
      rw [hbc, ih, decide_eq_false hpx]; rfl

/-- A total-function tier acts as `List.map`. -/
@[simp] theorem apply_total (f : α → β) (xs : List α) :
    apply (TierProjection.total f) xs = xs.map f :=
  congrFun List.filterMap_eq_map xs

/-- `total` is length-preserving — all symbols survive. -/
@[simp] theorem length_apply_total (f : α → β) (xs : List α) :
    (apply (TierProjection.total f) xs).length = xs.length := by
  simp

-- ---- Derived scans (used by tier-based alternation rules) -----------------

/-- The last (rightmost) projected symbol of `xs` satisfying `q`. The
    standard "preceding tier-adjacent context" lookup for rules like
    [belth-2026]'s `Disagree(A, F) / C __ ∘ proj(·, T)`. -/
def lastWith (T : TierProjection α β) (q : β → Prop) [DecidablePred q]
    (xs : List α) : Option β :=
  ((apply T xs).filter (fun y => decide (q y))).getLast?

/-- The first (leftmost) projected symbol of `xs` satisfying `q`. The
    symmetric right-context lookup for `C / __ C ∘ proj(·, T)` rules. -/
def firstWith (T : TierProjection α β) (q : β → Prop) [DecidablePred q]
    (xs : List α) : Option β :=
  ((apply T xs).filter (fun y => decide (q y))).head?

end TierProjection
