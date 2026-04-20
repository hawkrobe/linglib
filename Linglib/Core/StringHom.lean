import Mathlib.Data.List.Basic

/-!
# Erasing String Homomorphisms and Tier Projections

A **string homomorphism** `h : α* → β*` is a monoid homomorphism on free
monoids: it satisfies `h(uv) = h(u) ++ h(v)` and `h(ε) = ε`. Such a map is
**letterwise** when it is determined by its action on single symbols, and
**erasing** when each symbol maps to *at most one* output symbol.

A **tier projection** in autosegmental phonology (@cite{goldsmith-1976}) and
in tier-based learning (@cite{belth-2026}) is exactly the letterwise erasing
case: a per-symbol partial map `α → Option β`, lifted to `α* → β*` via
`List.filterMap`. This is the morphism `α → β` in the Kleisli category of
`Option` over the free-monoid functor.

This module provides:

- `StringHom α β := α → List β` — the general letterwise homomorphism.
- `Tier α β := α → Option β` — the erasing case.
- `Tier.apply` — lift to `List α → List β` (the projection itself).
- `Tier.id`, `Tier.empty`, `Tier.byClass`, `Tier.total` — constructors.

The monoid-homomorphism law (`Tier.apply_append`) holds **definitionally**
via `List.filterMap_append`; this is what licenses tier projections in OT
and HG constraint evaluation (`mkOCP` in `Phonology/Constraints.lean`
already takes a generic `project : C → List α`, so `Tier.apply T` plugs in
directly).

@cite{goldsmith-1976} @cite{belth-2026}
-/

namespace Core

universe u v

-- ============================================================================
-- § 1: Letterwise String Homomorphism
-- ============================================================================

/-- A **letterwise string homomorphism** `α* → β*`: a per-symbol map sending
    each input symbol to a (possibly empty, possibly multi-symbol) output
    string. Lifted to lists via `List.flatMap`. -/
abbrev StringHom (α : Type u) (β : Type v) : Type _ := α → List β

namespace StringHom

variable {α : Type u} {β : Type v}

/-- Lift a letterwise homomorphism to `List α → List β`. -/
def apply (h : StringHom α β) : List α → List β :=
  List.flatMap h

/-- Monoid-hom law: `h` distributes over concatenation. -/
@[simp] theorem apply_append (h : StringHom α β) (xs ys : List α) :
    apply h (xs ++ ys) = apply h xs ++ apply h ys :=
  List.flatMap_append

/-- Monoid-hom law: `h` sends the empty word to the empty word. -/
@[simp] theorem apply_nil (h : StringHom α β) : apply h [] = [] := rfl

end StringHom

-- ============================================================================
-- § 2: Tier — The Erasing Special Case
-- ============================================================================

/-- A **tier projection** `α* → β*`: a per-symbol partial map.
    Each input symbol either projects to one tier symbol or is erased.

    This is the morphism `α → β` in the Kleisli category of `Option`, and
    equivalently a letterwise erasing string homomorphism. The lift to
    `List α → List β` is `List.filterMap`. -/
abbrev Tier (α : Type u) (β : Type v) : Type _ := α → Option β

namespace Tier

variable {α : Type u} {β : Type v}

/-- The identity tier: every symbol projects to itself. -/
protected def id : Tier α α := some

/-- The empty tier: no symbol projects. -/
def empty : Tier α β := fun _ => none

/-- Tier defined by a class predicate: keep symbols satisfying `p`, erase
    the rest. The standard form for autosegmental tonal/featural tiers.

    Following mathlib's `Finset.filter` / `Multiset.filter` convention,
    `p` is `Prop`-valued with `[DecidablePred]`, so call sites can pass
    structural predicates (`fun x => x = .l`, `fun x => IsCons x`)
    without inserting `decide` wrappers. -/
def byClass (p : α → Prop) [DecidablePred p] : Tier α α :=
  fun x => if p x then some x else none

/-- Tier defined by a total function: every symbol projects to its image. -/
def total (f : α → β) : Tier α β := some ∘ f

/-- Lift a tier to `List α → List β`. This is the canonical projection. -/
def apply (T : Tier α β) : List α → List β := List.filterMap T

-- ---- Monoid-homomorphism laws ----------------------------------------------

/-- Tier projection distributes over concatenation. This is the
    monoid-homomorphism property — load-bearing for compositional
    tier-based constraint evaluation. -/
@[simp] theorem apply_append (T : Tier α β) (xs ys : List α) :
    apply T (xs ++ ys) = apply T xs ++ apply T ys :=
  List.filterMap_append

/-- Tier projection sends the empty word to the empty word. -/
@[simp] theorem apply_nil (T : Tier α β) : apply T [] = [] := rfl

-- ---- Constructor lemmas ----------------------------------------------------

/-- The identity tier is the identity on lists. -/
@[simp] theorem apply_id (xs : List α) : apply (Tier.id : Tier α α) xs = xs :=
  List.filterMap_some

/-- The empty tier projects every list to the empty list. -/
@[simp] theorem apply_empty (xs : List α) :
    apply (Tier.empty : Tier α β) xs = [] := by
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    show List.filterMap (fun _ => none) (_ :: _) = []
    rw [List.filterMap_cons]; exact ih

/-- A class-predicate tier acts as `List.filter`. The right-hand side
    inserts `decide` because `List.filter` is `Bool`-valued; consumers
    that already work in `Bool` should use this lemma directly. -/
theorem apply_byClass (p : α → Prop) [DecidablePred p] (xs : List α) :
    apply (Tier.byClass p) xs = xs.filter (fun x => decide (p x)) := by
  show List.filterMap (Tier.byClass p) xs = _
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.filterMap_cons, List.filter_cons]
    by_cases hpx : p x
    · have hbc : Tier.byClass p x = some x := by simp [Tier.byClass, hpx]
      rw [hbc, ih, decide_eq_true hpx]; rfl
    · have hbc : Tier.byClass p x = none := by simp [Tier.byClass, hpx]
      rw [hbc, ih, decide_eq_false hpx]; rfl

/-- A total-function tier acts as `List.map`. -/
@[simp] theorem apply_total (f : α → β) (xs : List α) :
    apply (Tier.total f) xs = xs.map f :=
  congrFun List.filterMap_eq_map xs

/-- `total` is length-preserving — all symbols survive. -/
@[simp] theorem length_apply_total (f : α → β) (xs : List α) :
    (apply (Tier.total f) xs).length = xs.length := by
  simp

-- ---- Derived scans (used by tier-based alternation rules) -----------------

/-- The last (rightmost) projected symbol of `xs` satisfying `q`. The
    standard "preceding tier-adjacent context" lookup for rules like
    @cite{belth-2026}'s `Disagree(A, F) / C __ ∘ proj(·, T)`. -/
def lastWith (T : Tier α β) (q : β → Prop) [DecidablePred q]
    (xs : List α) : Option β :=
  ((apply T xs).filter (fun y => decide (q y))).getLast?

/-- The first (leftmost) projected symbol of `xs` satisfying `q`. The
    symmetric right-context lookup for `C / __ C ∘ proj(·, T)` rules. -/
def firstWith (T : Tier α β) (q : β → Prop) [DecidablePred q]
    (xs : List α) : Option β :=
  ((apply T xs).filter (fun y => decide (q y))).head?

end Tier

end Core
