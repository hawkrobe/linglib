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
`List.filterMap`. This is the monoid-hom from `α*` to `β*` in the Kleisli
category of `Option`.

This module provides the types and basic operations:

- `StringHom α β := α → List β` — the general letterwise homomorphism.
- `Tier α β := α → Option β` — the erasing (tier-projecting) special case.
- `Tier.apply` — lift to `List α → List β` (the projection).
- `Tier.applyI` — lift to `List α → List (β × ℕ)` carrying source indices,
  matching @cite{belth-2026}'s `proj(x, T)` (Definition 2).
- `Tier.comp` — Kleisli composition of tiers (tiers compose as morphisms).
- `Tier.byClass`, `Tier.total`, `Tier.id'`, `Tier.empty` — constructors.

The monoid-homomorphism law (`Tier.apply_append`) holds **definitionally** via
`List.filterMap_append`; this is what licenses tier projections in OT and HG
constraint evaluation (`mkOCP` in `Phonology/Constraints.lean` already takes a
generic `project : C → List α`, so `Tier.apply T` plugs in directly).

@cite{goldsmith-1976} @cite{belth-2026}
-/

namespace Core

universe u v w

-- ============================================================================
-- § 1: Letterwise String Homomorphism
-- ============================================================================

/-- A **letterwise string homomorphism** `α* → β*`: a per-symbol map sending
    each input symbol to a (possibly empty, possibly multi-symbol) output
    string. Lifted to lists via `List.flatMap`. -/
abbrev StringHom (α : Type u) (β : Type v) : Type _ := α → List β

namespace StringHom

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Lift a letterwise homomorphism to `List α → List β`. -/
def apply (h : StringHom α β) : List α → List β :=
  List.flatMap h

/-- Monoid-hom law: `h` distributes over concatenation. -/
@[simp] theorem apply_append (h : StringHom α β) (xs ys : List α) :
    apply h (xs ++ ys) = apply h xs ++ apply h ys := by
  simp [apply, List.flatMap_append]

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

variable {α : Type u} {β : Type v} {γ : Type w}

-- ---- Constructors -----------------------------------------------------------

/-- The identity tier: every symbol projects to itself. -/
def id' : Tier α α := some

/-- The empty tier: no symbol projects. -/
def empty : Tier α β := fun _ => none

/-- Tier defined by a class predicate: keep symbols satisfying `p`, erase the
    rest. The standard form for autosegmental tonal/featural tiers. -/
def byClass (p : α → Bool) : Tier α α := fun x => if p x then some x else none

/-- Tier defined by a total function: every symbol projects to its image. -/
def total (f : α → β) : Tier α β := some ∘ f

-- ---- Lifts ------------------------------------------------------------------

/-- Lift a tier to `List α → List β`. This is the canonical projection. -/
def apply (T : Tier α β) : List α → List β := List.filterMap T

/-- Lift a tier to `List α → List (β × ℕ)` carrying the source index of each
    surviving symbol. Matches @cite{belth-2026}'s `proj(x, T)` (Definition 2),
    which is used by the D2L learner to recover blocking environments. -/
def applyI (T : Tier α β) (xs : List α) : List (β × ℕ) :=
  xs.zipIdx.filterMap fun p => (T p.1).map (·, p.2)

-- ---- Composition (Kleisli) -------------------------------------------------

/-- Kleisli composition: `(g ∘ T)(x) = (T x).bind g`. Tiers compose as
    morphisms in the Kleisli category of `Option`. -/
def comp (g : Tier β γ) (T : Tier α β) : Tier α γ := fun x => (T x).bind g

@[inherit_doc] infixr:90 " ∘ₜ " => Tier.comp

-- ---- Coercion to StringHom --------------------------------------------------

/-- Every tier is a (letterwise) string homomorphism whose per-symbol output
    has length ≤ 1. -/
def toStringHom (T : Tier α β) : StringHom α β :=
  fun x => (T x).toList

-- ============================================================================
-- § 3: Monoid-Homomorphism Laws
-- ============================================================================

/-- Tier projection distributes over concatenation. This is the
    monoid-homomorphism property — load-bearing for compositional
    tier-based constraint evaluation. -/
@[simp] theorem apply_append (T : Tier α β) (xs ys : List α) :
    apply T (xs ++ ys) = apply T xs ++ apply T ys :=
  List.filterMap_append

/-- Tier projection sends the empty word to the empty word. -/
@[simp] theorem apply_nil (T : Tier α β) : apply T [] = [] := rfl

/-- The image-tier is reflected through `toStringHom`. -/
theorem toStringHom_apply (T : Tier α β) (xs : List α) :
    StringHom.apply (toStringHom T) xs = apply T xs := by
  unfold StringHom.apply apply toStringHom
  induction xs with
  | nil => rfl
  | cons a t ih =>
    rw [List.flatMap_cons, List.filterMap_cons]
    cases h : T a with
    | none => simp [ih]
    | some b => simp [ih]

-- ============================================================================
-- § 4: Constructor Lemmas
-- ============================================================================

/-- The identity tier is the identity on lists. -/
@[simp] theorem apply_id' (xs : List α) : apply (Tier.id' : Tier α α) xs = xs := by
  show List.filterMap some xs = xs
  exact List.filterMap_some

/-- The empty tier projects every list to the empty list. -/
@[simp] theorem apply_empty (xs : List α) : apply (Tier.empty : Tier α β) xs = [] := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    show List.filterMap (fun _ => none) (a :: t) = []
    rw [List.filterMap_cons]; exact ih

/-- A class-predicate tier acts as `List.filter`. -/
theorem apply_byClass (p : α → Bool) (xs : List α) :
    apply (Tier.byClass p) xs = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    show List.filterMap (fun x => if p x then some x else none) (a :: t)
       = (a :: t).filter p
    rw [List.filterMap_cons, List.filter_cons]
    cases h : p a
    · simp; exact ih
    · simp; exact ih

/-- A total-function tier acts as `List.map`. -/
@[simp] theorem apply_total (f : α → β) (xs : List α) :
    apply (Tier.total f) xs = xs.map f := by
  show List.filterMap (some ∘ f) xs = xs.map f
  induction xs with
  | nil => rfl
  | cons a t _ => rw [List.filterMap_cons]; simp

/-- `total` is length-preserving — all symbols survive. -/
@[simp] theorem length_apply_total (f : α → β) (xs : List α) :
    (apply (Tier.total f) xs).length = xs.length := by
  simp

-- ============================================================================
-- § 5: Composition Laws
-- ============================================================================

/-- Kleisli composition agrees with sequential application on lists. -/
theorem apply_comp (g : Tier β γ) (T : Tier α β) (xs : List α) :
    apply (g ∘ₜ T) xs = apply g (apply T xs) := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    show List.filterMap (fun x => (T x).bind g) (a :: t)
       = List.filterMap g (List.filterMap T (a :: t))
    rw [List.filterMap_cons, List.filterMap_cons]
    cases h : T a with
    | none => simp; exact ih
    | some b =>
      cases hg : g b with
      | none => simp [hg]; exact ih
      | some c => simp [hg]; exact ih

/-- Identity is a left unit for composition. -/
@[simp] theorem id_comp (T : Tier α β) : (Tier.id' : Tier β β) ∘ₜ T = T := by
  funext x
  cases h : T x <;> simp [comp, id', h]

/-- Identity is a right unit for composition. -/
@[simp] theorem comp_id (T : Tier α β) : T ∘ₜ (Tier.id' : Tier α α) = T := by
  funext x; rfl

end Tier

end Core
