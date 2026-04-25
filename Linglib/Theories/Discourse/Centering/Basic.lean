import Linglib.Theories.Discourse.Centering.Defs
import Mathlib.Data.List.Perm.Basic

/-!
# Centering Theory — Cb, Cf, Cp
@cite{grosz-joshi-weinstein-1995} §3

The basic forward/backward-looking center operations, parameterized by
the role type (via `[CfRanker R]`) and the realizes-semantics
(via `[Realizes U E]`).

* `Utterance.cf` — forward-looking centers, ordered by role rank
  (descending), with surface order as tie-breaker. Implemented by
  insertion sort so that `decide` reduces it in the kernel for the
  paper's worked examples.

* `Utterance.cp` — preferred (top-ranked) Cf element.

* `cb prev cur` — backward-looking center: highest-ranked element of
  `prev.cf` realized in `cur`. The current utterance type is generic
  via `[Realizes U E]`, so the same `cb` works for an `Utterance E R`,
  a `DRSExpr`, or any future representation that supplies a `Realizes`
  instance.

The "unique Cb" claim of @cite{grosz-joshi-weinstein-1995} §3 is
enforced by the type `Option E`, not by a separate theorem.
-/

set_option autoImplicit false

namespace Discourse.Centering

variable {E R : Type}

-- ════════════════════════════════════════════════════
-- § 1. Default Realizes / Pronominalizes for Utterance
-- ════════════════════════════════════════════════════

/-- For a list-of-realizations utterance, `realizes` is list-membership
    of the entity among the realizations' entities. -/
instance utteranceRealizes [DecidableEq E] : Realizes (Utterance E R) E where
  decide u e := u.realizations.any (·.entity == e)

/-- For a list-of-realizations utterance, `pronominalizes` requires a
    realization of `e` whose `isPronoun` flag is true. -/
instance utterancePronominalizes [DecidableEq E] :
    Pronominalizes (Utterance E R) E where
  decide u e :=
    u.realizations.any (fun r => r.entity == e && r.isPronoun)

/-- A flat list of entities also realizes — an entity `e` is realized by
    `es : List E` iff it appears in `es`. This is the minimal "bag of
    referents" representation, useful when role/pronoun annotations are
    unavailable (corpus-extracted referent traces, simple toy examples).

    Together with `utteranceRealizes` and the `DRSExpr` instance in the
    DRT bridge, this confirms that the `Realizes` typeclass abstracts
    cleanly over multiple representations. -/
instance listRealizes [DecidableEq E] : Realizes (List E) E where
  decide es e := es.contains e

@[simp] theorem realizes_list_iff [DecidableEq E] (es : List E) (e : E) :
    realizes es e ↔ e ∈ es := by
  unfold realizes
  show es.contains e = true ↔ _
  simp

namespace Utterance
variable [DecidableEq E]

/-- Existential characterization of `realizes` on a list-of-realizations
    utterance, useful for proofs. -/
theorem realizes_iff (u : Utterance E R) (e : E) :
    realizes u e ↔ ∃ r ∈ u.realizations, r.entity = e := by
  unfold realizes
  show u.realizations.any (·.entity == e) = true ↔ _
  simp [List.any_eq_true]

/-- Existential characterization of `pronominalizes` on a
    list-of-realizations utterance. -/
theorem pronominalizes_iff (u : Utterance E R) (e : E) :
    pronominalizes u e ↔ ∃ r ∈ u.realizations, r.entity = e ∧ r.isPronoun = true := by
  unfold pronominalizes
  show u.realizations.any (fun r => r.entity == e && r.isPronoun) = true ↔ _
  simp [List.any_eq_true]

-- ════════════════════════════════════════════════════
-- § 2. Cf, Cp via insertion sort on rank
-- ════════════════════════════════════════════════════

/-- Insert `r` into a Cf list (ordered by `CfRanker.rank` descending),
    placing `r` after any equally-ranked elements so the original
    surface order acts as a stable tiebreaker.

    Concretely: walk the list, insert `r` at the first position where
    the existing element has *strictly smaller* rank. -/
def cfInsert [CfRanker R]
    (r : Realization E R) : List (Realization E R) → List (Realization E R)
  | []      => [r]
  | x :: xs =>
    if CfRanker.rank x.role < CfRanker.rank r.role then
      r :: x :: xs
    else
      x :: cfInsert r xs

/-- Forward-looking centers, ranked highest-first by role rank with
    surface order as tiebreaker. Implemented by `foldr cfInsert []` —
    insertion sort — so that `decide` reduces it in the kernel for
    the paper's worked examples. -/
def cf [CfRanker R] (u : Utterance E R) : List E :=
  (u.realizations.foldr cfInsert []).map (·.entity)

/-- The top-ranked Cf element ("preferred center", Cp). -/
def cp [CfRanker R] (u : Utterance E R) : Option E := u.cf.head?

end Utterance

-- ════════════════════════════════════════════════════
-- § 2a. cf / cp characterization API
-- ════════════════════════════════════════════════════

namespace Utterance

@[simp] theorem cf_mk_nil [CfRanker R] :
    (Utterance.mk [] : Utterance E R).cf = [] := rfl

@[simp] theorem cp_mk_nil [CfRanker R] :
    (Utterance.mk [] : Utterance E R).cp = none := rfl

/-- `cfInsert` preserves membership: every element of the result is either
    the inserted element or already in the list. -/
theorem mem_cfInsert_iff [CfRanker R] (r : Realization E R)
    (xs : List (Realization E R)) (x : Realization E R) :
    x ∈ cfInsert r xs ↔ x = r ∨ x ∈ xs := by
  induction xs with
  | nil => simp [cfInsert]
  | cons y ys ih =>
    simp only [cfInsert]
    split
    · simp
    · simp [ih, or_left_comm]

/-- `cfInsert r xs` is a permutation of `r :: xs` — insertion sort
    rearranges but doesn't drop or duplicate. -/
theorem cfInsert_perm [CfRanker R] (r : Realization E R)
    (xs : List (Realization E R)) :
    (cfInsert r xs).Perm (r :: xs) := by
  induction xs with
  | nil => exact .refl _
  | cons y ys ih =>
    simp only [cfInsert]
    split
    · exact .refl _
    · exact (List.Perm.cons y ih).trans (.swap r y ys)

/-- The internal sorted list (before mapping to entities) is a
    permutation of the surface realization list. -/
theorem cfRealizations_perm [CfRanker R] (u : Utterance E R) :
    (u.realizations.foldr cfInsert []).Perm u.realizations := by
  induction u.realizations with
  | nil => exact .refl _
  | cons r rs ih =>
    show (cfInsert r (rs.foldr cfInsert [])).Perm (r :: rs)
    exact (cfInsert_perm r _).trans (List.Perm.cons r ih)

/-- **Characterization of `cf`**: an entity is in the forward-looking
    centers iff some realization in the utterance refers to it. The
    insertion-sort implementation is a permutation, so membership is
    preserved. -/
theorem mem_cf_iff [CfRanker R] (u : Utterance E R) (e : E) :
    e ∈ u.cf ↔ ∃ r ∈ u.realizations, r.entity = e := by
  unfold cf
  rw [List.mem_map]
  refine ⟨?_, ?_⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, (cfRealizations_perm u).mem_iff.mp hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, (cfRealizations_perm u).mem_iff.mpr hr, rfl⟩

end Utterance

-- ════════════════════════════════════════════════════
-- § 3. Cb (backward-looking center)
-- ════════════════════════════════════════════════════

/-- Backward-looking center of `cur` with respect to `prev`: the
    highest-ranked element of `prev.cf` that is realized in `cur`.
    `none` if no such element exists.

    The current utterance `cur` can be anything with a `Realizes U E`
    instance — including a `DRSExpr` via the DRT bridge. -/
def cb [DecidableEq E] [CfRanker R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) : Option E :=
  prev.cf.find? (Realizes.decide cur)

/-- **Locality of Cb** (@cite{grosz-joshi-weinstein-1995} §4, claim 5):
    when `cb prev cur` returns some entity, that entity is in
    `prev.cf` — the backward-looking center is strictly local, drawn
    only from the previous utterance's forward-looking centers, never
    from `Cf(U_{n-2})` or earlier. -/
theorem cb_mem_prev_cf [DecidableEq E] [CfRanker R] {U : Type} [Realizes U E]
    {prev : Utterance E R} {cur : U} {e : E} (h : cb prev cur = some e) :
    e ∈ prev.cf :=
  List.mem_of_find?_eq_some h

/-- The Cb is realized in the current utterance: when `cb prev cur` is
    `some e`, the realizes-relation holds of `(cur, e)`. -/
theorem decide_of_cb [DecidableEq E] [CfRanker R] {U : Type} [Realizes U E]
    {prev : Utterance E R} {cur : U} {e : E} (h : cb prev cur = some e) :
    Realizes.decide cur e = true :=
  List.find?_eq_some_iff_append.mp h |>.1

/-- **Characterization of `cb`**: `cb prev cur = some e` iff `e` is in
    `prev.cf` realized in `cur`, and *no earlier* element of `prev.cf`
    (i.e., none more highly ranked) is realized in `cur`. This is the
    "first realized in cf-order" definition unfolded. -/
theorem cb_eq_some_iff [DecidableEq E] [CfRanker R] {U : Type} [Realizes U E]
    {prev : Utterance E R} {cur : U} {e : E} :
    cb prev cur = some e ↔
      ∃ l₁ l₂, prev.cf = l₁ ++ e :: l₂ ∧
        (∀ e' ∈ l₁, Realizes.decide cur e' = false) ∧
        Realizes.decide cur e = true := by
  unfold cb
  rw [List.find?_eq_some_iff_append]
  refine ⟨?_, ?_⟩
  · rintro ⟨h, l₁, l₂, hsplit, hbefore⟩
    refine ⟨l₁, l₂, hsplit, ?_, h⟩
    intro e' he'
    have := hbefore e' he'
    simpa using this
  · rintro ⟨l₁, l₂, hsplit, hbefore, h⟩
    refine ⟨h, l₁, l₂, hsplit, ?_⟩
    intro e' he'
    simp [hbefore e' he']

/-- `cb` is `none` iff no element of `prev.cf` is realized in `cur`. -/
theorem cb_eq_none_iff [DecidableEq E] [CfRanker R] {U : Type} [Realizes U E]
    {prev : Utterance E R} {cur : U} :
    cb prev cur = none ↔ ∀ e ∈ prev.cf, Realizes.decide cur e = false := by
  unfold cb
  rw [List.find?_eq_none]
  refine ⟨fun h e he => ?_, fun h e he => ?_⟩
  · simpa using h e he
  · simp [h e he]

@[simp] theorem cb_empty_prev [DecidableEq E] [CfRanker R] {U : Type} [Realizes U E]
    (cur : U) : cb (Utterance.mk [] : Utterance E R) cur = none := rfl

end Discourse.Centering
