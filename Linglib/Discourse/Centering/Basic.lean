import Linglib.Discourse.Centering.Defs
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Dedup

/-!
# Centering Theory — Cb, Cf, Cp
@cite{grosz-joshi-weinstein-1995}

Forward- and backward-looking center operations, parameterized by
role ranker (`[CfRankerOf E R]`) and realizes-semantics (`[Realizes U E]`).
GJW's "unique Cb" claim is enforced by `cb`'s `Option E` return type.
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

/-- A flat list of entities realizes by membership (minimal
    "bag of referents" representation). -/
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

/-- Insert `r` into a rank-descending Cf list, after any equally-ranked
    elements (surface order as stable tiebreaker). -/
def cfInsert [CfRankerOf E R]
    (r : Realization E R) : List (Realization E R) → List (Realization E R)
  | []      => [r]
  | x :: xs =>
    if CfRankerOf.rank x < CfRankerOf.rank r then
      r :: x :: xs
    else
      x :: cfInsert r xs

/-- Forward-looking centers via insertion-sort by rank (decide-reducible). -/
def cf [CfRankerOf E R] (u : Utterance E R) : List E :=
  (u.realizations.foldr cfInsert []).map (·.entity)

/-- The top-ranked Cf element ("preferred center", Cp). -/
def cp [CfRankerOf E R] (u : Utterance E R) : Option E := u.cf.head?

end Utterance

-- ════════════════════════════════════════════════════
-- § 2a. cf / cp characterization API
-- ════════════════════════════════════════════════════

namespace Utterance

@[simp] theorem cf_mk_nil [CfRankerOf E R] :
    (Utterance.mk [] : Utterance E R).cf = [] := rfl

@[simp] theorem cp_mk_nil [CfRankerOf E R] :
    (Utterance.mk [] : Utterance E R).cp = none := rfl

/-- `cfInsert` preserves membership: every element of the result is either
    the inserted element or already in the list. -/
theorem mem_cfInsert_iff [CfRankerOf E R] (r : Realization E R)
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
theorem cfInsert_perm [CfRankerOf E R] (r : Realization E R)
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
theorem cfRealizations_perm [CfRankerOf E R] (u : Utterance E R) :
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
theorem mem_cf_iff [CfRankerOf E R] (u : Utterance E R) (e : E) :
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

/-- Backward-looking center: the highest-ranked element of `prev.cf`
    realized in `cur`. Polymorphic in `cur`'s type via `Realizes U E`. -/
def cb [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) : Option E :=
  prev.cf.find? (Realizes.decide cur)

/-- Locality of Cb (@cite{grosz-joshi-weinstein-1995}): `cb prev cur`
    is always drawn from `prev.cf`, never further back. -/
theorem cb_mem_prev_cf [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    {prev : Utterance E R} {cur : U} {e : E} (h : cb prev cur = some e) :
    e ∈ prev.cf :=
  List.mem_of_find?_eq_some h

/-- The Cb is realized in the current utterance: when `cb prev cur` is
    `some e`, the realizes-relation holds of `(cur, e)`. -/
theorem decide_of_cb [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    {prev : Utterance E R} {cur : U} {e : E} (h : cb prev cur = some e) :
    Realizes.decide cur e = true :=
  List.find?_eq_some_iff_append.mp h |>.1

/-- `cb prev cur = some e` iff `e ∈ prev.cf` is realized in `cur` with
    no higher-ranked element of `prev.cf` also realized in `cur`. -/
theorem cb_eq_some_iff [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
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
theorem cb_eq_none_iff [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    {prev : Utterance E R} {cur : U} :
    cb prev cur = none ↔ ∀ e ∈ prev.cf, Realizes.decide cur e = false := by
  unfold cb
  rw [List.find?_eq_none]
  refine ⟨fun h e he => ?_, fun h e he => ?_⟩
  · simpa using h e he
  · simp [h e he]

@[simp] theorem cb_empty_prev [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (cur : U) : cb (Utterance.mk [] : Utterance E R) cur = none := rfl

-- ════════════════════════════════════════════════════
-- § 4. cbAll (multi-CB under partial ranking)
-- ════════════════════════════════════════════════════

/-- Multi-CB: entities tied at the highest rank-among-realized,
    deduplicated. Length ≤ 1 under total rankings; can exceed 1
    under partial rankings (PSDH §5.3.4). -/
def cbAll [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) : List E :=
  let realized := prev.realizations.filter (fun r => Realizes.decide cur r.entity)
  match realized with
  | [] => []
  | _ :: _ =>
    let topRank := match realized.argmax (fun r => CfRankerOf.rank r) with
                   | none => 0
                   | some top => CfRankerOf.rank top
    ((realized.filter (fun r => CfRankerOf.rank r = topRank)).map (·.entity)).dedup

@[simp] theorem cbAll_empty_prev [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    (cur : U) : cbAll (Utterance.mk [] : Utterance E R) cur = [] := rfl

/-- Every entity in `cbAll prev cur` corresponds to some realization
    in `prev` realized in `cur`. -/
theorem mem_cbAll_exists_realization [DecidableEq E] [CfRankerOf E R]
    {U : Type} [Realizes U E]
    {prev : Utterance E R} {cur : U} {e : E} (h : e ∈ cbAll prev cur) :
    ∃ r ∈ prev.realizations, r.entity = e ∧ Realizes.decide cur r.entity = true := by
  unfold cbAll at h
  cases hf : prev.realizations.filter (fun r => Realizes.decide cur r.entity) with
  | nil => simp [hf] at h
  | cons head tail =>
    simp only [hf, List.mem_dedup, List.mem_map, List.mem_filter] at h
    obtain ⟨r, ⟨hr_in_filtered, _⟩, hr_eq⟩ := h
    have : r ∈ prev.realizations.filter (fun r => Realizes.decide cur r.entity) := by
      rw [hf]; exact hr_in_filtered
    rw [List.mem_filter] at this
    exact ⟨r, this.1, hr_eq, hr_eq ▸ this.2⟩

/-- Every entity in `cbAll prev cur` is realized in `cur`. -/
theorem mem_cbAll_realized [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    {prev : Utterance E R} {cur : U} {e : E} (h : e ∈ cbAll prev cur) :
    Realizes.decide cur e = true := by
  obtain ⟨r, _, hr_eq, hr_real⟩ := mem_cbAll_exists_realization h
  exact hr_eq ▸ hr_real

/-- The multi-CB set is a subset of `prev.cf` (locality for `cbAll`). -/
theorem mem_cbAll_mem_prev_cf [DecidableEq E] [CfRankerOf E R] {U : Type} [Realizes U E]
    {prev : Utterance E R} {cur : U} {e : E} (h : e ∈ cbAll prev cur) :
    e ∈ prev.cf := by
  obtain ⟨r, hr_in, hr_eq, _⟩ := mem_cbAll_exists_realization h
  rw [Utterance.mem_cf_iff]
  exact ⟨r, hr_in, hr_eq⟩

end Discourse.Centering
