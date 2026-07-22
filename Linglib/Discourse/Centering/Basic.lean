import Linglib.Discourse.Centering.Defs
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Dedup

/-!
# Centering Theory — Cb, Cf, Cp
[grosz-joshi-weinstein-1995]

Forward- and backward-looking center operations, parameterized by
role ranker (`[CfRankerOf E R]`) and realizes-semantics (`[Realizes U E]`).
GJW's "unique Cb" claim is enforced by `cb`'s `Option E` return type.
-/

namespace Discourse.Centering

variable {E R : Type*}

/-! ### Default Realizes / Pronominalizes for Utterance -/

section Instances

variable [DecidableEq E]

/-- For a list-of-realizations utterance, `realizes` is existence of a
    realization whose entity is the target. -/
instance utteranceRealizes : Realizes (Utterance E R) E where
  Rel u e := ∃ r ∈ u.realizations, r.entity = e
  decRel _ _ := inferInstance

/-- For a list-of-realizations utterance, `pronominalizes` requires a
    realization of `e` whose `isPronoun` flag is true. -/
instance utterancePronominalizes : Pronominalizes (Utterance E R) E where
  Rel u e := ∃ r ∈ u.realizations, r.entity = e ∧ r.isPronoun = true
  decRel _ _ := inferInstance

/-- A flat list of entities realizes by membership (minimal
    "bag of referents" representation). -/
instance listRealizes : Realizes (List E) E where
  Rel es e := e ∈ es
  decRel _ _ := inferInstance

@[simp] theorem realizes_list_iff (es : List E) (e : E) :
    realizes es e ↔ e ∈ es := Iff.rfl

end Instances

namespace Utterance

section Realization

variable [DecidableEq E]

/-- Existential characterization of `realizes` on a list-of-realizations
    utterance. -/
theorem realizes_iff (u : Utterance E R) (e : E) :
    realizes u e ↔ ∃ r ∈ u.realizations, r.entity = e := Iff.rfl

/-- Existential characterization of `pronominalizes` on a
    list-of-realizations utterance. -/
theorem pronominalizes_iff (u : Utterance E R) (e : E) :
    pronominalizes u e ↔ ∃ r ∈ u.realizations, r.entity = e ∧ r.isPronoun = true := Iff.rfl

end Realization

/-! ### Cf, Cp via insertion sort on rank -/

section Cf

variable [CfRankerOf E R]

/-- Insert `r` into a rank-descending Cf list, after any equally-ranked
    elements (surface order as stable tiebreaker). -/
def cfInsert (r : Realization E R) :
    List (Realization E R) → List (Realization E R)
  | []      => [r]
  | x :: xs =>
    if CfRankerOf.rank x < CfRankerOf.rank r then
      r :: x :: xs
    else
      x :: cfInsert r xs

/-- Forward-looking centers via insertion-sort by rank (decide-reducible). -/
def cf (u : Utterance E R) : List E :=
  (u.realizations.foldr cfInsert []).map (·.entity)

/-- The top-ranked Cf element ("preferred center", Cp). -/
def cp (u : Utterance E R) : Option E := u.cf.head?

@[simp] theorem cf_mk_nil : (Utterance.mk [] : Utterance E R).cf = [] := rfl

@[simp] theorem cp_mk_nil : (Utterance.mk [] : Utterance E R).cp = none := rfl

/-- The preferred center, when defined, is a forward-looking center. -/
theorem cp_mem_cf {u : Utterance E R} {e : E} (h : u.cp = some e) :
    e ∈ u.cf :=
  List.mem_of_mem_head? (Option.mem_def.mpr h)

/-- `cfInsert` preserves membership: every element of the result is either
    the inserted element or already in the list. -/
theorem mem_cfInsert_iff (r : Realization E R)
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
theorem cfInsert_perm (r : Realization E R)
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
theorem cfRealizations_perm (u : Utterance E R) :
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
theorem mem_cf_iff (u : Utterance E R) (e : E) :
    e ∈ u.cf ↔ ∃ r ∈ u.realizations, r.entity = e := by
  unfold cf
  rw [List.mem_map]
  refine ⟨?_, ?_⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, (cfRealizations_perm u).mem_iff.mp hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, (cfRealizations_perm u).mem_iff.mpr hr, rfl⟩

end Cf

end Utterance

/-! ### Cb (backward-looking center) -/

section Cb

variable [CfRankerOf E R] {U : Type*} [Realizes U E]

/-- Backward-looking center: the highest-ranked element of `prev.cf`
    realized in `cur`. Polymorphic in `cur`'s type via `Realizes U E`. -/
def cb (prev : Utterance E R) (cur : U) : Option E :=
  prev.cf.find? (fun e => decide (realizes cur e))

variable {prev : Utterance E R} {cur : U} {e : E}

/-- Locality of Cb ([grosz-joshi-weinstein-1995]): `cb prev cur`
    is always drawn from `prev.cf`, never further back. -/
theorem cb_mem_prev_cf (h : cb prev cur = some e) : e ∈ prev.cf :=
  List.mem_of_find?_eq_some h

/-- The Cb is realized in the current utterance: when `cb prev cur` is
    `some e`, `realizes cur e` holds. -/
theorem realizes_of_cb (h : cb prev cur = some e) : realizes cur e :=
  decide_eq_true_eq.mp (List.find?_eq_some_iff_append.mp h).1

/-- `cb prev cur = some e` iff `e ∈ prev.cf` is realized in `cur` with
    no higher-ranked element of `prev.cf` also realized in `cur`. -/
theorem cb_eq_some_iff :
    cb prev cur = some e ↔
      ∃ l₁ l₂, prev.cf = l₁ ++ e :: l₂ ∧
        (∀ e' ∈ l₁, ¬ realizes cur e') ∧
        realizes cur e := by
  unfold cb
  rw [List.find?_eq_some_iff_append]
  simp only [decide_eq_true_eq, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
  tauto

/-- `cb` is `none` iff no element of `prev.cf` is realized in `cur`. -/
theorem cb_eq_none_iff :
    cb prev cur = none ↔ ∀ e ∈ prev.cf, ¬ realizes cur e := by
  unfold cb
  rw [List.find?_eq_none]
  simp only [decide_eq_true_eq]

@[simp] theorem cb_empty_prev (u : U) :
    cb (Utterance.mk [] : Utterance E R) u = none := rfl

/-! ### cbAll (multi-CB under partial ranking) -/

variable [DecidableEq E]

/-- Multi-CB: entities tied at the highest rank-among-realized,
    deduplicated. Length ≤ 1 under total rankings; can exceed 1
    under partial rankings (PSDH §5.3.4). -/
def cbAll (prev : Utterance E R) (cur : U) : List E :=
  let realized := prev.realizations.filter (fun r => decide (realizes cur r.entity))
  match realized.argmax (fun r => CfRankerOf.rank r) with
  | none => []
  | some top =>
    ((realized.filter (fun r => CfRankerOf.rank r = CfRankerOf.rank top)).map
      (·.entity)).dedup

@[simp] theorem cbAll_empty_prev (u : U) :
    cbAll (Utterance.mk [] : Utterance E R) u = [] := rfl

/-- Every entity in `cbAll prev cur` corresponds to some realization
    in `prev` realized in `cur`. -/
theorem mem_cbAll_exists_realization (h : e ∈ cbAll prev cur) :
    ∃ r ∈ prev.realizations, r.entity = e ∧ realizes cur r.entity := by
  simp only [cbAll] at h
  split at h
  · simp at h
  · simp only [List.mem_dedup, List.mem_map, List.mem_filter] at h
    obtain ⟨r, ⟨⟨hr_mem, hr_real⟩, _⟩, hr_eq⟩ := h
    exact ⟨r, hr_mem, hr_eq, decide_eq_true_eq.mp hr_real⟩

/-- Every entity in `cbAll prev cur` is realized in `cur`. -/
theorem mem_cbAll_realized (h : e ∈ cbAll prev cur) : realizes cur e := by
  obtain ⟨_, _, hr_eq, hr_real⟩ := mem_cbAll_exists_realization h
  exact hr_eq ▸ hr_real

/-- The multi-CB set is a subset of `prev.cf` (locality for `cbAll`). -/
theorem mem_cbAll_mem_prev_cf (h : e ∈ cbAll prev cur) : e ∈ prev.cf := by
  obtain ⟨r, hr_in, hr_eq, _⟩ := mem_cbAll_exists_realization h
  rw [Utterance.mem_cf_iff]
  exact ⟨r, hr_in, hr_eq⟩

end Cb

end Discourse.Centering
