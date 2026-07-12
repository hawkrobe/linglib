/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Linglib.Phonology.Autosegmental.AR

/-!
# Autosegmental realization of strings

The **realization** of a string maps each symbol to its autosegmental graph primitive
and concatenates them ([jardine-2019]'s mapping `g`): `realize g₀ w = ∏ (w.map g₀)` in
the concatenation monoid `Monoid (AR α β)`.

This is a string→AR **monoid homomorphism** (`realize_append`), the exact analogue —
one categorical level up — of the string→tier-string projection
`TierProjection.apply` (= `List.filterMap`, also concat-distributing): both are
free-monoid homomorphisms built from a per-symbol map, used to define a subregular
class as a *preimage* (`Phonology/Autosegmental/ASL.lean` for the realization,
`Subregular.Language.TierStrictlyLocal` for the projection). The realization keeps the
association structure the tier projection discards — see [jardine-2019] on `ASL` vs
`TSL`.
-/

namespace Autosegmental

variable {S : Type*} {α β : Type*}

/-- **Realize** a string as an autosegmental representation: concatenate the graph
    primitives `g₀ a` of its symbols ([jardine-2019]'s `g`). -/
def realize (g₀ : S → AR α β) (w : List S) : AR α β := (w.map g₀).prod

@[simp] theorem realize_nil (g₀ : S → AR α β) : realize g₀ [] = AR.empty := rfl

@[simp] theorem realize_cons (g₀ : S → AR α β) (a : S) (w : List S) :
    realize g₀ (a :: w) = (g₀ a).concat (realize g₀ w) := rfl

/-- **The realization is a monoid homomorphism**: it distributes over concatenation —
    the string→AR analogue of `TierProjection.apply_append`. -/
theorem realize_append (g₀ : S → AR α β) (xs ys : List S) :
    realize g₀ (xs ++ ys) = (realize g₀ xs).concat (realize g₀ ys) := by
  simp only [realize, List.map_append, List.prod_append]; rfl

/-! ### Tier projections

The realization composed with a tier accessor is itself a free-monoid hom into that
tier's free monoid: `upperProj g₀` sends a string to the concatenation of its symbols'
upper tiers (the underlying list of `realize g₀ w`'s upper tier), and likewise
`lowerProj`. These factor the realization's tier content through `FreeMonoid` and are
the bridge used to place link-free `ASL` sets in `SF` (`Studies.Jardine2019`): a
per-tier factor constraint on the realization is the `comap` of a factor language along
the tier projection. -/

/-- The upper-tier realization as a free-monoid hom `FreeMonoid S →* FreeMonoid α`:
each symbol maps to its primitive's upper tier, concatenated. -/
def upperProj (g₀ : S → AR α β) : FreeMonoid S →* FreeMonoid α :=
  FreeMonoid.lift (fun s => FreeMonoid.ofList (g₀ s).upper.toList)

/-- The lower-tier realization as a free-monoid hom `FreeMonoid S →* FreeMonoid β`. -/
def lowerProj (g₀ : S → AR α β) : FreeMonoid S →* FreeMonoid β :=
  FreeMonoid.lift (fun s => FreeMonoid.ofList (g₀ s).lower.toList)

@[simp] theorem upperProj_of (g₀ : S → AR α β) (s : S) :
    upperProj g₀ (FreeMonoid.of s) = FreeMonoid.ofList (g₀ s).upper.toList :=
  FreeMonoid.lift_eval_of _ _

@[simp] theorem lowerProj_of (g₀ : S → AR α β) (s : S) :
    lowerProj g₀ (FreeMonoid.of s) = FreeMonoid.ofList (g₀ s).lower.toList :=
  FreeMonoid.lift_eval_of _ _

/-- The upper tier of a realization is its upper projection: `(realize g₀ w).upper`'s
underlying list is `upperProj g₀ w`. -/
theorem realize_upper_toList (g₀ : S → AR α β) (w : List S) :
    (realize g₀ w).upper.toList = upperProj g₀ (FreeMonoid.ofList w) := by
  induction w with
  | nil => rw [realize_nil, show FreeMonoid.ofList ([] : List S) = 1 from rfl, map_one]; rfl
  | cons s w ih =>
    rw [realize_cons, AR.upper_concat, LabeledTuple.toList_concat, ih, FreeMonoid.ofList_cons,
      map_mul, upperProj_of]
    rfl

/-- The lower tier of a realization is its lower projection. -/
theorem realize_lower_toList (g₀ : S → AR α β) (w : List S) :
    (realize g₀ w).lower.toList = lowerProj g₀ (FreeMonoid.ofList w) := by
  induction w with
  | nil => rw [realize_nil, show FreeMonoid.ofList ([] : List S) = 1 from rfl, map_one]; rfl
  | cons s w ih =>
    rw [realize_cons, AR.lower_concat, LabeledTuple.toList_concat, ih, FreeMonoid.ofList_cons,
      map_mul, lowerProj_of]
    rfl

/-! ### Linearization: the association-state string of an AR

The inverse direction of the bridge. Where `realize` builds an AR from a string,
`linearize` reads the **association-state string** off an AR: per timing-tier position,
its label together with the labels of the melody nodes linked to it, in tier order. This
is the linearisation phonologists use implicitly when writing a tonal input as a string of
TBU symbols — [jardine-2016] §4.4: each string symbol records one timing unit's
associations, so transducer look-ahead is measured on the timing tier. Like `realize`, it
is a monoid homomorphism into `(List, ++)` (`AR.linearize_concat`), so the linearization
of a realization is the concatenation of the per-symbol association profiles
(`linearize_realize`). -/

/-- The labels of the upper (melody) nodes linked to lower position `j`, in tier order. -/
def Graph.linkedLabels (A : Graph α β) (j : ℕ) : List α :=
  ((List.range A.upper.len).filter fun i => decide ((i, j) ∈ A.links)).filterMap A.upper.get?

/-- Positions inside `A` see only `A`'s links. -/
theorem Graph.linkedLabels_concat_left {A B : Graph α β} (hA : A.InBounds) {j : ℕ}
    (hj : j < A.lower.len) :
    (A.concat B).linkedLabels j = A.linkedLabels j := by
  unfold Graph.linkedLabels
  rw [Graph.upper_concat, LabeledTuple.concat_len, List.range_add, List.filter_append,
    List.filterMap_append]
  have h₂ : ((List.range B.upper.len).map (A.upper.len + ·)).filter
      (fun i => decide ((i, j) ∈ (A.concat B).links)) = [] := by
    rw [List.filter_eq_nil_iff]
    rintro i hi
    simp only [List.mem_map, List.mem_range] at hi
    obtain ⟨i', -, rfl⟩ := hi
    simp only [Graph.links_concat, Finset.mem_union, Finset.mem_image, shiftLink_apply,
      Prod.mk.injEq, decide_eq_true_eq, not_or, not_exists]
    constructor
    · intro hmem
      exact absurd (hA _ hmem).1 (by omega)
    · rintro ⟨p1, p2⟩ ⟨hp, h1, h2⟩
      omega
  have h₁ : (List.range A.upper.len).filter (fun i => decide ((i, j) ∈ (A.concat B).links))
      = (List.range A.upper.len).filter (fun i => decide ((i, j) ∈ A.links)) := by
    refine List.filter_congr fun i hi => ?_
    simp only [List.mem_range] at hi
    simp only [decide_eq_decide, Graph.links_concat, Finset.mem_union, Finset.mem_image,
      shiftLink_apply, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨p, hp, h1, h2⟩)
      · exact h
      · omega
    · exact Or.inl
  rw [h₁, h₂, List.filterMap_nil, List.append_nil]
  exact List.filterMap_congr fun i hi => by
    have hilt : i < A.upper.len := by
      simp only [List.mem_filter, List.mem_range] at hi
      exact hi.1
    exact LabeledTuple.get?_concat_left hilt

/-- Positions past `A` see exactly `B`'s links, shifted down by `A`'s length. -/
theorem Graph.linkedLabels_concat_right {A B : Graph α β} (hA : A.InBounds) {j : ℕ}
    (hj : A.lower.len ≤ j) :
    (A.concat B).linkedLabels j = B.linkedLabels (j - A.lower.len) := by
  unfold Graph.linkedLabels
  rw [Graph.upper_concat, LabeledTuple.concat_len, List.range_add, List.filter_append,
    List.filterMap_append]
  have h₁ : (List.range A.upper.len).filter
      (fun i => decide ((i, j) ∈ (A.concat B).links)) = [] := by
    rw [List.filter_eq_nil_iff]
    rintro i hi
    simp only [List.mem_range] at hi
    simp only [Graph.links_concat, Finset.mem_union, Finset.mem_image, shiftLink_apply,
      Prod.mk.injEq, decide_eq_true_eq, not_or, not_exists]
    constructor
    · intro hmem
      exact absurd (hA _ hmem).2 (by omega)
    · rintro ⟨p1, p2⟩ ⟨hp, h1, h2⟩
      omega
  rw [h₁, List.filterMap_nil, List.nil_append, List.filter_map, List.filterMap_map]
  have h₂ : (List.range B.upper.len).filter
      ((fun i => decide ((i, j) ∈ (A.concat B).links)) ∘ (A.upper.len + ·))
      = (List.range B.upper.len).filter
          (fun i => decide ((i, j - A.lower.len) ∈ B.links)) := by
    refine List.filter_congr fun i hi => ?_
    simp only [Function.comp_apply, decide_eq_decide, Graph.links_concat, Finset.mem_union,
      Finset.mem_image, shiftLink_apply, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨⟨p1, p2⟩, hp, h1, h2⟩)
      · exact absurd (hA _ h).1 (by omega)
      · obtain rfl : p1 = i := by omega
        obtain rfl : p2 = j - A.lower.len := by omega
        exact hp
    · intro h
      exact Or.inr ⟨(i, j - A.lower.len), h, by omega, by omega⟩
  rw [h₂]
  exact List.filterMap_congr fun i hi => by
    rw [Function.comp_apply]
    exact LabeledTuple.get?_concat_right A.upper B.upper i

/-- `A.linearize` is the association-state string of `A` ([jardine-2016] (40)): position
`j` carries its timing-unit label together with the labels of the melody nodes linked
to it. -/
def AR.linearize (A : AR α β) : List (β × List α) :=
  A.lower.toList.mapIdx fun j b => (b, A.toGraph.linkedLabels j)

@[simp] theorem AR.linearize_length (A : AR α β) : A.linearize.length = A.lower.len := by
  simp [AR.linearize]

theorem AR.linearize_getElem? (A : AR α β) (j : ℕ) :
    A.linearize[j]? = (A.lower.get? j).map fun b => (b, A.toGraph.linkedLabels j) := by
  simp [AR.linearize, List.getElem?_mapIdx, LabeledTuple.get?_eq_getElem?]

/-- Linkedness is readable off the linearization: slot `j` is linked iff its
association-state entry carries a nonempty melody. -/
theorem AR.isLinkedLower_iff_linearize (A : AR α β) {j : ℕ} :
    A.toGraph.IsLinkedLower j ↔ ∃ b as, A.linearize[j]? = some (b, as) ∧ as ≠ [] := by
  rw [Graph.isLinkedLower_iff, AR.linearize_getElem?]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨hiu, hjl⟩ := A.inBounds _ hi
    obtain ⟨b, hb⟩ : ∃ b, A.lower.get? j = some b := by
      rw [LabeledTuple.get?_eq_getElem?]
      exact ⟨_, List.getElem?_eq_getElem (by simpa using hjl)⟩
    refine ⟨b, A.toGraph.linkedLabels j, by rw [hb]; rfl, fun hnil => ?_⟩
    have hmem : i ∈ (List.range A.upper.len).filter fun i => decide ((i, j) ∈ A.links) := by
      simp [List.mem_filter, hiu, hi]
    have hnone := List.filterMap_eq_nil_iff.mp hnil i hmem
    rw [LabeledTuple.get?_eq_getElem?, List.getElem?_eq_none_iff] at hnone
    simp at hnone
    omega
  · rintro ⟨b, as, hsome, hne⟩
    obtain ⟨b', hb', heq⟩ := Option.map_eq_some_iff.mp hsome
    obtain ⟨-, rfl⟩ : b' = b ∧ A.toGraph.linkedLabels j = as := by
      simpa [Prod.ext_iff] using heq
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨i, hif, -⟩ := List.mem_filterMap.mp hx
    rw [List.mem_filter] at hif
    exact ⟨i, of_decide_eq_true hif.2⟩

@[simp] theorem AR.linearize_empty : (AR.empty : AR α β).linearize = [] := by
  have h : (Graph.empty : Graph α β).lower.toList = [] :=
    List.eq_nil_of_length_eq_zero (by simp [Graph.empty])
  simp [AR.linearize, h]

/-- Linearization sends concatenation of ARs to concatenation of association-state
strings; the `inBounds` fields keep each side's links on its own positions. -/
theorem AR.linearize_concat (A B : AR α β) :
    (A.concat B).linearize = A.linearize ++ B.linearize := by
  refine List.ext_getElem? fun j => ?_
  rw [AR.linearize_getElem?]
  rcases Nat.lt_or_ge j A.lower.len with hj | hj
  · rw [List.getElem?_append_left (by rw [AR.linearize_length]; exact hj),
      AR.linearize_getElem?, AR.lower_concat, LabeledTuple.get?_concat_left hj,
      AR.toGraph_concat, Graph.linkedLabels_concat_left A.inBounds hj]
  · rw [List.getElem?_append_right (by rw [AR.linearize_length]; exact hj),
      AR.linearize_getElem?, AR.linearize_length, AR.lower_concat, AR.toGraph_concat,
      Graph.linkedLabels_concat_right A.inBounds hj,
      show j = A.lower.len + (j - A.lower.len) from by omega,
      LabeledTuple.get?_concat_right, Nat.add_sub_cancel_left]

/-- The linearization of a realization is the concatenation of the per-symbol
association profiles ([jardine-2016] (40)). -/
theorem linearize_realize (g₀ : S → AR α β) (w : List S) :
    (realize g₀ w).linearize = w.flatMap fun a => (g₀ a).linearize := by
  induction w with
  | nil => simp
  | cons a w ih => rw [realize_cons, AR.linearize_concat, ih, List.flatMap_cons]

end Autosegmental
