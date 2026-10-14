/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.OCP

/-!
# Merging concatenation of autosegmental representations

Jardine and Heinz concatenate two representations by bridging them and merging the seam: on the
melody tier, the last node of the first factor and the first node of the second become one node
when they bear the same label, and that node keeps the lines of both. `AR.mergeConcat m X Y` is
this concatenation, the repointing of `X ⊗ Y` along `OCP.mergeIdx`. A string realizes as the
left fold of merging concatenation over its symbols' primitives (`AR.mergeRealize`).

The merge happens at the seam only, so a primitive that itself violates the OCP keeps its
violation. Collapsing every run after concatenating, as `realizeMerged` does, would merge it
away. The two realizations agree when the primitives are OCP-clean, because the collapse of a
concatenation is the merging concatenation of the collapses.

## Main definitions

* `AR.mergeConcat`: concatenation with the melody seam merged.
* `AR.mergeRealize`: the realization of a string as a left fold of merging concatenation.

## Main statements

* `AR.mergeConcatAssocFullIso`: merging concatenation is associative.
* `AR.noCrossing_mergeConcat`, `AR.isCleanAt_mergeConcat`: it preserves the NCC, and the OCP of
  OCP-clean factors.
* `AR.collapseTensorFullIso`: the collapse of a concatenation is the merging concatenation of
  the collapses.
* `AR.nonempty_fullIso_realizeMerged`: over OCP-clean primitives, the realization by merging
  concatenation is the collapsed realization.

## Implementation notes

Jardine and Heinz merge at every melody tier; `mergeConcat` merges at one tier `m`, the two-tier
case their primitives assume. They prove associativity for the graphs generated from primitives,
whose tiers are strings; Axioms 1 and 2 make every tier a string, so here it holds for all
finite representations.

## References

* [jardine-heinz-2015]
* [jardine-2019]
-/

@[expose] public section

namespace Autosegmental

open CategoryTheory
open scoped MonoidalCategory

namespace AR

variable {ι : Type*} [DecidableEq ι] {τ : ι → Type*} (m : ι) [DecidableEq (τ m)]
variable (X Y : TieredAR ι τ) [Finite X.obj.V] [Finite Y.obj.V]

/-- Where tier `i` of the second factor starts in a merging concatenation. -/
noncomputable def mergeOffset (i : ι) : ℕ :=
  if i = m then OCP.mergeOffset (X.tierWord m) (Y.tierWord m) else X.tierLength i

section
variable {m X Y}

theorem repointIdx_mergeIdx_of_lt {i : ι} {p : ℕ} (hp : p < X.tierLength i) :
    repointIdx m (OCP.mergeIdx (X.tierWord m) (Y.tierWord m)) i p = p := by
  rcases eq_or_ne i m with rfl | hi
  · exact (repointIdx_self p).trans (OCP.mergeIdx_of_lt (by simpa using hp))
  · exact repointIdx_of_ne hi p

theorem repointIdx_mergeIdx_add (i : ι) (p : ℕ) :
    repointIdx m (OCP.mergeIdx (X.tierWord m) (Y.tierWord m)) i (X.tierLength i + p) =
      mergeOffset m X Y i + p := by
  rcases eq_or_ne i m with rfl | hi
  · rw [repointIdx_self, ← length_tierWord, OCP.mergeIdx_length_add]
    simp [mergeOffset]
  · simp [mergeOffset, hi]

theorem repointIdx_runIdx_append_left {i : ι} {p : ℕ} (hp : p < X.tierLength i) :
    repointIdx m (OCP.runIdx (X.tierWord m ++ Y.tierWord m)) i p =
      repointIdx m (OCP.runIdx (X.tierWord m)) i p := by
  rcases eq_or_ne i m with rfl | hi
  · simp only [repointIdx_self]
    exact OCP.runIdx_append_left (by simpa using hp)
  · simp [hi]

end

variable [Finite ι]

/-- **Merging concatenation**: `X ⊗ Y` with the seam of melody tier `m` merged, the last node of
`X` and the first node of `Y` becoming one node when they bear the same label. -/
noncomputable def mergeConcat : TieredAR ι τ :=
  (X ⊗ Y).repoint m (OCP.mergeAppend (X.tierWord m) (Y.tierWord m))
    (OCP.mergeIdx (X.tierWord m) (Y.tierWord m))

instance : Finite (mergeConcat m X Y).obj.V :=
  inferInstanceAs (Finite ((X ⊗ Y).repoint m _ _).obj.V)

variable {m X Y}

@[simp] theorem tierWord_mergeConcat_self :
    (mergeConcat m X Y).tierWord m = OCP.mergeAppend (X.tierWord m) (Y.tierWord m) :=
  tierWord_repoint_self

@[simp] theorem tierWord_mergeConcat_of_ne {i : ι} (h : i ≠ m) :
    (mergeConcat m X Y).tierWord i = X.tierWord i ++ Y.tierWord i := by
  simp [mergeConcat, h]

@[simp] theorem tierLength_mergeConcat_of_ne {i : ι} (h : i ≠ m) :
    (mergeConcat m X Y).tierLength i = X.tierLength i + Y.tierLength i := by
  rw [← length_tierWord, tierWord_mergeConcat_of_ne h]
  simp

/-- A link of a merging concatenation is a link of the first factor, or a link of the second
shifted to where that factor starts. -/
theorem link_mergeConcat (i j : ι) (r s : ℕ) :
    (mergeConcat m X Y).link i j r s ↔ X.link i j r s ∨
      ∃ p q, Y.link i j p q ∧ mergeOffset m X Y i + p = r ∧ mergeOffset m X Y j + q = s := by
  rw [show (mergeConcat m X Y).link i j r s ↔ ((X ⊗ Y).repoint m _ _).link i j r s from Iff.rfl,
    link_repoint (fun p hp ↦ OCP.mergeIdx_lt (by simpa using hp))]
  constructor
  · rintro ⟨p, q, hl, rfl, rfl⟩
    rcases (link_tensor i j p q).mp hl with hX | ⟨hp, hq, hY⟩
    · obtain ⟨hp, hq, -⟩ := id hX
      left
      rwa [repointIdx_mergeIdx_of_lt hp, repointIdx_mergeIdx_of_lt hq]
    · refine Or.inr ⟨_, _, hY, ?_, ?_⟩
      · rw [← repointIdx_mergeIdx_add, Nat.add_sub_cancel' hp]
      · rw [← repointIdx_mergeIdx_add, Nat.add_sub_cancel' hq]
  · rintro (hX | ⟨p, q, hY, rfl, rfl⟩)
    · obtain ⟨hp, hq, -⟩ := id hX
      exact ⟨r, s, (link_tensor i j r s).mpr (Or.inl hX), repointIdx_mergeIdx_of_lt hp,
        repointIdx_mergeIdx_of_lt hq⟩
    · exact ⟨X.tierLength i + p, X.tierLength j + q,
        (link_tensor i j _ _).mpr (Or.inr ⟨by omega, by omega, by simpa using hY⟩),
        repointIdx_mergeIdx_add i p, repointIdx_mergeIdx_add j q⟩

/-! ### The theorems of Jardine and Heinz -/

/-- The empty representation is a left unit ([jardine-heinz-2015] Theorem 1). -/
noncomputable def emptyMergeConcatFullIso : Graph.Iso (mergeConcat m (𝟙_ _) X).obj X.obj :=
  fullIsoOfReaderEq (fun i ↦ by rcases eq_or_ne i m with rfl | hi <;> simp [*])
    fun i j r s ↦ by simp [link_mergeConcat, mergeOffset]

/-- The empty representation is a right unit ([jardine-heinz-2015] Theorem 1). -/
noncomputable def mergeConcatEmptyFullIso : Graph.Iso (mergeConcat m X (𝟙_ _)).obj X.obj :=
  fullIsoOfReaderEq (fun i ↦ by rcases eq_or_ne i m with rfl | hi <;> simp [*])
    fun i j r s ↦ by simp [link_mergeConcat]

/-- Merging concatenation respects full isomorphism. -/
noncomputable def mergeConcatCongr {X' Y' : TieredAR ι τ} [Finite X'.obj.V] [Finite Y'.obj.V]
    (e₁ : Graph.Iso X.obj X'.obj) (e₂ : Graph.Iso Y.obj Y'.obj) :
    Graph.Iso (mergeConcat m X Y).obj (mergeConcat m X' Y').obj :=
  fullIsoOfReaderEq
    (fun i ↦ by
      rcases eq_or_ne i m with rfl | hi
      · rw [tierWord_mergeConcat_self, tierWord_mergeConcat_self, tierWord_eq_of_iso e₁,
          tierWord_eq_of_iso e₂]
      · rw [tierWord_mergeConcat_of_ne hi, tierWord_mergeConcat_of_ne hi, tierWord_eq_of_iso e₁,
          tierWord_eq_of_iso e₂])
    fun i j r s ↦ by
      have ho (k : ι) : mergeOffset m X Y k = mergeOffset m X' Y' k := by
        rw [mergeOffset, mergeOffset, tierWord_eq_of_iso e₁, tierWord_eq_of_iso e₂,
          tierLength_eq_of_iso e₁]
      simp only [link_mergeConcat, ho]
      exact or_congr (link_iff_of_iso e₁ i j r s)
        (exists₂_congr fun p q ↦ and_congr_left' (link_iff_of_iso e₂ i j p q))

variable {Z : TieredAR ι τ} [Finite Z.obj.V]

theorem mergeOffset_mergeConcat_left (i : ι) :
    mergeOffset m (mergeConcat m X Y) Z i =
      mergeOffset m X (mergeConcat m Y Z) i + mergeOffset m Y Z i := by
  rcases eq_or_ne i m with rfl | hi
  · simp [mergeOffset, OCP.mergeOffset_mergeAppend_left]
  · simp [mergeOffset, hi]

theorem mergeOffset_mergeConcat_right {i : ι} (h : 0 < Y.tierLength i) :
    mergeOffset m X (mergeConcat m Y Z) i = mergeOffset m X Y i := by
  rcases eq_or_ne i m with rfl | hi
  · have hy : Y.tierWord i ≠ [] := List.length_pos_iff.mp (by simpa using h)
    simp [mergeOffset, OCP.mergeOffset_mergeAppend_right hy]
  · simp [mergeOffset, hi]

/-- Merging concatenation is associative ([jardine-heinz-2015] Theorem 3). -/
noncomputable def mergeConcatAssocFullIso :
    Graph.Iso (mergeConcat m (mergeConcat m X Y) Z).obj
      (mergeConcat m X (mergeConcat m Y Z)).obj :=
  fullIsoOfReaderEq
    (fun i ↦ by
      rcases eq_or_ne i m with rfl | hi
      · simp [OCP.mergeAppend_assoc]
      · simp [hi])
    fun i j r s ↦ by
      simp only [link_mergeConcat]
      constructor
      · rintro ((hX | ⟨p, q, hY, rfl, rfl⟩) | ⟨p, q, hZ, rfl, rfl⟩)
        · exact Or.inl hX
        · obtain ⟨hp, hq, -⟩ := id hY
          exact Or.inr ⟨p, q, Or.inl hY, by rw [mergeOffset_mergeConcat_right (by omega)],
            by rw [mergeOffset_mergeConcat_right (by omega)]⟩
        · exact Or.inr ⟨_, _, Or.inr ⟨p, q, hZ, rfl, rfl⟩,
            by rw [mergeOffset_mergeConcat_left]; omega,
            by rw [mergeOffset_mergeConcat_left]; omega⟩
      · rintro (hX | ⟨_, _, hY | ⟨p, q, hZ, rfl, rfl⟩, rfl, rfl⟩)
        · exact Or.inl (Or.inl hX)
        · obtain ⟨hp, hq, -⟩ := id hY
          exact Or.inl (Or.inr ⟨_, _, hY, by rw [mergeOffset_mergeConcat_right (by omega)],
            by rw [mergeOffset_mergeConcat_right (by omega)]⟩)
        · exact Or.inr ⟨p, q, hZ, by rw [mergeOffset_mergeConcat_left]; omega,
            by rw [mergeOffset_mergeConcat_left]; omega⟩

/-- Merging concatenation preserves the NCC, the inductive step of [jardine-heinz-2015]
Theorem 4. -/
theorem noCrossing_mergeConcat (hX : NoCrossing X.obj.edges X.obj.arcs)
    (hY : NoCrossing Y.obj.edges Y.obj.arcs) :
    NoCrossing (mergeConcat m X Y).obj.edges (mergeConcat m X Y).obj.arcs :=
  noCrossing_repoint (fun _ hp ↦ OCP.mergeIdx_lt (by simpa using hp)) OCP.mergeIdx_monotone
    (Graph.noCrossing_concat _ hX hY)

/-- Merging concatenation of OCP-clean factors is OCP-clean, the inductive step of
[jardine-heinz-2015] Theorem 5. -/
theorem isCleanAt_mergeConcat (hX : X.IsCleanAt m) (hY : Y.IsCleanAt m) :
    (mergeConcat m X Y).IsCleanAt m := by
  simpa [IsCleanAt] using OCP.isClean_mergeAppend hX hY

/-! ### Collapse as a homomorphism -/

private theorem repointIdx_runIdx_append_right {i : ι} {p : ℕ} (hp : p < Y.tierLength i) :
    repointIdx m (OCP.runIdx (X.tierWord m ++ Y.tierWord m)) i (X.tierLength i + p) =
      mergeOffset m (X.collapse m) (Y.collapse m) i + repointIdx m (OCP.runIdx (Y.tierWord m)) i p := by
  rcases eq_or_ne i m with rfl | hi
  · simp only [repointIdx_self, mergeOffset, ↓reduceIte, tierWord_collapse_self]
    rw [← length_tierWord]
    exact OCP.runIdx_append_right (by simpa using hp)
  · simp [mergeOffset, hi]

/-- The collapse of a concatenation is the merging concatenation of the collapses. -/
noncomputable def collapseTensorFullIso :
    Graph.Iso ((X ⊗ Y).collapse m).obj (mergeConcat m (X.collapse m) (Y.collapse m)).obj :=
  fullIsoOfReaderEq
    (fun i ↦ by
      rcases eq_or_ne i m with rfl | hi
      · simp [OCP.collapse_append]
      · simp [hi])
    fun i j r s ↦ by
      simp only [link_collapse, link_mergeConcat, tierWord_tensor]
      constructor
      · rintro ⟨p, q, hl, rfl, rfl⟩
        rcases (link_tensor i j p q).mp hl with hX | ⟨hp, hq, hY⟩
        · obtain ⟨hp, hq, -⟩ := id hX
          exact Or.inl ⟨p, q, hX, (repointIdx_runIdx_append_left hp).symm,
            (repointIdx_runIdx_append_left hq).symm⟩
        · obtain ⟨hp', hq', -⟩ := id hY
          refine Or.inr ⟨_, _, ⟨_, _, hY, rfl, rfl⟩, ?_, ?_⟩
          · rw [← repointIdx_runIdx_append_right hp', Nat.add_sub_cancel' hp]
          · rw [← repointIdx_runIdx_append_right hq', Nat.add_sub_cancel' hq]
      · rintro (⟨p, q, hX, rfl, rfl⟩ | ⟨_, _, ⟨p, q, hY, rfl, rfl⟩, rfl, rfl⟩)
        · obtain ⟨hp, hq, -⟩ := id hX
          exact ⟨p, q, (link_tensor i j p q).mpr (Or.inl hX),
            repointIdx_runIdx_append_left hp, repointIdx_runIdx_append_left hq⟩
        · obtain ⟨hp, hq, -⟩ := id hY
          exact ⟨X.tierLength i + p, X.tierLength j + q,
            (link_tensor i j _ _).mpr (Or.inr ⟨by omega, by omega, by simpa using hY⟩),
            repointIdx_runIdx_append_right hp, repointIdx_runIdx_append_right hq⟩

/-! ### Realization by merging concatenation -/

section Realize
variable (m) {S : Type*} (g₀ : S → TieredAR ι τ) [∀ s, Finite (g₀ s).obj.V]

/-- A step of the left fold: the merging concatenation of a stage with a symbol's primitive. -/
noncomputable def mergeStep (A : {A : TieredAR ι τ // Finite A.obj.V}) (s : S) :
    {A : TieredAR ι τ // Finite A.obj.V} :=
  haveI := A.2
  ⟨mergeConcat m A.1 (g₀ s), inferInstance⟩

/-- The realization of a string by merging concatenation, the left fold `g(uγ) = g(u) ∘ g(γ)`
from the empty representation ([jardine-heinz-2015] Definition 5). -/
noncomputable def mergeRealize (w : List S) : TieredAR ι τ :=
  (w.foldl (mergeStep m g₀) ⟨𝟙_ _, inferInstance⟩).1

instance (w : List S) : Finite (mergeRealize m g₀ w).obj.V :=
  (w.foldl (mergeStep m g₀) ⟨𝟙_ _, inferInstance⟩).2

@[simp] theorem mergeRealize_nil : mergeRealize m g₀ [] = 𝟙_ _ := rfl

theorem mergeRealize_append_singleton (w : List S) (s : S) :
    mergeRealize m g₀ (w ++ [s]) = mergeConcat m (mergeRealize m g₀ w) (g₀ s) := by
  simp only [mergeRealize, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

private theorem nonempty_fullIso_foldl (w : List S) (A : {A : TieredAR ι τ // Finite A.obj.V}) :
    Nonempty (Graph.Iso (w.foldl (mergeStep m g₀) A).1.obj
      (haveI := A.2; mergeConcat m A.1 (mergeRealize m g₀ w)).obj) := by
  induction w generalizing A with
  | nil =>
    have := A.2
    exact ⟨(mergeConcatEmptyFullIso (X := A.1)).symm⟩
  | cons t w ih =>
    have := A.2
    obtain ⟨e₁⟩ := ih (mergeStep m g₀ A t)
    obtain ⟨e₂⟩ := ih (mergeStep m g₀ ⟨𝟙_ _, inferInstance⟩ t)
    exact ⟨e₁.trans (mergeConcatAssocFullIso.trans (mergeConcatCongr (Graph.Iso.refl _)
      (e₂.trans (mergeConcatCongr emptyMergeConcatFullIso (Graph.Iso.refl _))).symm))⟩

/-- Over primitives obeying the NCC, every realization obeys it ([jardine-heinz-2015]
Theorem 4). -/
theorem noCrossing_mergeRealize (hg : ∀ s, NoCrossing (g₀ s).obj.edges (g₀ s).obj.arcs)
    (w : List S) : NoCrossing (mergeRealize m g₀ w).obj.edges (mergeRealize m g₀ w).obj.arcs := by
  suffices ∀ (w : List S) (A : {A : TieredAR ι τ // Finite A.obj.V}),
      NoCrossing A.1.obj.edges A.1.obj.arcs →
        NoCrossing (w.foldl (mergeStep m g₀) A).1.obj.edges
          (w.foldl (mergeStep m g₀) A).1.obj.arcs from this w _ fun v ↦ v.elim
  intro w
  induction w with
  | nil => exact fun _ h ↦ h
  | cons t w ih => exact fun A h ↦ ih _ (haveI := A.2; noCrossing_mergeConcat h (hg t))

/-- Over OCP-clean primitives, every realization is OCP-clean ([jardine-heinz-2015]
Theorem 5). -/
theorem isCleanAt_mergeRealize (hg : ∀ s, (g₀ s).IsCleanAt m) (w : List S) :
    (mergeRealize m g₀ w).IsCleanAt m := by
  suffices ∀ (w : List S) (A : {A : TieredAR ι τ // Finite A.obj.V}),
      (haveI := A.2; A.1.IsCleanAt m) →
        (haveI := (w.foldl (mergeStep m g₀) A).2; (w.foldl (mergeStep m g₀) A).1.IsCleanAt m)
    from this w _ (by simp [IsCleanAt])
  intro w
  induction w with
  | nil => exact fun _ h ↦ h
  | cons t w ih => exact fun A h ↦ ih _ (haveI := A.2; isCleanAt_mergeConcat h (hg t))

/-- Over OCP-clean primitives, the realization by merging concatenation is the collapsed
realization. -/
theorem nonempty_fullIso_realizeMerged (hg : ∀ s, (g₀ s).IsCleanAt m) (w : List S) :
    Nonempty (Graph.Iso (mergeRealize m g₀ w).obj (realizeMerged m g₀ w).obj) := by
  induction w with
  | nil => exact ⟨(IsCleanAt.collapseFullIso (X := 𝟙_ _) (by simp [IsCleanAt])).symm⟩
  | cons s w ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨e₀⟩ := nonempty_fullIso_foldl m g₀ w (mergeStep m g₀ ⟨𝟙_ _, inferInstance⟩ s)
    exact ⟨e₀.trans ((mergeConcatCongr emptyMergeConcatFullIso e).trans
      ((mergeConcatCongr (hg s).collapseFullIso.symm (Graph.Iso.refl _)).trans
        collapseTensorFullIso.symm))⟩

theorem tierWord_mergeRealize (hg : ∀ s, (g₀ s).IsCleanAt m) (w : List S) (i : ι) :
    (mergeRealize m g₀ w).tierWord i = (realizeMerged m g₀ w).tierWord i :=
  (nonempty_fullIso_realizeMerged m g₀ hg w).elim fun e ↦ tierWord_eq_of_iso e i

theorem link_mergeRealize (hg : ∀ s, (g₀ s).IsCleanAt m) (w : List S) (i j : ι) (p q : ℕ) :
    (mergeRealize m g₀ w).link i j p q ↔ (realizeMerged m g₀ w).link i j p q :=
  (nonempty_fullIso_realizeMerged m g₀ hg w).elim fun e ↦ link_iff_of_iso e i j p q

end Realize

end AR

end Autosegmental
