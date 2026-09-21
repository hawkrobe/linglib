/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Disintegrating a finite product measure along one coordinate

`MeasureTheory.Measure.pi_setOf_forall_ne_mem` computes the measure, under `Measure.pi μ`, of a set
of the form `{x | ∀ j ≠ i, x j ∈ s j (x i)}` as an integral against `μ i`. `[UPSTREAM]` candidate
for `Mathlib/MeasureTheory/Constructions/Pi.lean`.
-/

public section

open Set Finset
open scoped ENNReal

namespace MeasureTheory.Measure

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]

/-- Disintegration of a finite product measure along coordinate `i`: the measure of a set cut out
by constraints tying each other coordinate to the `i`-th is the integral over the `i`-th coordinate
of the product of the measures of the constraint sets. -/
theorem pi_setOf_forall_ne_mem (i : ι) {s : ∀ j, α i → Set (α j)}
    (hs : ∀ j, MeasurableSet {p : α i × α j | p.2 ∈ s j p.1}) :
    Measure.pi μ {x | ∀ j, j ≠ i → x j ∈ s j (x i)} =
      ∫⁻ a, ∏ j ∈ univ.erase i, μ j (s j a) ∂μ i := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd α (· = i)
  let T : Set ((∀ j : {j // j = i}, α j) × ∀ j : {j // ¬j = i}, α j) :=
    {p | ∀ j : {j // ¬j = i}, p.2 j ∈ s j (p.1 ⟨i, rfl⟩)}
  have hT : MeasurableSet T := by
    have : T = ⋂ j : {j // ¬j = i}, (fun p ↦ (p.1 ⟨i, rfl⟩, p.2 j)) ⁻¹'
        {p : α i × α j | p.2 ∈ s j p.1} := by ext; simp [T]
    rw [this]
    exact .iInter fun j ↦ (hs j).preimage (by fun_prop)
  have hS : {x | ∀ j, j ≠ i → x j ∈ s j (x i)} = e ⁻¹' T := by
    ext x; simp [T, e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
  rw [hS, (measurePreserving_piEquivPiSubtypeProd μ (· = i)).measure_preimage_equiv,
    Measure.prod_apply hT]
  have hslice : ∀ y : ∀ j : {j // j = i}, α j, Prod.mk y ⁻¹' T =
      Set.pi univ fun j : {j // ¬j = i} ↦ s j (y ⟨i, rfl⟩) := by
    intro y; ext; simp [T]
  simp_rw [hslice, Measure.pi_pi]
  have h := (measurePreserving_piUnique fun j : {j // j = i} ↦ μ j).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (fun a : α i ↦ ∏ j ∈ univ.erase i, μ j (s j a))
  convert h using 3 with y
  exact (Finset.prod_subtype (univ.erase i) (by simp) fun j ↦ μ j (s j (y ⟨i, rfl⟩))).symm

end MeasureTheory.Measure
