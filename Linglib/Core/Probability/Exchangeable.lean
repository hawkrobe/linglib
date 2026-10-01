/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Exchangeable laws

A family of random variables indexed by `ι` with values in `α` is *exchangeable* when its law, a
measure on `ι → α`, is unchanged by permuting finitely many of the indices. `Exchangeable μ`
asks this of every transposition; the transpositions generate the permutations that move
finitely many indices, and for finite `ι` all of them (`exchangeable_iff_forall_perm`). This is
the invariance under the symmetric group that [pitman-2006] §2.1 takes as the definition of an
exchangeable random partition.

## Main definitions

* `ProbabilityTheory.Exchangeable μ`: swapping two coordinates leaves `μ` unchanged.

## Main results

* `ProbabilityTheory.Exchangeable.map_comp_perm`, `ProbabilityTheory.exchangeable_iff_forall_perm`:
  for finite `ι`, invariance under every permutation.
* `ProbabilityTheory.exchangeable_of_measure_singleton`: on a countable space with measurable
  singletons it suffices that swapping two coordinates of a point preserves its mass.
* `ProbabilityTheory.Exchangeable.map_comp`: applying a measurable map to every coordinate
  preserves exchangeability.
* `ProbabilityTheory.exchangeable_pi`: independent identically distributed families are
  exchangeable.

[UPSTREAM] candidate: mathlib has no notion of exchangeability.

## References

* [pitman-2006]
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {ι α β : Type*} [DecidableEq ι] [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure (ι → α)}

omit [DecidableEq ι] in
theorem measurable_comp_perm (σ : Equiv.Perm ι) : Measurable fun x : ι → α ↦ x ∘ σ :=
  .of_eval fun i ↦ measurable_pi_apply (σ i)

/-- The law `μ` of an `ι`-indexed family is *exchangeable* when swapping two coordinates leaves
it unchanged. -/
def Exchangeable (μ : Measure (ι → α)) : Prop :=
  ∀ i j : ι, μ.map (· ∘ Equiv.swap i j) = μ

theorem Exchangeable.map_comp_perm [Finite ι] (hμ : Exchangeable μ) (σ : Equiv.Perm ι) :
    μ.map (· ∘ σ) = μ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul σ i j _ ih =>
    rw [show (· ∘ ⇑(Equiv.swap i j * σ)) = (fun x : ι → α ↦ x ∘ σ) ∘ (· ∘ Equiv.swap i j) from
      rfl, ← Measure.map_map (measurable_comp_perm σ) (measurable_comp_perm _), hμ i j, ih]

theorem exchangeable_iff_forall_perm [Finite ι] :
    Exchangeable μ ↔ ∀ σ : Equiv.Perm ι, μ.map (· ∘ σ) = μ :=
  ⟨Exchangeable.map_comp_perm, fun h _ _ ↦ h _⟩

/-- On a countable space with measurable singletons, a law is exchangeable as soon as swapping two
coordinates of a point never changes its mass. -/
theorem exchangeable_of_measure_singleton [Countable (ι → α)] [MeasurableSingletonClass (ι → α)]
    (h : ∀ (x : ι → α) (i j : ι), μ {x ∘ Equiv.swap i j} = μ {x}) : Exchangeable μ :=
  fun i j ↦ Measure.ext_of_singleton fun x ↦ by
    rw [Measure.map_apply (measurable_comp_perm _) (measurableSet_singleton x),
      show (· ∘ Equiv.swap i j) ⁻¹' {x} = {x ∘ Equiv.swap i j} from Set.ext fun y ↦ by
        simpa [Equiv.symm_swap] using (Equiv.eq_comp_symm (Equiv.swap i j) y x).symm,
      h]

/-- Applying a measurable map to every coordinate of an exchangeable family gives an exchangeable
family. -/
theorem Exchangeable.map_comp {f : α → β} (hf : Measurable f) (hμ : Exchangeable μ) :
    Exchangeable (μ.map (f ∘ ·)) := fun i j ↦ by
  have hfc : Measurable fun x : ι → α ↦ f ∘ x := .of_eval fun k ↦ hf.comp (measurable_pi_apply k)
  rw [Measure.map_map (measurable_comp_perm _) hfc,
    show (· ∘ Equiv.swap i j) ∘ (f ∘ ·) = (f ∘ ·) ∘ (fun x : ι → α ↦ x ∘ Equiv.swap i j) from rfl,
    ← Measure.map_map hfc (measurable_comp_perm _), hμ i j]

/-- An independent identically distributed family is exchangeable. -/
theorem exchangeable_pi [Fintype ι] (ν : Measure α) [SigmaFinite ν] :
    Exchangeable (Measure.pi fun _ : ι ↦ ν) := fun i j ↦ by
  have h := (measurePreserving_piCongrLeft (fun _ : ι ↦ ν) (Equiv.swap i j)).map_eq
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι ↦ α) (Equiv.swap i j)) =
      (· ∘ Equiv.swap i j) := by
    funext x k
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rwa [hfun] at h

end ProbabilityTheory
