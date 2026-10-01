/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Action

/-!
# Exchangeable laws

A family of random variables indexed by `ι` with values in `α` is *exchangeable* when its law, a
measure on `ι → α`, is unchanged by permuting the indices. The permutations act on `ι → α` by
precomposition, as the domain action `(Equiv.Perm ι)ᵈᵐᵃ` (`(DomMulAct.mk σ • x) i = x (σ i)`),
and `Exchangeable μ` is invariance under that action, `SMulInvariantMeasure`; random partitions
are exchangeable in the same sense, for the action of the permutations on partitions
([pitman-2006] §2.1).

## Main definitions

* `ProbabilityTheory.Exchangeable μ`: every permutation of the indices leaves `μ` unchanged.

## Main results

* `ProbabilityTheory.exchangeable_iff`: invariance under `x ↦ x ∘ σ` for every permutation `σ`.
* `ProbabilityTheory.exchangeable_of_swap`: for finite `ι`, the transpositions suffice.
* `ProbabilityTheory.exchangeable_of_measure_singleton`: on a countable space with measurable
  singletons it suffices that permuting a point preserves its mass.
* `ProbabilityTheory.Exchangeable.map_comp`: applying a measurable map to every coordinate
  preserves exchangeability.
* `ProbabilityTheory.exchangeable_pi`: independent identically distributed families are
  exchangeable.

## Implementation notes

For infinite `ι` the usual definition asks for invariance only under the permutations that move
finitely many indices; `Exchangeable` asks for all of them, which de Finetti's theorem shows
equivalent on standard Borel spaces but which is not proved here.

[UPSTREAM] candidates: mathlib has no notion of exchangeability, and no measurability instance
for the domain action on functions.

## References

* [pitman-2006]
-/

@[expose] public section

open MeasureTheory

/-- The domain action on functions is measurable. -/
instance DomMulAct.instMeasurableConstSMul {M ι α : Type*} [SMul M ι] [MeasurableSpace α] :
    MeasurableConstSMul Mᵈᵐᵃ (ι → α) where
  measurable_const_smul c := .of_eval fun i ↦ measurable_pi_apply (DomMulAct.mk.symm c • i)

namespace ProbabilityTheory

variable {ι α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure (ι → α)}

theorem measurable_comp_perm (σ : Equiv.Perm ι) : Measurable fun x : ι → α ↦ x ∘ σ :=
  .of_eval fun i ↦ measurable_pi_apply (σ i)

/-- The law `μ` of an `ι`-indexed family is *exchangeable* when every permutation of the indices,
acting by precomposition, leaves it unchanged. -/
abbrev Exchangeable (μ : Measure (ι → α)) : Prop :=
  SMulInvariantMeasure (Equiv.Perm ι)ᵈᵐᵃ (ι → α) μ

theorem exchangeable_iff : Exchangeable μ ↔ ∀ σ : Equiv.Perm ι, μ.map (· ∘ σ) = μ := by
  refine ⟨fun _ σ ↦ MeasureTheory.map_smul (DomMulAct.mk σ) μ, fun h ↦ ⟨fun c s hs ↦ ?_⟩⟩
  rw [← Measure.map_apply (measurable_const_smul c) hs]
  exact congrArg (· s) (h (DomMulAct.mk.symm c))

theorem Exchangeable.map_comp_perm (hμ : Exchangeable μ) (σ : Equiv.Perm ι) :
    μ.map (· ∘ σ) = μ :=
  exchangeable_iff.1 hμ σ

/-- For finitely many indices, invariance under the transpositions suffices, since they generate
the permutations. -/
theorem exchangeable_of_swap [Finite ι] [DecidableEq ι]
    (h : ∀ i j : ι, μ.map (· ∘ Equiv.swap i j) = μ) : Exchangeable μ := by
  refine exchangeable_iff.2 fun σ ↦ ?_
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul σ i j _ ih =>
    rw [show (· ∘ ⇑(Equiv.swap i j * σ)) = (fun x : ι → α ↦ x ∘ σ) ∘ (· ∘ Equiv.swap i j) from
      rfl, ← Measure.map_map (measurable_comp_perm σ) (measurable_comp_perm _), h i j, ih]

/-- On a countable space with measurable singletons, a law is exchangeable as soon as permuting a
point never changes its mass. -/
theorem exchangeable_of_measure_singleton [Countable (ι → α)] [MeasurableSingletonClass (ι → α)]
    (h : ∀ (x : ι → α) (σ : Equiv.Perm ι), μ {x ∘ σ} = μ {x}) : Exchangeable μ :=
  exchangeable_iff.2 fun σ ↦ Measure.ext_of_singleton fun x ↦ by
    rw [Measure.map_apply (measurable_comp_perm σ) (measurableSet_singleton x),
      show (· ∘ σ) ⁻¹' {x} = {x ∘ σ.symm} from Set.ext fun y ↦
        (Equiv.eq_comp_symm σ y x).symm, h]

/-- Applying a measurable map to every coordinate of an exchangeable family gives an exchangeable
family. -/
theorem Exchangeable.map_comp {f : α → β} (hf : Measurable f) (hμ : Exchangeable μ) :
    Exchangeable (μ.map (f ∘ ·)) := exchangeable_iff.2 fun σ ↦ by
  have hfc : Measurable fun x : ι → α ↦ f ∘ x := .of_eval fun k ↦ hf.comp (measurable_pi_apply k)
  rw [Measure.map_map (measurable_comp_perm σ) hfc,
    show (· ∘ σ) ∘ (f ∘ ·) = (f ∘ ·) ∘ (fun x : ι → α ↦ x ∘ σ) from rfl,
    ← Measure.map_map hfc (measurable_comp_perm σ), hμ.map_comp_perm σ]

/-- An independent identically distributed family is exchangeable. -/
theorem exchangeable_pi [Fintype ι] (ν : Measure α) [SigmaFinite ν] :
    Exchangeable (Measure.pi fun _ : ι ↦ ν) := exchangeable_iff.2 fun σ ↦ by
  have h := (measurePreserving_piCongrLeft (fun _ : ι ↦ ν) σ.symm).map_eq
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι ↦ α) σ.symm) = (· ∘ σ) := by
    funext x k
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rwa [hfun] at h

end ProbabilityTheory
