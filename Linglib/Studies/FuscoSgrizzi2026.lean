import Linglib.Semantics.Modality.Kratzer.Flavor

/-!
# Inertial modality for Italian non-finite belief/action readings
@cite{fusco-sgrizzi-2026} @cite{dowty-1979} @cite{kratzer-2012}

@cite{fusco-sgrizzi-2026} analyse the belief/action ambiguity of Italian
non-finite complements (*convincere a* + INF, *promettere di* + INF) via
inertial modality in the @cite{dowty-1979} sense, recast as a Kratzer
circumstantial-base + inertial-ordering pair.

## Main declarations

* `InertialParams`: bundles a circumstantial modal base with an inertial
  ordering source.
* `inertialNecessity`, `inertialPossibility`: `□`/`◇` over the
  best-inertial-continuation worlds.
* `inertial_duality`: modal duality, delegated to `Kratzer.duality`.
* `empty_inertia_is_simple`: with an empty ordering source, inertial
  necessity collapses to circumstantial `simpleNecessity`.

## Implementation notes

@cite{dowty-1979}: w' is an inertia world of w iff w' matches w up to the
reference time and the course of events in w continues without interruption.
In Kratzer's framework this is a circumstantial modal base paired with an
ordering source whose propositions describe normal continuation.
-/

namespace FuscoSgrizzi2026

open Semantics.Modality Semantics.Modality.Kratzer

variable {W : Type*}

/-- Inertial modal parameters: circumstantial base + inertial ordering. -/
structure InertialParams (W : Type*) where
  /-- Circumstantial modal base: facts holding at the evaluation world. -/
  circumstances : ModalBase W
  /-- Inertial ordering: propositions describing normal continuation. -/
  inertia : OrderingSource W

/-- Extract Kratzer parameters from inertial parameters. -/
def InertialParams.toKratzer (p : InertialParams W) : KratzerParams W where
  base := p.circumstances
  ordering := p.inertia

/-- Inertial necessity: `p` holds in all best (most inertial) circumstantially
    accessible worlds. For intention readings: in all worlds where the
    experiencer's current course of action continues uninterrupted, the
    intended event obtains. -/
def inertialNecessity (p : InertialParams W) (prop : W → Prop) (w : W) : Prop :=
  necessity p.circumstances p.inertia prop w

/-- Inertial possibility: `p` holds in some best circumstantially accessible
    world. -/
def inertialPossibility (p : InertialParams W) (prop : W → Prop) (w : W) : Prop :=
  possibility p.circumstances p.inertia prop w

/-- Inertial modality satisfies modal duality: `□p ↔ ¬◇¬p`. -/
theorem inertial_duality (p : InertialParams W) (prop : W → Prop) (w : W) :
    inertialNecessity p prop w ↔ ¬ inertialPossibility p (fun w' => ¬ prop w') w :=
  Kratzer.duality p.circumstances p.inertia prop w

/-- With empty inertial ordering, inertial modality reduces to simple
    circumstantial necessity (no preference among accessible worlds). -/
theorem empty_inertia_is_simple (circ : ModalBase W) (prop : W → Prop) (w : W) :
    inertialNecessity ⟨circ, emptyBackground⟩ prop w ↔
    simpleNecessity circ prop w := by
  simp only [inertialNecessity, necessity, simpleNecessity,
             Core.Logic.Intensional.boxR]
  constructor
  · intro h j hj
    exact h j ((kratzerBestR_empty circ w j).mpr hj)
  · intro h j hj
    exact h j ((kratzerBestR_empty circ w j).mp hj)

/-- Inertial modality maps to the circumstantial flavor tag. Both inertial
    and teleological modality concern what happens given the facts — they
    differ only in ordering source, not modal base. -/
def InertialParams.flavorTag : ModalFlavor := .circumstantial

end FuscoSgrizzi2026
