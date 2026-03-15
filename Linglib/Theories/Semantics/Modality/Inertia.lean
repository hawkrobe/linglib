import Linglib.Theories.Semantics.Modality.Kratzer.Flavor

/-!
# Inertial Modality @cite{dowty-1979}
@cite{fusco-sgrizzi-2025} @cite{kratzer-2012} @cite{portner-1998}

The inertial ordering source ranks accessible worlds by how well they match
the "normal continuation" of the current state of affairs.

## Kratzer Parameters

- **Modal base**: circumstantial (facts holding at the evaluation world)
- **Ordering source**: inertial (normal continuation without interruption)

## Linguistic Application

Inertial modality underpins:
- **Progressive aspect**: "John was crossing the street" → in inertia worlds,
  John finishes crossing
- **Intention readings**: *convincere a partire* → in inertia worlds of
  the experiencer's rational attitude, the leaving comes about

-/

namespace Semantics.Modality.Inertia

open Semantics.Modality.Kratzer
open Semantics.Attitudes.Intensional

/-- Inertial modal parameters: circumstantial base + inertial ordering.

    @cite{dowty-1979}: w' is an inertia world of w iff w' matches w up to
    the reference time and the course of events in w continues without
    interruption in w'.

    In Kratzer's framework, this is a circumstantial modal base paired
    with an ordering source whose propositions describe what holds when
    the current course of events continues normally. -/
structure InertialParams where
  /-- Circumstantial modal base: facts holding at the evaluation world -/
  circumstances : ModalBase
  /-- Inertial ordering: propositions describing normal continuation -/
  inertia : OrderingSource

/-- Extract Kratzer parameters from inertial parameters. -/
def InertialParams.toKratzer (p : InertialParams) : KratzerParams where
  base := p.circumstances
  ordering := p.inertia

/-- Inertial necessity: p holds in all best (most inertial) circumstantially
    accessible worlds.

    For intention readings: in all worlds where the experiencer's current
    course of action continues uninterrupted, the intended event obtains. -/
def inertialNecessity (p : InertialParams) (prop : BProp World) (w : World) : Bool :=
  necessity p.circumstances p.inertia prop w

/-- Inertial possibility: p holds in some best (most inertial) circumstantially
    accessible world. -/
def inertialPossibility (p : InertialParams) (prop : BProp World) (w : World) : Bool :=
  possibility p.circumstances p.inertia prop w

/-- Inertial modality is a normal modal logic (inherits from Kratzer). -/
theorem inertial_isNormal (p : InertialParams) :
    (KratzerTheory p.toKratzer).isNormal :=
  kratzer_isNormal p.toKratzer

/-- With empty inertial ordering, inertial modality reduces to simple
    circumstantial necessity (no preference among accessible worlds). -/
theorem empty_inertia_is_simple (circ : ModalBase) (prop : BProp World) (w : World) :
    inertialNecessity ⟨circ, emptyBackground⟩ prop w =
    simpleNecessity circ prop w := by
  simp only [inertialNecessity, necessity, simpleNecessity]
  congr 1
  exact empty_ordering_simple circ w

/-- Inertial modality maps to the circumstantial flavor tag.
    Both inertial and teleological modality concern what happens given
    the facts — they differ only in ordering source, not modal base. -/
def InertialParams.flavorTag : Core.Modality.ModalFlavor := .circumstantial

end Semantics.Modality.Inertia
