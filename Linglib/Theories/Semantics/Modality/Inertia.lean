import Linglib.Theories.Semantics.Modality.Kratzer.Flavor

/-!
# Inertial Modality @cite{dowty-1979}
@cite{fusco-sgrizzi-2026} @cite{kratzer-2012}

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

variable {W : Type*}

/-- Inertial modal parameters: circumstantial base + inertial ordering.

    @cite{dowty-1979}: w' is an inertia world of w iff w' matches w up to
    the reference time and the course of events in w continues without
    interruption in w'.

    In Kratzer's framework, this is a circumstantial modal base paired
    with an ordering source whose propositions describe what holds when
    the current course of events continues normally. -/
structure InertialParams (W : Type*) where
  /-- Circumstantial modal base: facts holding at the evaluation world -/
  circumstances : ModalBase W
  /-- Inertial ordering: propositions describing normal continuation -/
  inertia : OrderingSource W

/-- Extract Kratzer parameters from inertial parameters. -/
def InertialParams.toKratzer (p : InertialParams W) : KratzerParams W where
  base := p.circumstances
  ordering := p.inertia

/-- Inertial necessity: p holds in all best (most inertial) circumstantially
    accessible worlds.

    For intention readings: in all worlds where the experiencer's current
    course of action continues uninterrupted, the intended event obtains. -/
def inertialNecessity (p : InertialParams W) (prop : W → Prop) (w : W) : Prop :=
  necessity p.circumstances p.inertia prop w

/-- Inertial possibility: p holds in some best (most inertial) circumstantially
    accessible world. -/
def inertialPossibility (p : InertialParams W) (prop : W → Prop) (w : W) : Prop :=
  possibility p.circumstances p.inertia prop w

/-- Inertial modality satisfies modal duality: □p ↔ ¬◇¬p.
    Inherited from `Kratzer.duality` since inertial necessity/possibility
    are `boxR`/`diamondR` over the same Kratzer best-worlds relation.

    See `Kratzer/Operators.lean::duality` docstring for the broader context:
    one of five modality-flavor `theorem duality`s that would unify under a
    `Core.Logic.Opposition.Square.fromBox` instance once the Prop↔Bool
    coercion lands. -/
theorem inertial_duality (p : InertialParams W) (prop : W → Prop) (w : W) :
    inertialNecessity p prop w ↔ ¬ inertialPossibility p (fun w' => ¬ prop w') w :=
  Kratzer.duality p.circumstances p.inertia prop w

/-- With empty inertial ordering, inertial modality reduces to simple
    circumstantial necessity (no preference among accessible worlds). -/
theorem empty_inertia_is_simple (circ : ModalBase W) (prop : W → Prop) (w : W) :
    inertialNecessity ⟨circ, emptyBackground⟩ prop w ↔
    simpleNecessity circ prop w := by
  simp only [inertialNecessity, necessity, simpleNecessity,
             Core.IntensionalLogic.boxR]
  constructor
  · intro h j hj
    exact h j ((kratzerBestR_empty circ w j).mpr hj)
  · intro h j hj
    exact h j ((kratzerBestR_empty circ w j).mp hj)

/-- Inertial modality maps to the circumstantial flavor tag.
    Both inertial and teleological modality concern what happens given
    the facts — they differ only in ordering source, not modal base. -/
def InertialParams.flavorTag : Core.Modality.ModalFlavor := .circumstantial

end Semantics.Modality.Inertia
