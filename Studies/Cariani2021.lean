/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.CarianiSantorio2018
public import Linglib.Logic.Modal.Basic

/-!
# Cariani (2021): *The Modal Future*, chapters 5 and 6

Cariani develops the selection semantics of Cariani and Santorio, on which *will* selects a
world from its modal domain, from the perspective of the world of evaluation, and evaluates its
prejacent there. A modal of this kind is necessity along the graph of a function, so it commutes
with negation and validates excluded middle, while the hybrid semantics of chapter 5, which adds
existential quantification over later times, keeps excluded middle and loses non-contradiction.
Chapter 6 replaces the fixed domain with a modal base, the historical partition, which repairs
*will* under epistemic possibility and makes *will* the identity on contents over a realistic
base. *Will B* and historical *might not B* are then consistent at a world but accepted together
by no information state that respects the partition.

## Main results

* `forall_hybrid_or_not_iff`, `forall_not_hybrid_and_not_iff`: the hybrid semantics validates
  excluded middle where a later time exists and non-contradiction only where at most one does.
* `hybrid_tacos`: the tacos model, where *I will have tacos* and *I will not have tacos* are
  both true.
* `not_diamond_will_fixed`, `diamond_will_historical`: the Oedipus bug of Figure 6.1 and its
  repair by the modal base of Figure 6.4.
* `not_accepts_will_and_might_not`: Fact 6.4, no eligible state accepts a historical
  future-might contradiction, which `fmc_point_consistent` shows consistent at a world.
* `not_will_and_might_not_will`, `not_not_will_and_might_will`, `fork_not_will_and_might_will`:
  Kissine's inconsistencies over transitive and Euclidean bases, and the fork model.

## Implementation notes

* A modal base is an accessibility relation, and *will* along it is
  `SelectionFunction.modal`, whose generalized transparency, Fact 6.1, is
  `SelectionFunction.modal_eq_id`. The fixed domain `H` of chapter 5 is the constant relation to
  `H`, which is Cariani and Santorio's `will`.
* An information state is a set of worlds, accepting the propositions that include it.

## References

* [cariani-2021]
* [cariani-santorio-2018]
* [kissine-2008]
-/

@[expose] public section

namespace Cariani2021

open Conditional ModalLogic SelectionFunction
open scoped SetRel

/-! ### The hybrid semantics

The hybrid semantics of §5.2 (p. 80) evaluates the prejacent of *will* at the selected world at
some later time. It is possibility along an index relation that is serial wherever a later time
exists and functional only where at most one does, so it validates excluded middle and loses
non-contradiction and Negation Swap (p. 83), the failure of scopelessness for which chapter 7
rejects it (p. 117). -/

section Hybrid

variable {W T : Type*} [LT T] (s : SelectionFunction W) (H : Set W)

/-- The index relation of the hybrid semantics relates `(w, t)` to the world selected from `H`
at each later time. -/
def hybridRel : SetRel (W × T) (W × T) := {p | p.2.1 = s.sel p.1.1 H ∧ p.1.2 < p.2.2}

/-- Hybrid *will*, possibility along `hybridRel`, holds of `A` at `(w, t)` when `A` holds at the
world selected from `H` at some later time. -/
def hybrid (A : W × T → Prop) : W × T → Prop := ◇[hybridRel s H] A

variable {s H}

theorem exists_hybridRel_iff {i : W × T} : (∃ j, i ~[hybridRel s H] j) ↔ ∃ u, i.2 < u :=
  ⟨fun ⟨j, _, hj⟩ ↦ ⟨j.2, hj⟩, fun ⟨u, hu⟩ ↦ ⟨(s.sel i.1 H, u), rfl, hu⟩⟩

/-- The hybrid semantics validates excluded middle at an index exactly when a later time
exists. -/
theorem forall_hybrid_or_not_iff {i : W × T} :
    (∀ A : W × T → Prop, hybrid s H A i ∨ hybrid s H (fun j ↦ ¬ A j) i) ↔ ∃ u, i.2 < u :=
  diamond_or_diamond_not_at_iff.trans exists_hybridRel_iff

/-- The hybrid semantics validates non-contradiction at an index exactly when at most one later
time exists. -/
theorem forall_not_hybrid_and_not_iff {i : W × T} :
    (∀ A : W × T → Prop, ¬ (hybrid s H A i ∧ hybrid s H (fun j ↦ ¬ A j) i)) ↔
      ∀ ⦃u⦄, i.2 < u → ∀ ⦃u'⦄, i.2 < u' → u = u' := by
  refine (not_diamond_and_diamond_not_at_iff (R := hybridRel s H) (w := i)).trans
    ⟨fun h u hu u' hu' ↦ congrArg Prod.snd
      (h (v := (s.sel i.1 H, u)) ⟨rfl, hu⟩ (u := (s.sel i.1 H, u')) ⟨rfl, hu'⟩),
      fun h _ ⟨hw, hu⟩ _ ⟨hw', hu'⟩ ↦ Prod.ext (hw.trans hw'.symm) (h hu hu')⟩

/-- In the tacos model of p. 83, with Monday `0`, tacos on Tuesday `1` and pasta on Wednesday
`2`, on Monday *I will have tacos* and *I will not have tacos* are both true. -/
theorem hybrid_tacos (s : SelectionFunction Unit) :
    hybrid s .univ (fun j : Unit × ℕ ↦ j.2 = 1) ((), 0) ∧
      hybrid s .univ (fun j : Unit × ℕ ↦ ¬ j.2 = 1) ((), 0) :=
  ⟨⟨((), 1), ⟨rfl, Nat.one_pos⟩, rfl⟩, ⟨((), 2), ⟨rfl, Nat.two_pos⟩, by decide⟩⟩

end Hybrid

/-! ### The Oedipus model

In Figure 6.1 (p. 94) the historical possibilities of the context, `w0` to `w3`, agree that
Oedipus marries Jocasta, and the epistemic state also admits `w4`, in which he marries Kate.
Over the fixed domain of the historical possibilities, *it is possible that Oedipus will avoid
incest* is false whatever the selection function, since every selection from the domain marries
Jocasta (p. 95). Over the modal base of Figure 6.4 (p. 105), which gives `w4` its own cell, it is
true. -/

section Oedipus

/-- The five worlds of Figure 6.1. -/
inductive World where
  | w0 | w1 | w2 | w3 | w4
  deriving DecidableEq, Repr, Fintype

/-- The proposition that Oedipus avoids incest, marrying Kate. -/
def avoidIncest : Set World := {.w4}

/-- The historical possibilities of the context, in which Oedipus marries Jocasta. -/
def historicalPossibilities : Set World := {.w0, .w1, .w2, .w3}

/-- The epistemic modal base admits every world. -/
def epistemic : SetRel World World := .univ

/-- The historical modal base of Figure 6.4 partitions the worlds into the historical
possibilities of the context and `w4`. -/
def historical : SetRel World World := {p | p.1 = .w4 ↔ p.2 = .w4}

instance : historical.IsRefl := ⟨fun _ ↦ Iff.rfl⟩

/-- Over the fixed domain of the historical possibilities, *it is possible that Oedipus will
avoid incest* is false at the actual world, whatever the selection function (p. 95). -/
theorem not_diamond_will_fixed (s : SelectionFunction World) :
    ¬ ◇[epistemic] (· ∈ CarianiSantorio2018.will s historicalPossibilities avoidIncest) .w0 := by
  rintro ⟨v, -, hv⟩
  have := s.inclusion v historicalPossibilities ⟨.w0, by simp [historicalPossibilities]⟩
  simp only [CarianiSantorio2018.mem_will, avoidIncest, Set.mem_singleton_iff] at hv
  rw [hv] at this
  simp [historicalPossibilities] at this

/-- Over the historical modal base, *it is possible that Oedipus will avoid incest* is true at
the actual world, `w4` witnessing it (p. 106). -/
theorem diamond_will_historical (s : SelectionFunction World) :
    ◇[epistemic] (· ∈ s.modal historical avoidIncest) .w0 :=
  ⟨.w4, trivial, by rw [modal_eq_id]; rfl⟩

end Oedipus

/-! ### Future-might contradictions

An information state is historically eligible when it cuts through no cell of the historical
partition (p. 109). Over a realistic base, *will B* and historical *might not B*, (20) of p. 107,
are consistent at a world but accepted together by no nonempty eligible state, which classifies
them as coordinated-informationally inconsistent, Fact 6.4 (p. 110, proof p. 114). -/

section FMC

variable {W : Type*} (s : SelectionFunction W) (R : SetRel W W)

/-- An information state is historically eligible for a modal base when it holds every world the
base relates to its own. -/
def IsEligible (S : Set W) : Prop := ∀ w ∈ S, ∀ v, w ~[R] v → v ∈ S

variable {s R}

/-- No nonempty eligible state accepts both *will B* and historical *might not B*, Fact 6.4. -/
theorem not_accepts_will_and_might_not [R.IsRefl] {S B : Set W} (hS : IsEligible R S)
    (hne : S.Nonempty) : ¬ (S ⊆ s.modal R B ∧ S ⊆ R.preimage Bᶜ) := by
  rintro ⟨hwill, hmight⟩
  obtain ⟨z, hz⟩ := hne
  obtain ⟨v, hv, hzv⟩ := hmight hz
  have := hwill (hS z hz v hzv)
  rw [modal_eq_id] at this
  exact hv this

end FMC

/-- Historical future-might contradictions are consistent at a world. In the Sports Fan model of
[cariani-santorio-2018], at the Warriors-cap world *Cynthia will wear a Warriors cap* and *she
might not* are both true over today's historical alternatives. -/
theorem fmc_point_consistent (s : SelectionFunction CarianiSantorio2018.W) :
    CarianiSantorio2018.W.cw ∈
      s.modal (CarianiSantorio2018.frame.alt 0) CarianiSantorio2018.warriorsCap ∩
        (CarianiSantorio2018.frame.alt 0).preimage CarianiSantorio2018.warriorsCapᶜ := by
  refine ⟨by rw [modal_eq_id]; rfl, .cg, by simp [CarianiSantorio2018.warriorsCap], ?_⟩
  change CarianiSantorio2018.W.cg ∈ CarianiSantorio2018.frame.alternatives (.cw, 0)
  simp

/-! ### Kissine's argument

Kissine argues against a modal *will* from the inconsistency of *will A and might not will A* and
of *not will A and might will A*, (12) and (15), which holds for a quantificational *will* over a
transitive and over a Euclidean base respectively; over a serial base with both properties
*might will A* collapses to *will A* (`ModalLogic.diamond_box_iff`). The fork model of
footnote 3 (p. 100) is transitive but not Euclidean, and satisfies (15). Selection escapes the
argument, which assumes universal force (p. 101). -/

section Kissine

variable {W : Type*} {R : SetRel W W} {p : W → Prop} {w : W}

/-- Over a transitive base *will A and might not will A* is inconsistent for a quantificational
*will*. -/
theorem not_will_and_might_not_will [R.IsTrans] :
    ¬ (□[R] p w ∧ ◇[R] (fun v ↦ ¬ □[R] p v) w) :=
  fun ⟨h, _, hv, hn⟩ ↦ hn (box_four h _ hv)

/-- Over a Euclidean base *not will A and might will A* is inconsistent for a quantificational
*will*. -/
theorem not_not_will_and_might_will [IsEuclidean R] :
    ¬ (¬ □[R] p w ∧ ◇[R] (□[R] p) w) :=
  fun ⟨h, h'⟩ ↦ h (box_of_diamond_box h')

/-- The fork model relates `0` to `1` and `2` and each of these to itself. -/
def fork : SetRel (Fin 3) (Fin 3) := {p | p.1 = 0 ∧ p.2 ≠ 0 ∨ p.1 ≠ 0 ∧ p.2 = p.1}

instance : DecidablePred (· ∈ fork) := fun p ↦
  inferInstanceAs (Decidable (p.1 = 0 ∧ p.2 ≠ 0 ∨ p.1 ≠ 0 ∧ p.2 = p.1))

instance : fork.IsTrans := ⟨by decide⟩

theorem not_isEuclidean_fork : ¬ IsEuclidean fork :=
  fun h ↦ absurd (h.eucl 0 1 2 (by decide) (by decide)) (by decide)

/-- In the fork model, with `A` true at `1` and false at `2`, *not will A and might will A* is
true at `0`. -/
theorem fork_not_will_and_might_will :
    ¬ □[fork] (· = 1) 0 ∧ ◇[fork] (□[fork] (· = 1)) 0 :=
  ⟨fun h ↦ absurd (h 2 (by decide)) (by decide),
    ⟨1, by decide, by decide⟩⟩

end Kissine

end Cariani2021
