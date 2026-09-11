import Linglib.Semantics.Modality.Kratzer.Operators
import Linglib.Semantics.Presupposition.Basic

/-!
# Izvorski (1997): The Present Perfect as an Epistemic Modal

This file formalizes [izvorski-1997], the analysis of the perfect of evidentiality, the
indirect evidential that present perfect morphology expresses in Bulgarian, Turkish, Norwegian
and other languages, (1). The evidential is an epistemic modal, (8): it asserts that the
proposition holds in every accessible world closest to the speaker's beliefs about the evidence,
in the possible-worlds semantics of [kratzer-1991] with a modal base of indirect evidence and
an ordering source of beliefs about it, (17) to (19), and it presupposes that the speaker has
indirect evidence for the proposition, evidence that exists and does not establish it (`Ev`).
Epistemic *must* has the same force and no such presupposition (`must`), which is why an
avowal of having no evidence, (12) and (13), or of having witnessed the event, (14), is
consistent with *must* and not with the evidential; the presupposition projects through
negation, (15), so that a denial targets the proposition, (16). The variability between the
report and inference readings comes from the ordering source (`necessity_of_beliefs`), and the
evidential does not entail its prejacent, as *must* does not, (9). Section 5 derives the
presupposition from the present perfect: the consequent state of the event is known at speech
time, giving the evidence, and the event itself is not, giving its indirectness
(`presup_of_perfect`), and the domain of quantification lies within the epistemically accessible
worlds, so that unlike the counterfactual inference of the past the evidential meaning is no
implicature (`bestWorlds_subset_accessible`).

## Implementation notes

* The presupposition "speaker has indirect evidence for `p`" is rendered as a nonempty
  evidence background whose worlds do not all verify `p`; the report and inference readings
  are not distinguished in the operator, as the paper intends.
* Section 4's temporal and aspectual diagnostics, (20) to (24), are recorded as rows; the
  evidential takes the temporal interpretation of the indicative, which the operator does not
  represent.

## References

* [izvorski-1997]
* [kratzer-1991]
-/

namespace Izvorski1997

open Modality.Kratzer Presupposition

variable {W : Type*}

/-- The speaker knows `p` relative to the background `f`: `p` holds throughout the worlds
compatible with it. -/
def Known (f : ModalBase W) (w : W) (p : W → Prop) : Prop := ∀ u ∈ accessibleWorlds f w, p u

/-- (8) and (17) to (19): the indirect evidential. `f` assigns each world the propositions the
speaker counts as indirect evidence and `g` the speaker's beliefs about that evidence; the
presupposition is that there is such evidence and that it does not establish `p`, the assertion
that `p` holds in every accessible world closest to the beliefs. -/
def Ev (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) : PartialProp W where
  presup w := f w ≠ [] ∧ ¬ Known f w p
  assertion w := necessity f g p w

/-- Epistemic *must*: the same necessity over what is known, with no presupposition about the
kind of evidence. -/
def must (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) : PartialProp W where
  presup _ := True
  assertion w := necessity f g p w

variable {f f' : ModalBase W} {g : OrderingSource W} {p : W → Prop} {w : W}

/-- (8a): the evidential and *must* assert the same universal claim. -/
theorem ev_assertion_eq_must : (Ev f g p).assertion = (must f g p).assertion := rfl

/-- *must* quantifies over what is known, a background at least as rich as the indirect
evidence, so its accessible worlds are among the evidential's, (10) and (11). -/
theorem accessible_must_subset (h : f w ⊆ f' w) : accessibleWorlds f' w ⊆ accessibleWorlds f w :=
  accessibleWorlds_anti h

/-- (12) and (13): with no evidence the evidential is undefined where *must* is not. -/
theorem not_presup_of_no_evidence (h : f w = []) : ¬ (Ev f g p).presup w :=
  λ hp => hp.1 h

/-- (14): evidence establishing `p`, as witnessing it does, is not indirect. -/
theorem not_presup_of_known (h : Known f w p) : ¬ (Ev f g p).presup w :=
  λ hp => hp.2 h

/-- (15) and (16): the presupposition projects through negation, so negating or denying an
evidential statement targets the proposition and not the evidence. -/
theorem neg_presup : (PartialProp.neg (Ev f g p)).presup = (Ev f g p).presup :=
  PartialProp.neg_presup _

/-- The force of the evidential is set by the beliefs about the evidence: when some accessible
world verifies every belief and all such worlds verify `p`, the assertion holds. A reliable
report or a sound inference makes the reading close to universal, an unreliable source leaves
it weak. -/
theorem necessity_of_beliefs (hex : ∃ u ∈ accessibleWorlds f w, ∀ q ∈ g w, q u)
    (h : ∀ u ∈ accessibleWorlds f w, (∀ q ∈ g w, q u) → p u) : necessity f g p w := by
  rw [necessity_iff_all]
  intro u hu
  rw [bestWorlds, kratzerNormality, Core.Order.Normality.fromProps,
    Core.Order.Normality.optimal_ofCriteria_eq hex] at hu
  exact h u hu.1 hu.2

/-- Section 5.3: the domain of quantification lies within the epistemically accessible worlds,
where the counterfactual's lies outside them; the evidential meaning is therefore asserted of
the actual epistemic state and is no implicature. -/
theorem bestWorlds_subset_accessible : bestWorlds f g w ⊆ accessibleWorlds f w :=
  Core.Order.Normality.optimal_subset _ _

/-- Section 5.2: the present perfect supplies the presupposition. The consequent state of the
event holding at speech time is a proposition the speaker knows, the indirect evidence; the
event not holding at speech time is `p` not being known. -/
theorem presup_of_perfect {p' : W → Prop} (hp' : p' ∈ f w) (hnot : ¬ Known f w p) :
    (Ev f g p).presup w :=
  ⟨List.ne_nil_of_mem hp', hnot⟩

/-- (9): like *must*, the evidential does not entail its prejacent. A two-world model: the
evidence excludes nothing, the speaker's beliefs single out the world where `p` holds, and the
evidential is defined and true at the other world. -/
theorem ev_not_entails :
    ∃ (f : ModalBase (Fin 2)) (g : OrderingSource (Fin 2)) (p : Fin 2 → Prop) (w : Fin 2),
      (Ev f g p).presup w ∧ (Ev f g p).assertion w ∧ ¬ p w := by
  refine ⟨λ _ => [λ _ => True], λ _ => [λ u => u = 1], (· = 1), 0, ⟨by simp, ?_⟩, ?_, by decide⟩
  · intro h
    exact absurd (h 0 (λ q hq => by simp at hq; exact hq ▸ trivial)) (by decide)
  · refine necessity_of_beliefs ⟨1, λ q hq => by simp at hq; exact hq ▸ trivial, ?_⟩ ?_
    · simp
    · intro u _ hu
      exact hu _ (List.mem_singleton_self _)

end Izvorski1997
