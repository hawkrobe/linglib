import Linglib.Semantics.Modality.EventRelativity
import Linglib.Data.Examples.Hacquard2010

/-!
# Hacquard (2010): On the Event Relativity of Modal Auxiliaries

This file formalizes [hacquard-2010]'s event-relative semantics for modal auxiliaries. A modal's
modal base is a function of an event rather than a world (29), `must` and `can`, and its event
variable is bound by the closest binder (37), (38): the speech event for a high modal in a matrix
clause, the attitude event for a high modal in a complement, and the VP event for a low modal
(48), which `Semantics/Modality/EventRelativity.lean` records as the binders of
`Modality.ModalPosition`. Speech and attitude events carry propositional content and embed a
proposition under universal quantification over it (41), (44), `attitude`; the epistemic modal
base is the content of the event the modal is anchored to (51), `canEpis` and `mustEpis`, so it
is undefined where a low modal is anchored to a contentless VP event (59),
`not_canEpis_of_content_eq_none`, and defined again when the complement is itself an attitude
(60). Anchored to the event that embeds it, an epistemic modal quantifies over the same worlds as
that event, so the outer layer of quantification is vacuous, (53) to (57),
`attitude_canEpis_iff` and `attitude_mustEpis_iff`, the possibility case once the information
state is consistent; and Yalcin's supposition (58) is incoherent because the modal quantifies
over the supposition's own content, `not_attitude_suppose`. Cinque's puzzle (section 3) is that
[cinque-1999]'s hierarchy fixes the epistemic head above tense and the root head below aspect,
`CinqueHead`, where a single flavor-neutral entry should suffice; the paper derives the same
matrix correlation from the content of the binding event, `epistemic_high_iff`. The paper's
examples are the rows of `Data.Examples.Hacquard2010`.

## Implementation notes

The content of an event is its set of compatible worlds, `⋂CON(e)`, an `Option` undefined for
contentless events; the descriptive part of an attitude or asserting event, `Exp(e, x)` and
`belief'(e, w)` or `Assert'(e₀, w)`, is an abstract predicate. Ordering sources are omitted, as
in the paper's derivations, and the circumstantial modal base (61), whose event dependence the
paper leaves open, is not defined. The individual and time a modal is keyed to (section 4) enter
only through the binding event; the Italian restructuring evidence belongs to [hacquard-2006].

## References

* [hacquard-2010]
* [cinque-1999]
* [yalcin-2007]
-/

namespace Hacquard2010

open Modality

variable {E W : Type*}

/-! ### Event-relative modals, section 5 -/

/-- (29): a necessity modal quantifies over the worlds its event-relative modal base returns. -/
def must (f : E → Set W) (q : W → Prop) (e : E) : Prop := ∀ w' ∈ f e, q w'

/-- (29): a possibility modal over the event-relative modal base. -/
def can (f : E → Set W) (q : W → Prop) (e : E) : Prop := ∃ w' ∈ f e, q w'

/-- (41) and (44): a contentful event, an attitude or the speech event, embeds a proposition
under universal quantification over its content; `holds e w` is the event's descriptive part. -/
def attitude (con : E → Option (Set W)) (holds : E → W → Prop) (e : E) (p : W → Prop)
    (w : W) : Prop :=
  holds e w ∧ ∃ C, con e = some C ∧ ∀ w' ∈ C, p w'

/-- (51): the epistemic modal base is the content of the event the modal is anchored to, so an
epistemic possibility is defined only for a contentful event. -/
def canEpis (con : E → Option (Set W)) (q : W → Prop) (e : E) : Prop :=
  ∃ C, con e = some C ∧ ∃ w' ∈ C, q w'

/-- (51): epistemic necessity over the content of the anchoring event. -/
def mustEpis (con : E → Option (Set W)) (q : W → Prop) (e : E) : Prop :=
  ∃ C, con e = some C ∧ ∀ w' ∈ C, q w'

variable {con : E → Option (Set W)} {holds : E → W → Prop} {e : E} {q : W → Prop} {w : W}
  {C : Set W}

/-! ### Content licensing, section 6.1 -/

/-- (49e) and (59): an event without content licenses no epistemic modal base, so a low modal
anchored to a train-taking cannot report what its subject knew. -/
theorem not_canEpis_of_content_eq_none (h : con e = none) : ¬ canEpis con q e :=
  λ ⟨_, hC, _⟩ => by simp [h] at hC

theorem not_mustEpis_of_content_eq_none (h : con e = none) : ¬ mustEpis con q e :=
  λ ⟨_, hC, _⟩ => by simp [h] at hC

/-- (60): when the complement is itself an attitude, the aspect-bound modal's event has content,
and the modal expresses a possibility given what the subject came to know. -/
theorem canEpis_of_content_eq_some (hC : con e = some C) {w' : W} (hw' : w' ∈ C) (hq : q w') :
    canEpis con q e :=
  ⟨C, hC, w', hw', hq⟩

/-- (53) and (57): a possibility modal anchored to the event that embeds it quantifies over the
same worlds as that event, so the outer universal layer is vacuous whenever the content is
consistent. -/
theorem attitude_canEpis_iff :
    attitude con holds e (λ _ => canEpis con q e) w ↔
      holds e w ∧ ∃ C, con e = some C ∧ (C.Nonempty → ∃ w' ∈ C, q w') := by
  simp only [attitude, canEpis]
  refine and_congr_right λ _ => exists_congr λ C => and_congr_right λ hC => ⟨?_, ?_⟩
  · rintro h ⟨w₀, hw₀⟩
    obtain ⟨C', hC', hex⟩ := h w₀ hw₀
    rw [hC] at hC'
    cases hC'
    exact hex
  · exact λ h w₀ hw₀ => ⟨C, hC, h ⟨w₀, hw₀⟩⟩

/-- (54): with a consistent content, an embedded epistemic possibility says that `q` is
compatible with the content of the embedding event, the speaker's beliefs under `ASSERT` or the
attitude holder's under `believe`. -/
theorem attitude_canEpis_iff_of_nonempty (hC : con e = some C) (hne : C.Nonempty) :
    attitude con holds e (λ _ => canEpis con q e) w ↔ holds e w ∧ ∃ w' ∈ C, q w' := by
  rw [attitude_canEpis_iff]
  refine and_congr_right λ _ => ⟨λ ⟨C', hC', h⟩ => ?_, λ h => ⟨C, hC, λ _ => h⟩⟩
  rw [hC] at hC'
  cases hC'
  exact h hne

/-- (55) and (57): an embedded epistemic necessity is necessity over the embedding event's
content, the outer layer again vacuous. -/
theorem attitude_mustEpis_iff :
    attitude con holds e (λ _ => mustEpis con q e) w ↔ holds e w ∧ mustEpis con q e := by
  simp only [attitude, mustEpis]
  refine and_congr_right λ _ => ⟨?_, ?_⟩
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, λ w'' hw'' => ?_⟩
    obtain ⟨C', hC', hall⟩ := h w'' hw''
    rw [hC] at hC'
    cases hC'
    exact hall w'' hw''
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, λ _ _ => ⟨C, hC, h⟩⟩

/-- (58), [yalcin-2007]'s puzzle: supposing that it is raining and that it might not be raining
is incoherent, since the epistemic quantifies over the supposition's own content and no
consistent content satisfies both. -/
theorem not_attitude_suppose {rain : W → Prop} (hC : con e = some C) (hne : C.Nonempty) :
    ¬ attitude con holds e (λ w' => rain w' ∧ canEpis con (λ w'' => ¬ rain w'') e) w := by
  rintro ⟨-, C', hC', h⟩
  rw [hC] at hC'
  cases hC'
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨-, C'', hC'', w₁, hw₁, hnr⟩ := h w₀ hw₀
  rw [hC] at hC''
  cases hC''
  exact hnr (h w₁ hw₁).1

/-! ### Cinque's puzzle, section 3 -/

/-- [cinque-1999]'s hierarchy at the granularity the paper uses: an epistemic head above tense,
a root head below aspect. -/
inductive CinqueHead
  | modEpistemic
  | tense
  | aspect
  | modRoot
  deriving DecidableEq

namespace CinqueHead

/-- Height in the hierarchy, the topmost head highest. -/
def height : CinqueHead → ℕ
  | .modEpistemic => 3
  | .tense => 2
  | .aspect => 1
  | .modRoot => 0

/-- `h` sits above `h'` in the hierarchy. -/
def Above (h h' : CinqueHead) : Prop := h'.height < h.height

instance : DecidableRel Above := λ h h' => inferInstanceAs (Decidable (h'.height < h.height))

/-- A high head sits above tense. -/
def IsHigh (h : CinqueHead) : Prop := h.Above .tense

instance : DecidablePred IsHigh := λ h => inferInstanceAs (Decidable (h.Above .tense))

/-- The flavor the hierarchy stipulates for each modal head. -/
def flavor : CinqueHead → Option ModalFlavor
  | .modEpistemic => some .epistemic
  | .modRoot => some .circumstantial
  | _ => none

/-- In the hierarchy the correlation of height and flavor is built in: the high modal head is the
epistemic one, and the root head is below aspect. -/
theorem isHigh_iff (h : CinqueHead) : h.IsHigh ↔ h.flavor = some .epistemic := by
  cases h <;> decide

theorem aspect_above_modRoot : CinqueHead.aspect.Above .modRoot := by decide

end CinqueHead

/-- Section 6.3: the same matrix correlation derived from one flavor-neutral entry. A modal
above tense is bound by the speech event, which has content, and a modal below aspect by the VP
event, which has none, so an epistemic modal base is available exactly in the high position. -/
theorem epistemic_high_iff (pos : ModalPosition) :
    pos.defaultBinder.canProjectEpistemic = true ↔ pos = .aboveAsp := by
  cases pos <;> decide

end Hacquard2010
