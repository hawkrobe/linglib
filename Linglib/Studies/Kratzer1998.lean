import Linglib.Semantics.Tense.Decomposition
import Linglib.Semantics.Events.Basic
import Linglib.Fragments.English.Tense
import Linglib.Fragments.German.Tense
import Linglib.Data.Examples.Kratzer1998

/-!
# Kratzer (1998): More Structural Analogies between Pronouns and Tenses

This file formalizes the paper's tense inventory and the consequences it draws from it.
Tenses are pronouns ([partee-1973]): English has two indexical tenses, a present defined
when the context provides an interval including the utterance time and a past defined when
it provides one preceding it, and a zero tense, a variable with no presupposition that must
be bound by the next tense up, just as a zero pronoun must be bound by a local antecedent.
Attitude complements denote properties of times because a zero tense with a binder index
abstracts over the time, which derives Abusch's constraint from the verbs' selection; an
indexical tense in the same position yields a proposition, whatever binder is inserted. The
present under past of *The ultrasound picture indicated that Mary is pregnant* is read de re
about a state through the operator that turns a property of times into a property of
eventualities. Finally, since English *Borromini built this church* is fine out of the blue
while the German Präteritum is not, the English simple past spells out a present tense with
perfect aspect, one of the three aspect operators after [klein-1994] that map properties of
events to properties of times; the German Perfekt has the same decomposition.

## Implementation notes

An out-of-the-blue context is the temporal assignment sending every variable to the
utterance time, so the definedness of a tense pronoun there is its presupposition under the
library's `TensePronoun.fullPresupposition`, and the (40)–(41) verdicts follow from the
Fragments' surface tenses rather than being listed. The aspect operators take a reference
interval; a tense supplies a point, embedded as `NonemptyInterval.pure`. The zero-pronoun
typology of §2–§3 and the locality argument from switch reference are prose.

## References

* [kratzer-1998]
* [partee-1973] — tenses as pronouns
* [abusch-1997], [ogihara-1989], [ogihara-1996] — sequence of tense and temporal de se
* [heim-kratzer-1998] — binder indices
* [klein-1994] — reference time and the aspects
-/

namespace Kratzer1998

open Tense Tense.Decomposition Data.Examples

section Tenses

variable {T : Type*} [LinearOrder T]

/-- An out-of-the-blue context: no salient time but the utterance time, so every temporal
variable resolves to it. -/
def outOfTheBlue (t₀ : T) : TemporalAssignment T := Function.const ℕ t₀

/-- The indexical present is defined out of the blue: the utterance time includes itself. -/
theorem indexicalPresent_outOfTheBlue (t₀ : T) :
    indexicalPresent.fullPresupposition (outOfTheBlue t₀) := by
  simp [TensePronoun.fullPresupposition, TensePronoun.resolve, TensePronoun.evalTime,
    indexicalPresent, outOfTheBlue, present]

/-- A past pronoun is undefined out of the blue: no provided interval precedes the utterance
time. -/
theorem not_anaphoricPast_outOfTheBlue (n : ℕ) (t₀ : T) :
    ¬ (anaphoricPast n).fullPresupposition (outOfTheBlue t₀) := by
  simp [TensePronoun.fullPresupposition, TensePronoun.resolve, TensePronoun.evalTime,
    anaphoricPast, outOfTheBlue, past]

omit [LinearOrder T] in
/-- A zero tense with a binder index makes its clause a property of times (§5, (31)):
whatever the assignment, the abstract applied to `t` evaluates the clause at `t`. -/
theorem boundPresent_abstract (n : ℕ) (P : T → Prop) (g : TemporalAssignment T) (t : T) :
    temporalLambdaAbs n (λ g => P ((boundPresent n).resolve g)) g t ↔ P t := by
  simp [temporalLambdaAbs, TensePronoun.resolve, interpTense, boundPresent]

omit [LinearOrder T] in
/-- An indexical tense cannot be abstracted over: the binder leaves the clause a proposition
about the utterance time, which is why an attitude verb forces a zero tense. -/
theorem indexicalPresent_not_abstracted {n : ℕ} (hn : n ≠ 0) (P : T → Prop)
    (g : TemporalAssignment T) (t : T) :
    temporalLambdaAbs n (λ g => P (indexicalPresent.resolve g)) g t ↔ P (g 0) := by
  simp [temporalLambdaAbs, TensePronoun.resolve, interpTense, indexicalPresent,
    Function.update_of_ne hn.symm]

end Tenses

section Aspect

variable {T W : Type*} [LinearOrder T]

/-- The operator of (38): a property of times becomes a property of eventualities holding
of `e` at every world iff the property holds of the running time of `e`. -/
def star (P : NonemptyInterval T → W → Prop) (e : Event T) (_ : W) : Prop :=
  ∀ w', P e.τ w'

/-- The temporal de re is semantically forced: `star P` does not depend on the evaluation
world. -/
theorem star_congr (P : NonemptyInterval T → W → Prop) (e : Event T) (w w' : W) :
    star P e w ↔ star P e w' := Iff.rfl

/-- Imperfective aspect (§7): the reference time is included in the event time. -/
def imperfective (P : Event T → W → Prop) (r : NonemptyInterval T) (w : W) : Prop :=
  ∃ e, r ≤ e.τ ∧ P e w

/-- Perfective aspect: the event time is included in the reference time. -/
def perfective (P : Event T → W → Prop) (r : NonemptyInterval T) (w : W) : Prop :=
  ∃ e, e.τ ≤ r ∧ P e w

/-- Perfect aspect: the event is over by the reference time. -/
def perfect (P : Event T → W → Prop) (r : NonemptyInterval T) (w : W) : Prop :=
  ∃ e, e.τ.precedes r ∧ P e w

/-- Present tense with perfect aspect describes an event over by the utterance time: the
English simple past needs no past pronoun to describe past events. -/
theorem perfect_pure (P : Event T → W → Prop) (t₀ : T) (w : W) :
    perfect P (NonemptyInterval.pure t₀) w ↔ ∃ e, e.τ.snd < t₀ ∧ P e w := Iff.rfl

end Aspect

/-! ### The Fragments' surface tenses (§7) -/

open English.Tense German.Tense

/-- The surface tense a row's `form` feature names. -/
def surface : String → Option SurfaceTense
  | "simple past" => some simplePastSurface
  | "Präteritum" => some preteritSurface
  | "Perfekt" => some perfektSurface
  | _ => none

/-- (40)–(41): a form is acceptable out of the blue iff its tense pronoun is defined there.
The English simple past and the German Perfekt, PRESENT + PERFECT, are; the Präteritum, an
anaphoric PAST, is not. -/
theorem rows_outOfTheBlue :
    ∀ r ∈ Examples.all, r.feature? "context" = some "out of the blue" →
      ∀ s ∈ (r.feature? "form").bind surface,
        (r.judgment = .acceptable ↔ s.tensePronoun.fullPresupposition (outOfTheBlue (0 : ℤ))) := by
  decide +kernel

/-- The English simple past and the German Perfekt share their decomposition, and both carry
the PERFECT that the Präteritum lacks. -/
theorem simplePast_eq_perfekt :
    simplePastSurface = perfektSurface ∧ preteritSurface.hasPerfect = false := ⟨rfl, rfl⟩

end Kratzer1998
