import Linglib.Syntax.Category.Verb.Tense
import Linglib.Semantics.Tense.Pronoun
import Linglib.Semantics.Aspect.Basic
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
eventualities. Finally, what looks like a tense may spell out a tense together with one of
three aspects after [klein-1994], operators from properties of events to properties of times.
Out of the blue only the present is defined, and only the perfect places the event before
the reference time, so a form describes a past event out of the blue just in case it spells
out present tense with perfect aspect. The closing tables assign that combination to the
English simple past and the German *Perfekt* and never to the *Präteritum*, which is the
contrast between *Borromini built this church* and its two German renderings.

## Main declarations

* `ReferenceTime`, `Aspect` — the two indexical tenses and the three aspects, the axes of the
  closing tables, with their tense pronouns and their operators.
* `denote` — the truth conditions of a tense with an aspect.
* `Aspect.IsAnterior`, `ReferenceTime.IsDefinedOutOfTheBlue` — the two semantic properties the
  argument turns on, each characterized by a theorem.
* `Variety` — a variety's tense forms with the table that spells them out; `english`,
  `standardGerman` and `southGerman` are the paper's.
* `Variety.DescribesPastOutOfTheBlue` — a form spells out a combination that is defined out of
  the blue and anterior; `describesPastOutOfTheBlue_iff` reduces it to one cell of the table.
* `standardGerman_transparent`, `not_english_transparent` — the Standard German table can be
  read off the make-up of the forms, and the English one cannot.

## Implementation notes

An out-of-the-blue context is the temporal assignment sending every variable to the
utterance time, so the definedness of a tense pronoun there is its presupposition under the
library's `TensePronoun.fullPresupposition`. The aspect operators take a reference interval; a
tense supplies a point, embedded as `NonemptyInterval.pure`. The imperfective and the
perfective are the library's `Aspect.UNBOUNDED` and `Aspect.PRFV`; the perfect, with strict
precedence, is stronger than the relation of `Aspect.ViewpointType.perfect`, which admits an
event abutting the reference time (`perfect_ttTSitRelation`). The zero-pronoun typology of
§2–§3 and the locality argument from switch reference are prose. The French table is not
entered, since the library has no French tense forms.

## References

* [kratzer-1998]
* [partee-1973] — tenses as pronouns
* [abusch-1997], [ogihara-1989], [ogihara-1996] — sequence of tense and temporal de se
* [heim-kratzer-1998] — binder indices
* [klein-1994] — reference time and the aspects
-/

namespace Kratzer1998

open Tense Data.Examples
open _root_.Aspect (IntervalPred UNBOUNDED PRFV)

/-! ### The tenses (§4–§5) -/

/-- A reference time is present or past. These are the two indexical tenses, the columns of the
closing tables. -/
inductive ReferenceTime where
  | present
  | past
  deriving DecidableEq, Repr, Fintype

namespace ReferenceTime

/-- The cell of a tense is the position it presupposes of its reference relative to the
utterance time. -/
def cell : ReferenceTime → Finset Ordering
  | .present => Tense.present
  | .past => Tense.past

/-- The pronoun of a tense is the variable `n` presupposing the tense's position. -/
def pronoun (t : ReferenceTime) (n : ℕ) : TensePronoun where
  varIndex := n
  constraint := t.cell
  mode := .indexical

end ReferenceTime

/-- The zero tense is a variable with no presupposition, bound by the next tense up. -/
def zeroTense (n : ℕ) : TensePronoun where
  varIndex := n
  constraint := ⊤
  mode := .bound

section Tenses

variable {T : Type*}

/-- An out-of-the-blue context has no salient time but the utterance time, so every temporal
variable resolves to it. -/
def outOfTheBlue (t₀ : T) : TemporalAssignment T := Function.const ℕ t₀

/-- Out of the blue the present is defined, the utterance time including itself, and the past
is not, no provided interval preceding the utterance time. -/
theorem pronoun_outOfTheBlue_iff [LinearOrder T] (t : ReferenceTime) (n : ℕ) (t₀ : T) :
    (t.pronoun n).fullPresupposition (outOfTheBlue t₀) ↔ t = .present := by
  cases t <;>
    simp [TensePronoun.fullPresupposition, TensePronoun.resolve, TensePronoun.evalTime,
      ReferenceTime.pronoun, ReferenceTime.cell, outOfTheBlue, present, past]

/-- The zero tense has no presupposition. -/
theorem zeroTense_fullPresupposition [LinearOrder T] (n : ℕ) (g : TemporalAssignment T) :
    (zeroTense n).fullPresupposition g := Finset.mem_univ _

/-- A zero tense with a binder index makes its clause a property of times, (31). Whatever the
assignment, the abstract applied to `t` evaluates the clause at `t`. -/
theorem zeroTense_abstract (n : ℕ) (P : T → Prop) (g : TemporalAssignment T) (t : T) :
    temporalLambdaAbs n (fun g ↦ P ((zeroTense n).resolve g)) g t ↔ P t := by
  simp [temporalLambdaAbs, TensePronoun.resolve, interpTense, zeroTense]

/-- An indexical tense cannot be abstracted over by another index. The binder leaves the clause
a proposition about the tense's own reference, which is why an attitude verb forces a zero
tense. -/
theorem pronoun_not_abstracted (r : ReferenceTime) {m n : ℕ} (hn : n ≠ m) (P : T → Prop)
    (g : TemporalAssignment T) (t : T) :
    temporalLambdaAbs m (fun g ↦ P ((r.pronoun n).resolve g)) g t ↔ P (g n) := by
  simp [temporalLambdaAbs, TensePronoun.resolve, interpTense, ReferenceTime.pronoun,
    Function.update_of_ne hn]

end Tenses

/-! ### The aspects (§6–§7) -/

/-- An aspect is imperfective, perfective or perfect. These are the rows of the closing
tables. -/
inductive Aspect where
  | imperfective
  | perfective
  | perfect
  deriving DecidableEq, Repr, Fintype

section Aspect

variable {T W : Type*} [LinearOrder T]

/-- The operator of (38) turns a property of times into the property of eventualities that
holds of `e`, at any world, iff the property of times holds of the running time of `e` at every
world. -/
def star (P : IntervalPred W T) (_ : W) (e : Event T) : Prop :=
  ∀ w', P w' e.τ

/-- The temporal de re is semantically forced, since `star P` does not depend on the evaluation
world. -/
theorem star_congr (P : IntervalPred W T) (e : Event T) (w w' : W) :
    star P w e ↔ star P w' e := Iff.rfl

/-- The aspects map properties of events to properties of times. The imperfective includes the
reference time in the event time, the perfective includes the event time in the reference
time, and the perfect has the event over by the reference time. -/
def Aspect.denote : Aspect → (W → Event T → Prop) → IntervalPred W T
  | .imperfective => UNBOUNDED
  | .perfective => PRFV
  | .perfect => fun P w r ↦ ∃ e : Event T, e.τ.precedes r ∧ P w e

/-- The perfect entails the perfect viewpoint of the library, whose relation also admits an
event that ends exactly when the reference time begins. -/
theorem perfect_ttTSitRelation {P : W → Event T → Prop} {w : W} {r : NonemptyInterval T}
    (h : Aspect.perfect.denote P w r) :
    ∃ e, _root_.Aspect.ViewpointType.perfect.ttTSitRelation r e.τ ∧ P w e :=
  let ⟨e, he, hP⟩ := h
  ⟨e, le_of_lt he, hP⟩

/-- Tense `t` on the variable `n` with aspect `a` is true of an event property when the tense is
defined and the aspect holds of the property at the tense's reference. -/
def denote (t : ReferenceTime) (a : Aspect) (n : ℕ) (P : W → Event T → Prop)
    (g : TemporalAssignment T) (w : W) : Prop :=
  (t.pronoun n).fullPresupposition g ∧ a.denote P w (.pure ((t.pronoun n).resolve g))

/-- Out of the blue a tense with an aspect is true iff the tense is the present and the aspect
holds at the utterance time. -/
theorem denote_outOfTheBlue_iff (t : ReferenceTime) (a : Aspect) (n : ℕ)
    (P : W → Event T → Prop) (t₀ : T) (w : W) :
    denote t a n P (outOfTheBlue t₀) w ↔ t = .present ∧ a.denote P w (.pure t₀) := by
  rw [denote, pronoun_outOfTheBlue_iff]; rfl

/-- Present tense with perfect aspect describes an event over by the utterance time, so a past
event can be described with no past tense. -/
theorem denote_present_perfect_outOfTheBlue_iff (n : ℕ) (P : W → Event T → Prop) (t₀ : T)
    (w : W) :
    denote .present .perfect n P (outOfTheBlue t₀) w ↔ ∃ e : Event T, e.τ.snd < t₀ ∧ P w e := by
  simp [denote_outOfTheBlue_iff, Aspect.denote, NonemptyInterval.precedes]

end Aspect

/-- An anterior aspect places its event before the reference time, whatever the times, the
worlds and the event property. -/
def Aspect.IsAnterior (a : Aspect) : Prop :=
  ∀ {T W : Type} [LinearOrder T] (P : W → Event T → Prop) (w : W) (r : NonemptyInterval T),
    a.denote P w r → ∃ e : Event T, e.τ.precedes r ∧ P w e

/-- A tense is defined out of the blue when its presupposition holds in every such context. -/
def ReferenceTime.IsDefinedOutOfTheBlue (t : ReferenceTime) : Prop :=
  ∀ {T : Type} [LinearOrder T] (n : ℕ) (t₀ : T), (t.pronoun n).fullPresupposition (outOfTheBlue t₀)

/-- Only the perfect is anterior, since an event whose time is the reference time satisfies the
imperfective and the perfective. -/
theorem Aspect.isAnterior_iff (a : Aspect) : a.IsAnterior ↔ a = .perfect := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ fun _ _ _ h ↦ h⟩
  by_contra ha
  have key : a.denote (fun (_ : Unit) (_ : Event Unit) ↦ True) () (.pure ()) := by
    cases a
    · exact ⟨⟨.pure (), .action⟩, le_rfl, trivial⟩
    · exact ⟨⟨.pure (), .action⟩, le_rfl, trivial⟩
    · exact absurd rfl ha
  obtain ⟨e, he, -⟩ := h _ _ _ key
  exact absurd he (by simp [NonemptyInterval.precedes])

/-- Only the present is defined out of the blue. -/
theorem ReferenceTime.isDefinedOutOfTheBlue_iff (t : ReferenceTime) :
    t.IsDefinedOutOfTheBlue ↔ t = .present :=
  ⟨fun h ↦ (pronoun_outOfTheBlue_iff t 0 ()).1 (h 0 ()),
    fun h _ _ n t₀ ↦ (pronoun_outOfTheBlue_iff t n t₀).2 h⟩

instance : DecidablePred Aspect.IsAnterior :=
  fun a ↦ decidable_of_iff _ a.isAnterior_iff.symm

instance : DecidablePred ReferenceTime.IsDefinedOutOfTheBlue :=
  fun t ↦ decidable_of_iff _ t.isDefinedOutOfTheBlue_iff.symm

/-! ### What the tense forms spell out (§7) -/

/-- A variety of a language, as the closing tables describe it, consists of its tense forms and,
for each reference time and aspect, the forms that spell the combination out. -/
structure Variety where
  /-- The tense forms of the variety. -/
  forms : List Tense.Form
  /-- The forms that spell out a reference time with an aspect. -/
  spellOut : ReferenceTime → Aspect → List Tense.Form

open English in
/-- In English the progressive forms spell out the imperfective and the simple forms the
perfective, and the simple past also spells out the perfect, of the present as of the past. -/
def english : Variety where
  forms := tenseForms
  spellOut
    | .present, .imperfective => [presentProgressive]
    | .past, .imperfective => [pastProgressive]
    | .present, .perfective => [simplePresent]
    | .past, .perfective => [simplePast]
    | .present, .perfect => [simplePast]
    | .past, .perfect => [simplePast, pastPerfect]

open German in
/-- In Standard German the synthetic forms spell out the imperfective and the perfective, and
the forms with a participle the perfect. -/
def standardGerman : Variety where
  forms := tenseForms
  spellOut
    | .present, .imperfective | .present, .perfective => [praesens]
    | .past, .imperfective | .past, .perfective => [praeteritum]
    | .present, .perfect => [perfekt]
    | .past, .perfect => [plusquamperfekt]

open German in
/-- In South German, with the *Präteritum* gone, the *Perfekt* also spells out the past with the
imperfective and the perfective, and the double perfect the past with the perfect. -/
def southGerman : Variety where
  forms := southernTenseForms
  spellOut
    | .present, .imperfective | .present, .perfective => [praesens]
    | .past, .imperfective | .past, .perfective => [perfekt]
    | .present, .perfect => [perfekt]
    | .past, .perfect => [doppelperfekt]

namespace Variety

/-- A form can describe a past event out of the blue when it spells out a tense defined out of
the blue with an anterior aspect. -/
def DescribesPastOutOfTheBlue (v : Variety) (f : Tense.Form) : Prop :=
  ∃ t a, f ∈ v.spellOut t a ∧ t.IsDefinedOutOfTheBlue ∧ a.IsAnterior

/-- A form can describe a past event out of the blue iff it spells out the present with the
perfect. -/
theorem describesPastOutOfTheBlue_iff (v : Variety) (f : Tense.Form) :
    v.DescribesPastOutOfTheBlue f ↔ f ∈ v.spellOut .present .perfect := by
  simp [DescribesPastOutOfTheBlue, ReferenceTime.isDefinedOutOfTheBlue_iff,
    Aspect.isAnterior_iff]

instance (v : Variety) : DecidablePred v.DescribesPastOutOfTheBlue :=
  fun f ↦ decidable_of_iff _ (v.describesPastOutOfTheBlue_iff f).symm

/-- A variety is transparent when its table can be read off the make-up of its forms, a form
spelling out the reference time its finite verb is inflected for, and the perfect just in case
it has a past participle. -/
def IsTransparent (v : Variety) : Prop :=
  ∀ f ∈ v.forms, ∀ t a, f ∈ v.spellOut t a ↔
    (f.finite = .Pres ↔ t = .present) ∧ (.pastParticiple ∈ f.nonfinite ↔ a = .perfect)

instance (v : Variety) : Decidable v.IsTransparent :=
  by unfold IsTransparent; infer_instance

end Variety

/-- Standard German is transparent. -/
theorem standardGerman_transparent : standardGerman.IsTransparent := by decide +kernel

/-- English is not transparent, since the simple past, a past inflection with no participle,
spells out the present with the perfect. -/
theorem not_english_transparent : ¬ english.IsTransparent := by decide +kernel

/-- South German is not transparent, since the *Perfekt*, a present inflection, spells out the
past. -/
theorem not_southGerman_transparent : ¬ southGerman.IsTransparent := by decide +kernel

/-- The backward-shifted reading of a past under a past, (42), is the past with the perfect,
which the English simple past spells out and the *Präteritum* does not, so that Standard German
needs the *Plusquamperfekt*. -/
theorem backwardShifted :
    English.simplePast ∈ english.spellOut .past .perfect ∧
      ∀ f, f ∈ standardGerman.spellOut .past .perfect ↔ f = German.plusquamperfekt := by
  simp [english, standardGerman]

/-- The language codes of the example rows name these varieties. -/
def varieties : List (String × Variety) := [("stan1293", english), ("stan1295", standardGerman)]

/-- In (40) and (41) a form is acceptable out of the blue iff it can describe a past event
there. The English simple past and the German *Perfekt* can, and the *Präteritum* cannot. -/
theorem rows_outOfTheBlue :
    ∀ r ∈ Examples.all, r.feature? "context" = some "out of the blue" →
      ∀ v ∈ varieties.lookup r.language, ∀ f ∈ v.forms, r.feature? "form" = some f.name →
        (r.judgment = .acceptable ↔ v.DescribesPastOutOfTheBlue f) := by
  decide +kernel

end Kratzer1998
