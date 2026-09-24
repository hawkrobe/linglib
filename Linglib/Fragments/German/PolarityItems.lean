module

public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Fragments.German.ModalIndefinites
public import Linglib.Fragments.German.TemporalConnectives

/-!
# German polarity-sensitive items

This file defines the German polarity-sensitive items: the indefinite *irgendein*, the modal
*brauchen* 'need' and the punctual *erst* 'only then'. Each entry records the environments in
which the item is attested, and the licensing theory of `Semantics/Polarity/Licensing.lean`
predicts which environments license it.

*Irgendein* is an existential indefinite with free-choice effects under modals. Kratzer and
Shimoyama attest it under possibility and necessity modals, under negative quantifiers such as
*niemand* 'nobody' and *auf keinen Fall* 'in no case', under *bezweifeln* 'doubt' and in an
embedded question, and they find it ungrammatical under the inflectional negation *nicht* unless
*irgend* is stressed. It is also fine in an episodic sentence, where it signals the speaker's
ignorance or indifference, which is not a licensing environment. Its analysis as a modal
indefinite is `German.ModalIndefinites.irgendein`. *Brauchen* with a *zu*-infinitive occurs only
with a negative or with *nur* or *bloß* 'only'; Büring and Gunlogson, and Schaebbicke, Seeliger
and Repp in a rating study, find it licensed by *niemand* and *kein* and out in a positive polar
question. *Erst* is the positive polarity *until* of Karttunen's chart, the connective
`German.TemporalConnectives.erst`.

## References

* [kratzer-shimoyama-2002]
* [durrell-2011]
* [buring-gunlogson-2000]
* [schaebbicke-seeliger-repp-2021]
* [van-rooy-2003-npi]
* [karttunen-1974]
-/

@[expose] public section

namespace German.PolarityItems

open PolarityItem

/-- *Irgendein* is an existential indefinite with free-choice effects, attested in questions, under
*bezweifeln*, under possibility and necessity modals and under negative quantifiers. -/
def irgendein : PolarityItem :=
  { form := ModalIndefinites.irgendein.form
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.question, .doubtVerb, .modalPossibility, .modalNecessity, .nobody] }

/-! ### NPI -/

/-- *Brauchen* 'need' with a *zu*-infinitive is out in a plain declarative and in a positive polar
question and is licensed by *niemand* and by *kein*. The rating study of Schaebbicke, Seeliger and
Repp finds it intermediate under the merely downward-entailing *kaum*, with a median of 4 of 7
between 5.5 under *kein* and 1.5 in a positive question. The licensing table has questions license
every weak NPI, after van Rooy, so the entry is anti-additive; the classification the rating study
tests reserves questions for superweak NPIs, and there the *kaum* rating leaves weak open. -/
def brauchen : PolarityItem :=
  { form := "brauchen"
  , licensor := some .antiAdditive
  , baseForce := .modal
  , licensingContexts := [.nobody] }

/-! ### PPI -/

/-- *Erst* 'only then' is the punctual *until* of a positive clause. -/
def erst : PolarityItem :=
  { form := TemporalConnectives.erst.form
  , ppi := true
  , baseForce := .temporal
  , licensingContexts := [] }

/-! ### Licensing -/

/-- Every environment in which *irgendein* is attested licenses it. -/
theorem irgendein_licensing_sound :
    ∀ c ∈ irgendein.licensingContexts, c.licenses irgendein := by decide

/-- Every environment in which *brauchen* is attested licenses it. -/
theorem brauchen_licensing_sound :
    ∀ c ∈ brauchen.licensingContexts, c.licenses brauchen := by decide

/-- A positive polar question does not license *brauchen*, as in *\*Braucht sie eine
Entschuldigung mitzubringen?* -/
theorem not_question_licenses_brauchen : ¬ LicensingContext.question.licenses brauchen := by
  decide

end German.PolarityItems
