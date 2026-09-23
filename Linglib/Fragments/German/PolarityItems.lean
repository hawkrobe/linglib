module

public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Fragments.German.TemporalConnectives

/-!
# German Polarity-Sensitive Items

German *irgendein*, [chierchia-2006]'s existential FCI (EFCI): NPI uses in
questions and conditionals, FCI uses under modals, with the *irgend-*
prefix marking domain widening. The negative quantifier *niemand* negates
rather than being licensed, and bare *wer* is a plain colloquial
indefinite ([haspelmath-1997] A.1) — neither is a polarity item, so
neither has an entry here. *erst* 'only then' is the positive polarity
punctual *until*, the twin of Finnish *vasta* ([karttunen-1974]). The
modal *brauchen* 'need' with a *zu*-infinitive is an anti-additive NPI
([buring-gunlogson-2000], [schaebbicke-seeliger-repp-2021]).

## References

* [haspelmath-1997]
* [chierchia-2006]
* [karttunen-1974]
* [buring-gunlogson-2000]
* [schaebbicke-seeliger-repp-2021]
* [van-rooy-2003-npi]
-/

@[expose] public section

namespace German.PolarityItems

open PolarityItem

/-- *irgendein/irgendwer* — [chierchia-2006]'s EFCI class: existential FCI
    with NPI uses (questions, conditionals) and FCI uses (modals,
    imperatives); *irgend-* marks domain widening. -/
def irgendein : PolarityItem :=
  { form := "irgendein/irgendwer"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.question, .conditionalAntecedent, .modalPossibility, .modalNecessity, .imperative]
  , scalarDirection := some .strengthening }

/-! ### NPI -/

/-- *brauchen* 'need' with a *zu*-infinitive: out in a plain declarative and in a positive polar
question, licensed by *niemand* and by *kein* ([buring-gunlogson-2000] (15), (16)). The rating
study of [schaebbicke-seeliger-repp-2021] (Fig. 2) agrees, and finds it intermediate under the
merely downward-entailing *kaum*: median 4 of 7, between 5.5 under *kein* and 1.5 in a positive
question. The library's table has questions license every weak NPI ([van-rooy-2003-npi]), so
the entry is anti-additive; the classification that study tests reserves questions for superweak
NPIs, and there the *kaum* rating leaves weak open. -/
def brauchen : PolarityItem :=
  { form := "brauchen"
  , licensor := some .antiAdditive
  , baseForce := .modal
  , licensingContexts := [.nobody] }

/-! ### PPI -/

/-- *erst* 'only then', the punctual *until* of a positive clause ([karttunen-1974], the paper's
(38)). Its connective entry is `German.TemporalConnectives.erst`. -/
def erst : PolarityItem :=
  { form := TemporalConnectives.erst.form
  , ppi := true
  , baseForce := .temporal
  , licensingContexts := [] }

/-! ### Verification -/

/-- Every attested context is predicted licensed. -/
theorem irgendein_licensing_sound :
    ∀ c ∈ irgendein.licensingContexts, c.licenses irgendein := by decide

/-- Every attested context is predicted licensed. -/
theorem brauchen_licensing_sound :
    ∀ c ∈ brauchen.licensingContexts, c.licenses brauchen := by decide

/-- *\*Braucht sie eine Entschuldigung mitzubringen?* ([buring-gunlogson-2000] (15c)): a positive
polar question does not license *brauchen*. -/
theorem not_question_licenses_brauchen : ¬ LicensingContext.question.licenses brauchen := by
  decide

end German.PolarityItems
