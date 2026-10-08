module

public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Fragments.Dutch.TemporalConnectives

/-!
# Dutch polarity items

Polarity items of Dutch typed by `PolarityItem`: *pas* 'only then', the positive polarity item
that serves as the punctual *until* and does not combine with negation ([giannakidou-2002], the
paper's (47); [karttunen-1974] on the parallel German *erst*), and *ooit* 'ever', which
[vanderwouden-1997] shows to be bipolar, a weak negative and a weak positive polarity item at once.

## Main results

* `Dutch.PolarityItems.ooit_admits`: the licensing theory admits *ooit* under *weinig* 'few' and
  *geen van* 'none of' and not under clausal negation, which licenses it and blocks it.

## References

* [giannakidou-2002]
* [karttunen-1974]
* [vanderwouden-1997]
-/

@[expose] public section

namespace Dutch.PolarityItems

open PolarityItem

/-- *pas*, the punctual *until* of a positive clause. Its connective entry is
`Dutch.TemporalConnectives.pas`. -/
def pas : PolarityItem :=
  { form := TemporalConnectives.pas.form
  , antiLicensor := some .antiMorphic }

/-- *ooit* 'ever', a weak negative polarity item that is also a weak positive polarity item:
*Weinig kinderen gaan ooit bij oma op bezoek* 'Few children ever visit granny', *Geen van de
kinderen gaat ooit bij oma op bezoek* 'None of the children ever visits granny', against
*\*Een van de kinderen gaat niet ooit bij oma op bezoek* ([vanderwouden-1997] (184)). -/
def ooit : PolarityItem :=
  { form := "ooit"
  , licensor := some .weak
  , antiLicensor := some .antiMorphic
  , licensingContexts := [.few, .nobody]
  , excludedContexts := [.negation] }

/-- The licensing theory admits *ooit* in its attested contexts and not under clausal negation,
which licenses it as a negative polarity item and blocks it as a positive one. -/
theorem ooit_admits :
    (∀ c ∈ ooit.licensingContexts, c.Admits ooit) ∧
      LicensingContext.negation.Licenses ooit ∧ ¬ LicensingContext.negation.Admits ooit := by
  simp +decide [ooit, LicensingContext.Admits]

end Dutch.PolarityItems
