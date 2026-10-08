module

public import Linglib.Semantics.Polarity.Item
public import Linglib.Fragments.Dutch.TemporalConnectives

/-!
# Dutch polarity items

Polarity items of Dutch typed by `PolarityItem`: *pas* 'only then', the positive polarity item
that serves as the punctual *until* and does not combine with negation ([giannakidou-2002], the
paper's (47); [karttunen-1974] on the parallel German *erst*), and *ooit* 'ever', which
[vanderwouden-1997] shows to be bipolar, a weak negative and a weak positive polarity item at once;
`Studies/VanDerWouden1997.lean` checks the entry against his examples.

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

/-- *ooit* 'ever', a weak negative polarity item that is also a weak positive polarity item
([vanderwouden-1997]). -/
def ooit : PolarityItem :=
  { form := "ooit"
  , licensor := some .weak
  , antiLicensor := some .antiMorphic }

end Dutch.PolarityItems
