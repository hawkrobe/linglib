module

public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Fragments.Dutch.TemporalConnectives

/-!
# Dutch polarity items

Polarity items of Dutch typed by `PolarityItem`: *pas* 'only then', the positive polarity item
that serves as the punctual *until* and does not combine with negation ([giannakidou-2002], the
paper's (47); [karttunen-1974] on the parallel German *erst*).

## References

* [A. Giannakidou, *UNTIL, Aspect, and Negation: A Novel Argument for Two "Until"s*
  (2002)][giannakidou-2002]
* [L. Karttunen, *Until* (1974)][karttunen-1974]
-/

@[expose] public section

namespace Dutch.PolarityItems

open PolarityItem

/-- *pas*, the punctual *until* of a positive clause. Its connective entry is
`Dutch.TemporalConnectives.pas`. -/
def pas : PolarityItem :=
  { form := TemporalConnectives.pas.form
  , ppi := true
  , baseForce := .temporal
  , licensingContexts := [] }

end Dutch.PolarityItems
