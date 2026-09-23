module

public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Fragments.Greek.StandardModern.TemporalConnectives

/-!
# Greek polarity items

Polarity items of Modern Greek typed by `Polarity.Item`: *para monon*, literally 'but only', the
punctual *until* of a negated clause and a negative polarity item in the sense of
[giannakidou-1998], licensed by negation and *xoris* 'without' and not by *amfivalo* 'I doubt' or
a rhetorical question ([giannakidou-2002], the paper's (36)–(42)).

## References

* [giannakidou-2002]
* [giannakidou-1998]
-/

@[expose] public section

namespace Greek.StandardModern.PolarityItems

open Polarity

/-- *para monon*, the punctual *until*: licensed by negation and *xoris* 'without'. Its connective
entry is `Greek.StandardModern.TemporalConnectives.paraMonon`. -/
def paraMonon : Item :=
  { form := TemporalConnectives.paraMonon.form
  , licensor := some .antiAdditive
  , baseForce := .temporal
  , licensingContexts := [.negation, .withoutClause] }

end Greek.StandardModern.PolarityItems
