module

public import Linglib.Semantics.Polarity.Licensing

/-!
# Greek polarity items

Polarity items of Modern Greek typed by `PolarityItem`: *para monon*, literally 'but only', which
with a negated clause renders English punctual *until*. It is a negative polarity item in the
sense of Giannakidou's nonveridicality theory, licensed by negation and *xoris* 'without' and not
by *amfivalo* 'I doubt' or a rhetorical question, by her 2002 paper's (36)–(42).

## References

* [giannakidou-2002]
* [giannakidou-1998]
-/

@[expose] public section

namespace Greek.StandardModern.PolarityItems

open PolarityItem

/-- *para monon* (παρά μόνον) 'but only' is licensed by negation and *xoris* 'without', as in
*i prigipisa dhen eftase para monon ta mesanixta* 'the princess did not arrive until midnight'. -/
def paraMonon : PolarityItem :=
  { form := "para monon"
  , licensor := some .antiAdditive
  , licensingContexts := [.negation, .withoutClause] }

end Greek.StandardModern.PolarityItems
