import Linglib.Syntax.Negation

/-!
# Italian negation

Italian negates a clause with the preverbal particle *non*, and nothing else in the clause
changes, in any person or tense: *canto* 'I sing', *non canto* 'I do not sing'. Object clitics
stand between *non* and the verb. The same *non* occurs expletively, contributing no negation,
under *prima che* 'before', *dubitare* 'doubt', *appena* 'hardly', *per poco* 'nearly', *di
quanto* 'than', *a meno che* 'unless', *finché* 'until' and *senza che* 'without', the triggers
[jin-koenig-2021] record for the language. N-words and the other polarity-sensitive items are
entered in `Fragments/Romance/Italian/PolarityItems.lean`. The examples are those of [miestamo-2005].

## References

* [miestamo-2005]
* [jin-koenig-2021]
-/

open Negation Morphology

namespace Italian.Negation

/-- *non*, the standard negator. -/
def non : Marker := { pieces := [[.free "non"]] }

private def words (ws : List String) : List Morph := ws.map .free

/-- The first person singular present and future of *cantare* 'sing'. -/
def pairs : List Pair :=
  [⟨words ["canto"], words ["non", "canto"]⟩,
   ⟨words ["canterò"], words ["non", "canterò"]⟩]

end Italian.Negation
