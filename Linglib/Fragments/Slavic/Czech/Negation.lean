module

public import Linglib.Syntax.Negation

/-!
# Czech negation

Czech negates a clause with the prefix *ne-* on the verb, "Petr neplave" 'Peter doesn't swim'
([short-1993-czech], p. 510). In the past tense and the conditional the prefix goes on the
*l*-participle, in the imperfective future on the auxiliary, *Petr se nebude učit* 'Peter won't
study', and on a modal auxiliary, which it then negates. Negation is concordant: "any negative
subject or object pronoun or pronoun-adverb is reinforced by ne- in the verb", *Nikdo to
nekoupil* 'No one bought it' (p. 511). The concord items are in the sibling `PolarityItems.lean`.

## References

* [short-1993-czech]
-/

@[expose] public section

open Negation Morphology

namespace Czech.Negation

/-- *ne-*, the standard negation prefix. -/
def ne : Marker := { pieces := [[.pref "ne"]] }

/-- *Petr se musí učit* 'Peter must study' and *Petr smí přijít* 'Peter may come', with their
negatives *Petr se nemusí učit* 'Peter needn't study' and *Petr nesmí přijít* 'Peter must not
come' (p. 510). -/
def pairs : List Pair :=
  [⟨[.free "Petr", .free "se", .root "musí", .free "učit"],
    [.free "Petr", .free "se", .pref "ne", .root "musí", .free "učit"]⟩,
   ⟨[.free "Petr", .root "smí", .free "přijít"],
    [.free "Petr", .pref "ne", .root "smí", .free "přijít"]⟩]

end Czech.Negation
