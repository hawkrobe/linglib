import Linglib.Syntax.Reciprocal
import Linglib.Fragments.Romance.Italian.Pronouns
import Linglib.Fragments.Romance.Italian.Verbs

/-!
# Italian reciprocals

Italian marks reciprocity with the clitic *si*, which is also the third-person reflexive clitic,
so a clause such as *Mary e Lisa si sono descritte* reads as 'Mary and Lisa described
themselves' or as 'Mary and Lisa described each other', and the adverbial *a vicenda* 'mutually'
leaves only the reciprocal reading. A closed class of transitive verbs, *abbracciare* 'hug',
*baciare* 'kiss', *sposare* 'marry' and the others of Palmieri's Appendix A, also reads
reciprocally with no marker at all under the causative *fare*, *Ho fatto abbracciare Mary e
Lisa* 'I made Mary and Lisa hug', where *si* is in fact excluded, though in a finite clause the
same verbs still need it. These are the lexical reciprocals; their entries are those of
`Verbs`, and Palmieri's analysis of the class is `Studies/Palmieri2024.lean`.

## References

* [palmieri-2024]
-/

namespace Italian.Reciprocals

open Reciprocal

/-- The clitic *si*, reciprocal or reflexive, the third-person reflexive clitic of `Pronouns`. -/
def si : Marker :=
  { form := Pronouns.si.form, strategy := .recipClitic, readings := {.reciprocal, .reflexive} }

/-- The reciprocal marker inventory. -/
def markers : Finset Marker := {si}

/-- The transitive verbs of Palmieri's Appendix A with a lexical reciprocal use, as verb entries,
since the lexical strategy marks predicates rather than forms. -/
def lexicalReciprocals : List Verb :=
  [Verbs.abbracciare, Verbs.baciare, Verbs.coccolare, Verbs.conoscere,
    Verbs.consultare, Verbs.frequentare, Verbs.incontrare, Verbs.incrociare,
    Verbs.lasciare, Verbs.sposare, Verbs.trovare, Verbs.vedere]

end Italian.Reciprocals
