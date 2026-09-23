module

public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Modern Greek Complementizers [christidis-1982] [roussou-2010]
[roussou-2019] [angelopoulos-2026]

The four Modern Greek complementizers, as root `Complementizer`
entries. The matrix verbs that select them are in `Verbs.lean`.

## References

* [christidis-1982]
* [roussou-2010]
* [roussou-2019]
* [angelopoulos-2026]
* [grano-2024]

[angelopoulos-2026]-specific apparatus — the [n]-feature/light-noun
selection (§3.1), the content/situation typing, the attested selection
classes, and the stativity generalizations — lives in
`Studies/Angelopoulos2026.lean` as projections over these entries.
-/

@[expose] public section

namespace Greek.StandardModern.Complementizers

/-- *oti* — indicative declarative complementizer ([christidis-1982],
    [roussou-2010]); selected by verbs of saying / belief / knowledge.
    Factivity of *oti*-clauses tracks the matrix verb (*kséro* vs
    *léo*), so no lexical `factive` value is recorded. -/
def oti : Complementizer where
  morphs := [.free "oti"]
  coding := some .indicative
  force := some .declarative

/-- *pu* — factive complementizer ([christidis-1982], [roussou-2019]);
    selected by emotive factives, and by perception/memory verbs on
    direct-perception readings ([angelopoulos-2026] fn. 16). Doubles as
    adverbial / relative / interrogative *where* ([angelopoulos-2026]
    unifies the uses via a PLACE noun); the entry records the
    complement use. -/
def pu : Complementizer where
  morphs := [.free "pu"]
  coding := some .indicative
  force := some .declarative
  factive := some true

/-- *an* — interrogative complementizer 'if' ([roussou-2010]); types
    embedded polar questions over indicative-inflected clauses, both
    selected (*anarotjéme* 'wonder') and, under matrix negation or
    question, unselected (*dhen kséro an* 'I don't know if'). -/
def an : Complementizer where
  morphs := [.free "an"]
  coding := some .indicative
  force := some .interrogative

/-- *na* — subjunctive ([grano-2024]), selected by volitional, intention and causative
    verbs (`Verbs.lean`). Whether *na* heads C or a Mood projection is debated; the schema is head-agnostic,
    and [angelopoulos-2026] sets *na* aside. -/
def na : Complementizer where
  morphs := [.free "na"]
  coding := some .subjunctive

/-- The complementizer inventory. -/
def complementizers : List Complementizer := [oti, pu, an, na]

end Greek.StandardModern.Complementizers
