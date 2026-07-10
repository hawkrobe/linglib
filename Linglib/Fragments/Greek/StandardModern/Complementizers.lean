import Linglib.Semantics.Verb.Basic
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Modern Greek Complementizers [christidis-1982] [roussou-2010]
[roussou-2019] [angelopoulos-2026]

The four Modern Greek complementizers, as root `Complementizer`
entries, and the matrix verbs that select them (with the attitude and
stativity metadata [angelopoulos-2026]'s data turns on).

[angelopoulos-2026]-specific apparatus — the [n]-feature/light-noun
selection (§3.1), the content/situation typing, the attested selection
classes, and the stativity generalizations — lives in
`Studies/Angelopoulos2026.lean` as projections over these entries.
-/

namespace Greek.StandardModern.Complementizers

/-- *oti* — indicative declarative complementizer ([christidis-1982],
    [roussou-2010]); selected by verbs of saying / belief / knowledge.
    Factivity of *oti*-clauses tracks the matrix verb (*kséro* vs
    *léo*), so no lexical `factive` value is recorded. -/
def oti : Complementizer where
  form := "oti"
  position := some .detached
  noonanType := some .indicative
  clauseForm := some .declarative

/-- *pu* — factive complementizer ([christidis-1982], [roussou-2019]);
    selected by emotive factives, and by perception/memory verbs on
    direct-perception readings ([angelopoulos-2026] fn. 16). Doubles as
    adverbial / relative / interrogative *where* ([angelopoulos-2026]
    unifies the uses via a PLACE noun); the entry records the
    complement use. -/
def pu : Complementizer where
  form := "pu"
  position := some .detached
  noonanType := some .indicative
  clauseForm := some .declarative
  factive := some true

/-- *an* — interrogative complementizer 'if' ([roussou-2010]); types
    embedded polar questions over indicative-inflected clauses, both
    selected (*anarotjéme* 'wonder') and, under matrix negation or
    question, unselected (*dhen kséro an* 'I don't know if'). -/
def an : Complementizer where
  form := "an"
  position := some .detached
  noonanType := some .indicative
  clauseForm := some .embeddedQuestion

/-- *na* — subjunctive ([grano-2024]); the *na*-selecting mood-choice
    verbs are in `MoodChoice.lean`. Whether *na* heads C or a Mood
    projection is debated; the schema is head-agnostic, and
    [angelopoulos-2026] sets *na* aside. -/
def na : Complementizer where
  form := "na"
  position := some .detached
  noonanType := some .subjunctive

/-- The complementizer inventory. -/
def complementizers : List Complementizer := [oti, pu, an, na]

/-! ### Matrix verbs selecting *oti*

Verbs of saying / belief / knowledge / understanding
([angelopoulos-2026] ex. 1a, 3, 36). -/

/-- *léo* (λέω) 'say' — past tense *ípe* in [angelopoulos-2026]
    ex. 1a. Speech-act verb, eventive (activity). -/
def leo : Verb where
  form := "léo"
  frames := [Frame.finiteClause]
  speechActVerb := true
  vendlerClass := some .activity

/-- *pistévo* (πιστεύω) 'believe' — doxastic, stative; the impersonal
    passive *pistévetai oti* is standard. -/
def pistevo : Verb where
  form := "pistévo"
  frames := [Frame.finiteClause]
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .state
  opaqueContext := true

/-- *kséro* (ξέρω) 'know' (alongside *gnorízo*) — factive doxastic,
    stative. Rejects manner adverbs ([angelopoulos-2026] ex. 21a). -/
def ksero : Verb where
  form := "kséro"
  frames := [Frame.finiteClause]
  attitude := some (.doxastic .veridical)
  vendlerClass := some .state

/-- *katalavéno* (καταλαβαίνω) 'understand' — eventive (allows
    manner adverbs in [angelopoulos-2026] ex. 21b),
    factive doxastic. -/
def katalaveno : Verb where
  form := "katalavéno"
  frames := [Frame.finiteClause]
  attitude := some (.doxastic .veridical)
  vendlerClass := some .achievement

/-- *sinidhitopió* (συνειδητοποιώ) 'realize' — eventive (achievement),
    factive doxastic ([angelopoulos-2026] ex. 21b). -/
def sinidhitopio : Verb where
  form := "sinidhitopió"
  frames := [Frame.finiteClause]
  attitude := some (.doxastic .veridical)
  vendlerClass := some .achievement

/-- *eksigó* (εξηγώ) 'explain' — accomplishment, takes *oti*
    yielding *explanans* reading ([angelopoulos-2026] ex. 4a). -/
def eksigo : Verb where
  form := "eksigó"
  frames := [Frame.finiteClause]
  vendlerClass := some .accomplishment

/-! ### Matrix verbs selecting *pu*

Emotive-factive predicates, stative under [angelopoulos-2026]'s §2.3
stativity restriction. -/

/-- *metanióno* (μετανιώνω) 'regret' — preferential (negative
    valence), stative. [angelopoulos-2026] ex. 1b, 20. -/
def metaniono : Verb where
  form := "metanióno"
  frames := [Frame.finiteClause]
  attitude := some (.preferential (.degreeComparison .negative))
  vendlerClass := some .state

/-- *aréso* (αρέσω) 'appeal to / be liked by' — Class III experiencer,
    stative ([angelopoulos-2026] ex. 13, 14; [landau-2010]). -/
def areso : Verb where
  form := "aréso"
  frames := [Frame.finiteClause]
  attitude := some (.preferential (.degreeComparison .positive))
  vendlerClass := some .state
  unaccusative := true

/-- *xérome* (χαίρομαι) 'be happy/glad' — preferential positive,
    stative. -/
def xerome : Verb where
  form := "xérome"
  frames := [Frame.finiteClause]
  attitude := some (.preferential (.degreeComparison .positive))
  vendlerClass := some .state

/-! ### Verbs compatible with both *oti* and *pu*

Eventive with *oti*, stative with *pu* ([angelopoulos-2026] ex. 19,
22–23, fn. 16). Both complements are finite indicative clauses, so the
polysemy rides on sense-tagged entry pairs (`SenseTag.stative`, the
`suivreStat` pattern) rather than frame-keyed `Verb.readings` rows. -/

/-- *thimáme* (θυμάμαι) 'remember' — eventive attitude sense ('recall,
    infer that'), the one available with *oti* ([angelopoulos-2026]
    ex. 22, fn. 16); the stative direct-perception recollection sense
    is `thimameStat`. -/
def thimame : Verb where
  form := "thimáme"
  frames := [Frame.finiteClause]
  attitude := some (.doxastic .veridical)
  vendlerClass := some .achievement

/-- *thimáme* — stative direct-perception recollection sense
    ('remember him reading'), the one available with *pu*
    ([angelopoulos-2026] fn. 16; [roussou-2010] ex. 17's strong
    presupposition). -/
def thimameStat : Verb where
  form := "thimáme"
  frames := [Frame.finiteClause]
  senseTag := .stative
  attitude := some (.doxastic .veridical)
  vendlerClass := some .state

/-- *thimóno* (θυμώνω) 'get angry' — eventive (achievement) sense, the
    one available with *oti*; the stative sense is `thimonoStat`
    ([angelopoulos-2026] ex. 19, 23). -/
def thimono : Verb where
  form := "thimóno"
  frames := [Frame.finiteClause]
  attitude := some (.preferential (.degreeComparison .negative))
  vendlerClass := some .achievement

/-- *thimóno* — stative 'be angry' sense, the one available with *pu*
    ([angelopoulos-2026] ex. 19, 23). -/
def thimonoStat : Verb where
  form := "thimóno"
  frames := [Frame.finiteClause]
  senseTag := .stative
  attitude := some (.preferential (.degreeComparison .negative))
  vendlerClass := some .state

end Greek.StandardModern.Complementizers
