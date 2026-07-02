import Linglib.Semantics.Verb.Basic
import Linglib.Syntax.Complementizer.Basic

/-!
# Modern Greek Complementizers [christidis-1982] [roussou-2010]
[roussou-2019] [angelopoulos-2026]

The three Modern Greek complementizers, as root `Complementizer`
entries, and the matrix verbs that select them (with the attitude and
stativity metadata [angelopoulos-2026]'s data turns on).

[angelopoulos-2026]-specific apparatus — the [n]-feature/light-noun
selection (§3.1), the content/situation typing, and the stativity
generalizations — lives in `Studies/Angelopoulos2026.lean` as
projections over these entries.
-/

namespace Greek.StandardModern.Complementizers

/-- *oti* — indicative declarative complementizer ([christidis-1982],
    [roussou-2010]); selected by verbs of saying / belief / knowledge. -/
def oti : Complementizer where
  form := "oti"
  position := some .detached
  noonanType := some .indicative
  clauseForm := some .declarative
  factive := some false

/-- *pu* — factive complementizer ([christidis-1982], [roussou-2019]);
    selected by emotive factives. Doubles as adverbial / relative /
    interrogative *where*; the entry records the complement use. -/
def pu : Complementizer where
  form := "pu"
  position := some .detached
  noonanType := some .indicative
  clauseForm := some .declarative
  factive := some true

/-- *na* — subjunctive ([grano-2024]); the substantive mood entries are
    in `MoodChoice.lean`, exposed here for inventory completeness. -/
def na : Complementizer where
  form := "na"
  position := some .detached
  noonanType := some .subjunctive

/-- The complementizer inventory. -/
def complementizers : List Complementizer := [oti, pu, na]

-- ════════════════════════════════════════════════════════════════
-- § 2. Matrix Verbs Selecting *oti*
-- ════════════════════════════════════════════════════════════════
--
-- Verbs of saying / belief / knowledge / understanding. All take
-- *oti*-complements per [angelopoulos-2026] ex. 1a, 3, 36, etc.

/-- *léo* (λέω) 'say' — past tense *ípe* in [angelopoulos-2026]
    ex. 1a. Speech-act verb, eventive (activity). -/
def leo : Verb where
  form := "léo"
  complementType := .finiteClause
  speechActVerb := true
  vendlerClass := some .activity

/-- *pistévo* (πιστεύω) 'believe' — doxastic, stative. -/
def pistevo : Verb where
  form := "pistévo"
  complementType := .finiteClause
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true

/-- *kséro* (ξέρω) 'know' (alongside *gnorízo*) — factive doxastic,
    stative. Rejects manner adverbs ([angelopoulos-2026] ex. 21a). -/
def ksero : Verb where
  form := "kséro"
  complementType := .finiteClause
  attitude := some (.doxastic .veridical)
  vendlerClass := some .state
  opaqueContext := false  -- factive ⇒ no opacity

/-- *katalavéno* (καταλαβαίνω) 'understand' — eventive (allows
    manner adverbs in [angelopoulos-2026] ex. 21b, 22a),
    factive doxastic. -/
def katalaveno : Verb where
  form := "katalavéno"
  complementType := .finiteClause
  attitude := some (.doxastic .veridical)
  vendlerClass := some .achievement

/-- *sinidhitopió* (συνειδητοποιώ) 'realize' — eventive (achievement),
    factive doxastic ([angelopoulos-2026] ex. 21b). -/
def sinidhitopio : Verb where
  form := "sinidhitopió"
  complementType := .finiteClause
  attitude := some (.doxastic .veridical)
  vendlerClass := some .achievement

/-- *eksigó* (εξηγώ) 'explain' — accomplishment, takes *oti*
    yielding *explanans* reading ([angelopoulos-2026] ex. 4a). -/
def eksigo : Verb where
  form := "eksigó"
  complementType := .finiteClause
  vendlerClass := some .accomplishment

-- ════════════════════════════════════════════════════════════════
-- § 3. Matrix Verbs Selecting *pu*
-- ════════════════════════════════════════════════════════════════
--
-- Emotive-factive predicates. Stative when taking *pu*-complements
-- ([angelopoulos-2026] §2.3 stativity restriction).

/-- *metanióno* (μετανιώνω) 'regret' — preferential (negative
    valence), stative. [angelopoulos-2026] ex. 1b, 20. -/
def metaniono : Verb where
  form := "metanióno"
  complementType := .finiteClause
  attitude := some (.preferential (.degreeComparison .negative))
  vendlerClass := some .state

/-- *aréso* (αρέσω) 'appeal to / be liked by' — Class III experiencer,
    stative ([angelopoulos-2026] ex. 13, 14; [landau-2009]). -/
def areso : Verb where
  form := "aréso"
  complementType := .finiteClause
  attitude := some (.preferential (.degreeComparison .positive))
  vendlerClass := some .state
  unaccusative := true

/-- *xérome* (χαίρομαι) 'be happy/glad' — preferential positive,
    stative. -/
def xerome : Verb where
  form := "xérome"
  complementType := .finiteClause
  attitude := some (.preferential (.degreeComparison .positive))
  vendlerClass := some .state

-- ════════════════════════════════════════════════════════════════
-- § 4. Verbs Compatible with Both *oti* and *pu*
-- ════════════════════════════════════════════════════════════════
--
-- Verbs whose stativity matters: with *oti* they are eventive,
-- with *pu* they shift to stative interpretation
-- ([angelopoulos-2026] ex. 22, fn 16). Polysemy handled via
-- sense tags rather than separate entries — the eventive sense is
-- the citation form here; the stative/perception sense is left
-- to be tracked in the consuming Studies file.

/-- *thimáme* (θυμάμαι) 'remember' — ambiguous between direct-
    perception (eventive, with *oti*) and stative recollection
    (with *pu*). Citation form is the eventive one;
    [angelopoulos-2026] ex. 22 contrasts the two. -/
def thimame : Verb where
  form := "thimáme"
  complementType := .finiteClause
  attitude := some (.doxastic .veridical)
  vendlerClass := some .achievement  -- eventive (perception) sense

/-- *thimóno* (θυμώνω) 'get/be angry' — eventive (achievement)
    normally; stative when taking *pu* ([angelopoulos-2026]
    ex. 19, 23). -/
def thimono : Verb where
  form := "thimóno"
  complementType := .finiteClause
  attitude := some (.preferential (.degreeComparison .negative))
  vendlerClass := some .achievement

end Greek.StandardModern.Complementizers
