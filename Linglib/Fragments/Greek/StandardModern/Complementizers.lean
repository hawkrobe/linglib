import Linglib.Semantics.Verb.Basic

/-!
# Modern Greek Complementizers [christidis-1982] [roussou-2010]
[roussou-2019] [angelopoulos-2026]

The three Modern Greek complementizers and a small inventory of
matrix verbs that select them. Consensus-only metadata: form, mood
(indicative / subjunctive / factive), categorial [n]-feature, and
the stativity / attitude classification of the matrix verbs.

## Scope

This file exposes ONLY consensus typological metadata. The
content/situation typing of the matrix-verb selection that
[angelopoulos-2026] introduces (following [bondarenko-2022])
is paper-specific apparatus and lives in
`Studies/Angelopoulos2026.lean` as a
projection over these `Verb` entries — it does not pollute the
fragment schema.

## Three complementizers

- *oti* — indicative declarative ([christidis-1982],
  [roussou-2010]). Combines with verbs of saying / belief /
  knowledge. Bears an uninterpretable [n]-feature checked by a
  light noun in its specifier per [angelopoulos-2026] §3.1.
- *pu* — factive declarative ([christidis-1982],
  [roussou-2019]). Combines with emotive factives and
  doubles as adverbial / relative / interrogative pronoun *where*.
  Bears the same [n]-feature as *oti*.
- *na* — subjunctive ([grano-2024]). Already covered in
  `Greek.StandardModern.MoodChoice`; referenced here
  for completeness, not redefined.
-/

namespace Greek.StandardModern.Complementizers


-- ════════════════════════════════════════════════════════════════
-- § 1. Complementizer Inventory
-- ════════════════════════════════════════════════════════════════

/-- The three Modern Greek complementizers covered here. *na* is
    in `MoodChoice.lean`; `GreekComplementizer.na` is exposed for
    cross-reference but the substantive entries live there. -/
inductive GreekComplementizer where
  | oti
  | pu
  | na
  deriving DecidableEq, Repr

/-- Phonological form. -/
def GreekComplementizer.form : GreekComplementizer → String
  | .oti => "oti"
  | .pu  => "pu"
  | .na  => "na"

/-- Bears an uninterpretable [n]-feature checked by a light noun
    in Spec,CP per [angelopoulos-2026] §3.1.  *na* does not
    bear [n]; its checking machinery is mood-driven ([grano-2024]). -/
def GreekComplementizer.bearsN : GreekComplementizer → Bool
  | .oti => true
  | .pu  => true
  | .na  => false

/-- Factive presupposition (consensus across [christidis-1982],
    [roussou-2010], [roussou-2019], [angelopoulos-2026]). -/
def GreekComplementizer.isFactive : GreekComplementizer → Bool
  | .pu => true
  | _   => false

/-- All three are finite. -/
theorem all_finite (c : GreekComplementizer) : c.form.length > 0 := by
  cases c <;> decide

/-- *oti* and *pu* both bear the [n]-feature; *na* does not. -/
theorem n_bearing_complementizers :
    GreekComplementizer.oti.bearsN = true ∧
    GreekComplementizer.pu.bearsN  = true ∧
    GreekComplementizer.na.bearsN  = false := ⟨rfl, rfl, rfl⟩

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
  altComplementType := some .finiteClause  -- pu-complement available
  attitude := some (.doxastic .veridical)
  vendlerClass := some .achievement  -- eventive (perception) sense

/-- *thimóno* (θυμώνω) 'get/be angry' — eventive (achievement)
    normally; stative when taking *pu* ([angelopoulos-2026]
    ex. 19, 23). -/
def thimono : Verb where
  form := "thimóno"
  complementType := .finiteClause
  altComplementType := some .finiteClause
  attitude := some (.preferential (.degreeComparison .negative))
  vendlerClass := some .achievement

-- ════════════════════════════════════════════════════════════════
-- § 5. Theorems on consensus stativity
-- ════════════════════════════════════════════════════════════════

/-- The *pu*-only verbs are all stative. This is the consensus
    pattern ([angelopoulos-2026] §2.3, restating the diagnostic
    from [roussou-2019]). -/
theorem pu_only_verbs_stative :
    metaniono.vendlerClass = some .state ∧
    areso.vendlerClass     = some .state ∧
    xerome.vendlerClass    = some .state := ⟨rfl, rfl, rfl⟩

/-- The *oti*-only verbs span eventive and stative classes:
    *léo*, *katalavéno*, *sinidhitopió*, *eksigó* are eventive;
    *pistévo* and *kséro* are stative. -/
theorem oti_verbs_stativity_split :
    leo.vendlerClass = some .activity ∧
    katalaveno.vendlerClass = some .achievement ∧
    pistevo.vendlerClass = some .state ∧
    ksero.vendlerClass = some .state := ⟨rfl, rfl, rfl, rfl⟩

end Greek.StandardModern.Complementizers
