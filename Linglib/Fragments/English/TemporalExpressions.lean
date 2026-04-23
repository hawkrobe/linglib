import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Theories.Semantics.Tense.TemporalAdverbials
import Linglib.Core.Lexical.PolarityItem
import Linglib.Fragments.English.FunctionWords

/-!
# English Temporal Expressions Fragment
@cite{alstott-aravind-2026} @cite{heinamaki-1974} @cite{rett-2020} @cite{karttunen-1974} @cite{ogihara-steinert-threlkeld-2024} @cite{iatridou-anagnostopoulou-izvorski-2001} @cite{vendler-1957}

Lexical entries for English temporal expressions, organised into two sibling
structures (mathlib pattern, mirroring `QuantifierEntry` + `NumericalDetEntry`
in `Determiners.lean`):

- `TemporalExprEntry` — **ordering expressions**: subordinating connectives
  (*before*, *after*, *while*, *when*, *until*, *since*, *till*) and ordering
  modifiers (*within*, *at*, *by*). The `complementType` field captures the
  clausal-vs-nominal distinction; semantic fields (`order`, `licensesNPI`,
  `complementVeridical`) are shared so generalizations like @cite{rett-2020}'s
  veridicality typology apply uniformly.

- `DurationExprEntry` — **duration / measure adverbials**: *for*, *in* (telic
  and NPI-gap readings), *ago*. These take a measure phrase and yield a
  modifier whose semantics involves *measuring* an interval rather than
  *ordering* two time points. The schema is consensus-only: surface form,
  IAI 2001 typological classification, NPI status and strength, perfect /
  negation requirements, Vendler-class selection. Paper-specific apparatus
  (Rouillard 2026's E-TIA / G-TIA labels, M = τ vs M = id parameterization,
  IAI's PTS apparatus) lives in the relevant Theory or Studies file as
  partial projections from `DurationExprEntry`, not as fields on it.

-/

namespace Fragments.English.TemporalExpressions

open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs
open Semantics.Tense.TemporalAdverbials (AdverbialType)
open Core.Lexical.PolarityItem (PolarityType)

-- ============================================================================
-- § 1: Shared Types
-- ============================================================================

/-- Temporal ordering relation encoded by a connective or modifier. -/
inductive TemporalOrder where
  | before
  | after
  | while_
  | when_
  | until_
  | since_
  | by_
  | whenever
  deriving DecidableEq, Repr, Inhabited

/-- Available readings for a temporal clause or modified VP.
    "Start" = initial point of embedded eventuality; "finish" = final point. -/
inductive Reading where
  | beforeStart   -- ME precedes onset of EE
  | beforeFinish  -- ME precedes telos of EE
  | afterStart    -- ME follows onset of EE
  | afterFinish   -- ME follows telos of EE
  | durative      -- ME overlaps with EE runtime
  deriving DecidableEq, Repr, Inhabited

/-- Syntactic complement type: clausal (*before she arrived*) vs
    nominal (*by 3pm*, *within an hour*). -/
inductive ComplementType where
  | clausal
  | nominal
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- § 2: Unified Temporal Expression Entry
-- ============================================================================

/-- Lexical entry for any temporal expression — subordinating connective
    or adverbial modifier. Unifies the semantic fields (ordering direction,
    NPI licensing, veridicality) that @cite{heinamaki-1974} shows are shared
    across both syntactic categories.

    The `complementType` field records the syntactic distinction (clausal
    vs nominal complement) without splitting the semantic properties into
    separate types. -/
structure TemporalExprEntry where
  /-- Surface form -/
  form : String
  /-- Syntactic complement type -/
  complementType : ComplementType
  /-- Temporal ordering direction -/
  order : TemporalOrder
  /-- Does this expression license NPIs in its complement? -/
  licensesNPI : Bool
  /-- Reading obtained without coercion (Rett's strong default) -/
  defaultReading : Reading
  /-- Reading requiring aspectual coercion (INCHOAT or COMPLET) -/
  coercedReading : Option Reading
  /-- Does telicity of the embedded clause affect interpretation? -/
  embeddedTelicityEffect : Bool
  /-- Attested in all 17 languages of @cite{rett-2020}'s typological survey -/
  crossLinguisticBasic : Bool
  /-- Does the expression entail the truth of its complement?
      *after* is veridical: "He left after she arrived" entails she arrived.
      *before* is non-veridical: "He left before she arrived" is compatible
      with her not arriving. -/
  complementVeridical : Bool
  /-- Does this expression force a punctual (point-like) reading? -/
  forcesPunctual : Bool
  /-- Which coercion operator is *mandatorily* triggered (if any).
      `some "INCHOAT"` or `some "COMPLET"` for modifiers that force coercion
      (e.g. *within*, *at*). `none` for connectives like *before*/*after* where
      coercion is optional — those use `coercedReading` to record the
      alternative reading available through voluntary coercion. -/
  triggeredCoercion : Option String
  deriving Repr, BEq

-- ============================================================================
-- § 3: Connective Entries (clausal complement)
-- ============================================================================

/-- *before*: licenses NPIs; default = before-start; coerced = before-finish
    (requires COMPLET to extract telos of telic EE). -/
def before_ : TemporalExprEntry :=
  { form := "before"
  , complementType := .clausal
  , order := .before
  , licensesNPI := true
  , defaultReading := .beforeStart
  , coercedReading := some .beforeFinish
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := false
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *after*: no NPIs; default = after-finish; coerced = after-start
    (requires INCHOAT to extract onset of atelic EE). -/
def after_ : TemporalExprEntry :=
  { form := "after"
  , complementType := .clausal
  , order := .after
  , licensesNPI := false
  , defaultReading := .afterFinish
  , coercedReading := some .afterStart
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *while*: durative overlap, no coercion, no telicity sensitivity. -/
def while_conn : TemporalExprEntry :=
  { form := "while"
  , complementType := .clausal
  , order := .while_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *until*: durative persistence up to complement time.
    Has two uses:
    - **Durative**: "John slept until 3pm" — main clause is stative, *until*
      marks minimum extent. Truth-conditionally = temporal overlap.
    - **Punctual** (with negation): "He didn't wake up until 3pm" — logical
      form = NOT(A BEFORE T). Licenses NPIs in this use.

    We encode the durative reading as default, with the punctual reading
    arising compositionally via negation + the `before` semantics. -/
def until_ : TemporalExprEntry :=
  { form := "until"
  , complementType := .clausal
  , order := .until_
  , licensesNPI := true
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *when*: temporal coincidence, no coercion. Veridical complement.
    "John arrived when Mary left" — the two events overlap in time.
    Symmetric: "A when B" ↔ "B when A". -/
def when_conn : TemporalExprEntry :=
  { form := "when"
  , complementType := .clausal
  , order := .when_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *since*: starting-point connective. Veridical complement.
    "He's been happy since she arrived" entails she arrived.
    Requires durative (stative/activity) main clause, like *until*.
    Does not license NPIs. -/
def since_conn : TemporalExprEntry :=
  { form := "since"
  , complementType := .clausal
  , order := .since_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *till*: dialectal variant of *until*.
    Identical semantic properties to *until*. Dialectally restricted:
    not universal across English varieties. -/
def till_conn : TemporalExprEntry :=
  { form := "till"
  , complementType := .clausal
  , order := .until_
  , licensesNPI := true
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

-- ============================================================================
-- § 4: Modifier Entries (nominal complement)
-- ============================================================================

/-- *within* + duration: relevant to INCHOAT debate.
    Alstott & Aravind Exps 1a, 3: "within an hour" + activity verb.
    Alstott & Aravind found no INCHOAT cost here. -/
def within_ : TemporalExprEntry :=
  { form := "within"
  , complementType := .nominal
  , order := .while_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := some "INCHOAT" }

/-- *at* + time point: relevant to COMPLET debate.
    Alstott & Aravind Exp 1b: "at 7 o'clock" + accomplishment.
    Forces punctual reading → COMPLET required for telic events. -/
def at_punct : TemporalExprEntry :=
  { form := "at"
  , complementType := .nominal
  , order := .when_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := true
  , triggeredCoercion := some "COMPLET" }

/-- *by* + time point: deadline semantics.
    "He arrived by 3pm" = at or before 3pm.
    Weaker than *before* (allows coincidence). Does not force punctual
    reading: "He had finished the book by Tuesday" is fine with an
    accomplishment. -/
def by_deadline : TemporalExprEntry :=
  { form := "by"
  , complementType := .nominal
  , order := .by_
  , licensesNPI := false
  , defaultReading := .beforeStart
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

-- ============================================================================
-- § 4b: Additional Connective Entries (@cite{heinamaki-1974})
-- ============================================================================

/-- *as long as*: temporal containment, synonymous with *while*.
    "I'll stay as long as you need me." Same ∀-containment semantics as *while*. Carries an additional conditional flavor in many
    uses ("As long as it rains, we stay inside"), but truth-conditionally
    equivalent to *while*. -/
def asLongAs : TemporalExprEntry :=
  { form := "as long as"
  , complementType := .clausal
  , order := .while_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *whenever*: universally quantified temporal overlap.
    "Whenever it rains, I carry an umbrella." Every occasion of B has a
    corresponding occurrence of A. Truth-conditionally ∀t∈B, t∈A (= while
    with arguments swapped). Implies habitual/generic interpretation.
    Veridical for both clauses (given nonempty B). -/
def whenever_conn : TemporalExprEntry :=
  { form := "whenever"
  , complementType := .clausal
  , order := .whenever
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *as soon as*: strengthened *after* with temporal proximity implicature. "He left as soon as she arrived." Truth-conditionally
    equivalent to *after* (∃∃ ordering), but pragmatically implies minimal
    temporal gap between the two events. Veridical complement. -/
def asSoonAs : TemporalExprEntry :=
  { form := "as soon as"
  , complementType := .clausal
  , order := .after
  , licensesNPI := false
  , defaultReading := .afterFinish
  , coercedReading := none
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

-- ============================================================================
-- § 5: Entry Lists
-- ============================================================================

def allEntries : List TemporalExprEntry :=
  [before_, after_, while_conn, until_, when_conn, since_conn, till_conn,
   asLongAs, whenever_conn, asSoonAs, within_, at_punct, by_deadline]

/-- Connective entries only (clausal complement). -/
def allConnectives : List TemporalExprEntry :=
  allEntries.filter (·.complementType == .clausal)

/-- Modifier entries only (nominal complement). -/
def allModifiers : List TemporalExprEntry :=
  allEntries.filter (·.complementType == .nominal)

-- ============================================================================
-- § 6: Form Agreement with FunctionWords
-- ============================================================================

open Fragments.English.FunctionWords in
theorem before_form_agrees : before_.form = FunctionWords.before.form := rfl

open Fragments.English.FunctionWords in
theorem after_form_agrees : after_.form = FunctionWords.after.form := rfl

-- ============================================================================
-- § 7: Coverage — Every TemporalOrder Has an Entry
-- ============================================================================

/-- All eight temporal orders in the enum have corresponding entries. -/
theorem all_orders_covered :
    before_.order = .before ∧
    after_.order = .after ∧
    while_conn.order = .while_ ∧
    until_.order = .until_ ∧
    when_conn.order = .when_ ∧
    since_conn.order = .since_ ∧
    by_deadline.order = .by_ ∧
    whenever_conn.order = .whenever :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Veridicality pattern: *before* is the only non-veridical expression.
    This holds across both connectives and modifiers. -/
theorem only_before_nonveridical :
    before_.complementVeridical = false ∧
    after_.complementVeridical = true ∧
    while_conn.complementVeridical = true ∧
    until_.complementVeridical = true ∧
    when_conn.complementVeridical = true ∧
    since_conn.complementVeridical = true ∧
    till_conn.complementVeridical = true ∧
    asLongAs.complementVeridical = true ∧
    whenever_conn.complementVeridical = true ∧
    asSoonAs.complementVeridical = true ∧
    by_deadline.complementVeridical = true ∧
    within_.complementVeridical = true ∧
    at_punct.complementVeridical = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- NPI licensing pattern: only *before*, *until*, and *till* license NPIs.
    For *before*, this follows from downward entailment of the complement.
    For *until*/*till*, this arises in the punctual (*not...until*) construction,
    which is truth-conditionally ¬*before*.
    No modifiers license NPIs. -/
theorem npi_pattern :
    before_.licensesNPI = true ∧
    until_.licensesNPI = true ∧
    till_conn.licensesNPI = true ∧
    after_.licensesNPI = false ∧
    while_conn.licensesNPI = false ∧
    when_conn.licensesNPI = false ∧
    since_conn.licensesNPI = false ∧
    asLongAs.licensesNPI = false ∧
    whenever_conn.licensesNPI = false ∧
    asSoonAs.licensesNPI = false ∧
    by_deadline.licensesNPI = false ∧
    within_.licensesNPI = false ∧
    at_punct.licensesNPI = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- *Till* and *until* agree on all semantic properties. -/
theorem till_matches_until :
    till_conn.order = until_.order ∧
    till_conn.licensesNPI = until_.licensesNPI ∧
    till_conn.defaultReading = until_.defaultReading ∧
    till_conn.complementVeridical = until_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The complement-type field correctly classifies all entries. -/
theorem complement_type_classification :
    before_.complementType = .clausal ∧
    after_.complementType = .clausal ∧
    while_conn.complementType = .clausal ∧
    until_.complementType = .clausal ∧
    when_conn.complementType = .clausal ∧
    since_conn.complementType = .clausal ∧
    till_conn.complementType = .clausal ∧
    by_deadline.complementType = .nominal ∧
    within_.complementType = .nominal ∧
    at_punct.complementType = .nominal :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- *As long as* agrees with *while* on all semantic properties. -/
theorem asLongAs_matches_while :
    asLongAs.order = while_conn.order ∧
    asLongAs.licensesNPI = while_conn.licensesNPI ∧
    asLongAs.defaultReading = while_conn.defaultReading ∧
    asLongAs.complementVeridical = while_conn.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- *As soon as* agrees with *after* on ordering and veridicality. -/
theorem asSoonAs_matches_after :
    asSoonAs.order = after_.order ∧
    asSoonAs.licensesNPI = after_.licensesNPI ∧
    asSoonAs.defaultReading = after_.defaultReading ∧
    asSoonAs.complementVeridical = after_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Duration Adverbials — Sibling Structure
-- ============================================================================

/-- Sub-class discriminator for duration adverbials.

    The four English duration adverbials carve out distinct semantic
    profiles even though they share the same schema:

    - `telicCompletion` (*in three hours*): measures the runtime of a telic
      event from onset to telos.
    - `atelicDurative` (*for three hours*): measures the runtime of an
      atelic event.
    - `pastOffset` (*three days ago*): postposed deictic offset from the
      utterance time into the past.
    - `npiGap` (*in years* under negation+perfect): measures the gap
      between the right boundary of the perfect time span and the most
      recent witnessing event. Strong NPI. -/
inductive DurationKind where
  | telicCompletion
  | atelicDurative
  | pastOffset
  | npiGap
  deriving DecidableEq, Repr, Inhabited

/-- Lexical entry for a duration / measure adverbial.

    Schema is consensus typological metadata only. Theory-specific
    machinery (PTS classification, Rouillard's E-TIA / G-TIA labels,
    Iatridou-Zeijlstra 2021's domain-widening profile) lives as
    partial projections from this structure in the relevant Theory
    or Studies file (mathlib-style pattern: same discipline as
    `QuantifierEntry → gqDenotation/ptMeaning/gqtMeaning` in
    `Determiners.lean`).

    Cross-references for *in years* (the NPI-gap entry):
    - `Theories/Semantics/Tense/PTS.lean :: inYears` — Iatridou-Zeijlstra
      2021 boundary-adverbial projection (PTS-tradition apparatus).
    - `Fragments/English/PolarityItems.lean :: inYears` — polarity-theoretic
      projection (Israel 1996 / 2001 scalar model).
    Consolidating the three views into a single canonical entry plus
    derived projections is a follow-up refactor. -/
structure DurationExprEntry where
  /-- Surface form (e.g., `"in"`, `"for"`, `"ago"`) -/
  form : String
  /-- Sub-class of duration adverbial -/
  kind : DurationKind
  /-- True for postpositions (*ago*); most duration adverbials are prepositions. -/
  isPostposition : Bool := false
  /-- Aspectual classes the adverbial selects for at the VP it modifies
      (Vendler-level consensus; @cite{vendler-1957}). Empty list = no
      restriction; `[.telic]` = requires accomplishment/achievement;
      `[.atelic]` = requires state/activity. -/
  vendlerSelection : List Telicity := []
  /-- Iatridou-Anagnostopoulou-Izvorski 2001 typological classification.
      `durative` = pins the left boundary of the perfect time span;
      `inclusive` = leaves the LB free. `none` for entries that don't
      participate in the perfect-time-span typology. -/
  iaiClassification : Option AdverbialType := none
  /-- Is this entry itself a polarity-sensitive item? -/
  polaritySensitive : Bool := false
  /-- Polarity-item type if `polaritySensitive` (Zwarts 1998 strong/weak).
      Strong NPIs (*in years*) require anti-additive licensors; weak NPIs
      require any DE licensor. -/
  polarityType : Option PolarityType := none
  /-- Distributional licensing flags (theory-neutral surface facts). -/
  requiresPerfect : Bool := false
  requiresNegation : Bool := false
  deriving Repr, BEq

-- ============================================================================
-- § 9: Duration Adverbial Entries
-- ============================================================================

/-- *in three days* (telic-completion): "Mary wrote a paper in three days".
    Selects telic VPs (accomplishment / achievement). Not an NPI.
    IAI 2001 classification: inclusive (leaves PTS LB free). -/
def inTelic : DurationExprEntry :=
  { form := "in"
    kind := .telicCompletion
    vendlerSelection := [.telic]
    iaiClassification := some .inclusive }

/-- *in years* / *in days* / *in months* (NPI-gap reading):
    "Mary hasn't been sick in years". Strong NPI. Requires the perfect
    and negative polarity. IAI 2001 classification: durative (pins PTS LB).

    Same surface preposition as `inTelic`; the two readings are
    distinguished by syntactic position and licensing environment. -/
def inGap : DurationExprEntry :=
  { form := "in"
    kind := .npiGap
    iaiClassification := some .durative
    polaritySensitive := true
    polarityType := some .npiStrong
    requiresPerfect := true
    requiresNegation := true }

/-- *for three hours* (atelic-durative): "Mary was sick for three hours".
    Selects atelic VPs (state / activity). IAI 2001 classification:
    durative when combined with the perfect (pins PTS LB by specifying
    duration). -/
def forDur : DurationExprEntry :=
  { form := "for"
    kind := .atelicDurative
    vendlerSelection := [.atelic]
    iaiClassification := some .durative }

/-- *three days ago*: postposed deictic past offset.
    The lone English postposition. Combines with a measure phrase to
    locate an event a specified duration prior to the utterance time.
    Not an NPI; does not require the perfect. -/
def ago : DurationExprEntry :=
  { form := "ago"
    kind := .pastOffset
    isPostposition := true }

/-- All duration adverbial entries. -/
def allDurationEntries : List DurationExprEntry := [inTelic, inGap, forDur, ago]

-- ============================================================================
-- § 10: Duration Adverbial Theorems
-- ============================================================================

/-- Both *in*-readings share the surface preposition. -/
theorem in_readings_share_form : inTelic.form = inGap.form := rfl

/-- The two *in*-readings are distinguished by `kind`. -/
theorem in_readings_distinct_kind : inTelic.kind ≠ inGap.kind := by decide

/-- Surface form of telic *in* agrees with the canonical preposition entry. -/
theorem inTelic_form_agrees :
    inTelic.form = Fragments.English.FunctionWords.in_.form := rfl

/-- Surface form of NPI-gap *in* agrees with the canonical preposition entry. -/
theorem inGap_form_agrees :
    inGap.form = Fragments.English.FunctionWords.in_.form := rfl

/-- *Ago* is the only postposition among duration adverbials. -/
theorem ago_unique_postposition :
    ago.isPostposition = true ∧
    inTelic.isPostposition = false ∧
    inGap.isPostposition = false ∧
    forDur.isPostposition = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Only the NPI-gap reading is polarity-sensitive. -/
theorem only_inGap_polarity_sensitive :
    inGap.polaritySensitive = true ∧
    inTelic.polaritySensitive = false ∧
    forDur.polaritySensitive = false ∧
    ago.polaritySensitive = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Telicity-selection pattern: telic *in* selects telic VPs;
    atelic *for* selects atelic VPs; the gap reading and *ago*
    have no Vendler restriction. -/
theorem vendler_selection_pattern :
    inTelic.vendlerSelection = [.telic] ∧
    forDur.vendlerSelection = [.atelic] ∧
    inGap.vendlerSelection = [] ∧
    ago.vendlerSelection = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- IAI 2001 durative-vs-inclusive classification:
    *for* and the NPI-gap *in* pin the PTS left boundary (durative);
    telic *in* leaves it free (inclusive); *ago* is outside the
    PTS typology entirely. -/
theorem iai_classification_pattern :
    inTelic.iaiClassification = some .inclusive ∧
    inGap.iaiClassification = some .durative ∧
    forDur.iaiClassification = some .durative ∧
    ago.iaiClassification = none :=
  ⟨rfl, rfl, rfl, rfl⟩

end Fragments.English.TemporalExpressions
