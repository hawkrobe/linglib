import Linglib.Phenomena.ArgumentStructure.Typology
import Linglib.Theories.Semantics.Lexical.Verb.EntailmentProfile

/-!
# Siloni (2012): Reciprocal Verbs and Symmetry

@cite{siloni-2012} @cite{siloni-2008}

Natural Language and Linguistic Theory 30(1): 261–320.

Beyond periphrastic reciprocals (*each other*), languages have reciprocal
*verbs* — predicates that express reciprocity without an anaphoric object.
These split into two types based on where reciprocalization applies:

- **Lexical** (Hebrew *hitnašek*, English intransitive *kiss*): formed in
  the lexicon via θ-role bundling. Produces symmetric verbs whose
  reciprocity involves a singular atomic event.
- **Syntactic** (French *s'embrasser*, Czech *se políbit*): formed in
  the syntax via a clitic (*se*). Reciprocity involves accumulation of
  sub-events; the operation is productive.

Nine empirical properties cluster along this divide, verified across ten
languages (Hebrew, Russian, Hungarian, English, French, Italian, Spanish,
Czech, Romanian, Serbo-Croatian). Both types disallow the "I" reading of
embedded reciprocals — because both associate the subject with two
θ-roles, blocking the sole-role requirement for distribution under
embedding.

## Connections

- `RecipFormation` from `Typology.lean` — extended with nine predicted
  properties and per-language verification
- `EntailmentProfile` — used to define θ-role bundling
- `VerbDistributivity` in `Events/StratifiedReference.lean` — the
  `meet_agent_not_sdr` axiom captures the same property: symmetric
  verbs denote singular events that do not distribute over atomic agents
-/

namespace Phenomena.ArgumentStructure.Studies.Siloni2012

open Phenomena.ArgumentStructure.Typology
open Semantics.Lexical.Verb.EntailmentProfile (EntailmentProfile)

-- ════════════════════════════════════════════════════
-- § 1. Three-Way Reciprocal Classification (§2.4)
-- ════════════════════════════════════════════════════

/-- The three classes of reciprocal constructions.

    Class (i): periphrastic — reciprocal anaphor in object position
    (*each other*, *l'un l'autre*). Subject bears one θ-role.

    Class (ii): lexical reciprocal verb — formed in the lexicon by
    θ-role bundling. Subject bears a complex [Agent-Theme] role.
    The verb is symmetric: reciprocity involves a singular atomic event.

    Class (iii): syntactic reciprocal verb — formed in the syntax by
    a clitic (*se*). Subject bears two θ-roles via parasitic assignment.
    Reciprocity involves accumulation of sub-events. -/
inductive RecipClass where
  | periphrastic
  | lexicalVerb
  | syntacticVerb
  deriving DecidableEq, BEq, Repr

def toRecipClass : RecipFormation → RecipClass
  | .lexical  => .lexicalVerb
  | .syntactic => .syntacticVerb

/-- Number of θ-roles associated with the subject.
    Periphrastic: subject = Agent only (Theme on anaphoric object).
    Reciprocal verbs: subject = Agent + Theme (bundled or parasitic). -/
def RecipClass.subjectRoleCount : RecipClass → Nat
  | .periphrastic  => 1
  | .lexicalVerb   => 2
  | .syntacticVerb => 2

/-- Whether the sub-event reading is available (§2.2).
    Periphrastic and syntactic reciprocals build reciprocity from
    sub-events. Lexical reciprocal verbs (symmetric verbs) denote
    a singular atomic event — sub-events are inaccessible. -/
def RecipClass.allowsSubEventReading : RecipClass → Bool
  | .periphrastic  => true
  | .lexicalVerb   => false
  | .syntacticVerb => true

-- ════════════════════════════════════════════════════
-- § 2. Nine-Property Cluster (§§2–7, §8)
-- ════════════════════════════════════════════════════

/-- Nine empirical properties that systematically distinguish lexical
    from syntactic reciprocal verbs. Each `Bool` indicates whether the
    property holds for that formation type. -/
structure PropertyCluster where
  /-- (i) Reciprocity involves a singular atomic event.
      Diagnostic: count adverbials (*five times*) yield N mutual
      events, not 2N directional sub-events (§2.2–2.3). -/
  singularEvent : Bool
  /-- (ii) The reciprocalization operation is productive — applies
      freely to transitive verbs (§3.5, §5). -/
  productive : Bool
  /-- (iii) ECM reciprocal verbs are possible — reciprocalization
      spans a clause boundary (§5.2). -/
  ecmReciprocals : Bool
  /-- (iv) Can be formed from a frozen lexical entry (one without
      a transitive alternate in the vocabulary) (§5.3). -/
  frozenInput : Bool
  /-- (v) The reciprocal verb can undergo semantic drift — acquire
      a meaning not shared by the transitive alternate (§5.3). -/
  semanticDrift : Bool
  /-- (vi) Can retain accusative case when the dative (not accusative)
      argument is suppressed by reciprocalization (§5.1). -/
  retainsAccOnDativeSuppression : Bool
  /-- (vii) Can derive reciprocal event nominals (§6).
      Exception: Czech allows reciprocal event nominals despite a
      syntactic setting, because Czech nominalization is itself a
      syntactic operation that can access syntactic reciprocal outputs
      (Hron 2005). -/
  eventNominals : Bool
  /-- (viii) Can head phrasal idioms unavailable for the transitive
      alternate (§5.3). -/
  phrasalIdioms : Bool
  /-- (ix) Allows the discontinuous reciprocal construction —
      subject + comitative "with"-phrase (§7). -/
  discontinuous : Bool
  deriving DecidableEq, BEq, Repr

/-- Predicted cluster for lexically-formed reciprocal verbs.
    Symmetric verbs: closed class, singular event, can be frozen or
    drifted, derive event nominals, head idioms, license discontinuity.
    Cannot form ECM reciprocals or retain accusative on dative targets. -/
def lexicalProperties : PropertyCluster :=
  { singularEvent                := true
  , productive                   := false
  , ecmReciprocals               := false
  , frozenInput                  := true
  , semanticDrift                := true
  , retainsAccOnDativeSuppression := false
  , eventNominals                := true
  , phrasalIdioms                := true
  , discontinuous                := true }

/-- Predicted cluster for syntactically-formed reciprocal verbs.
    Productive, allow ECM and sub-events, can retain accusative on
    dative targets. Cannot be frozen, drift, head idioms, derive
    event nominals, or license discontinuity. -/
def syntacticProperties : PropertyCluster :=
  { singularEvent                := false
  , productive                   := true
  , ecmReciprocals               := true
  , frozenInput                  := false
  , semanticDrift                := false
  , retainsAccOnDativeSuppression := true
  , eventNominals                := false
  , phrasalIdioms                := false
  , discontinuous                := false }

/-- Derive the predicted property cluster from formation locus. -/
def predictedProperties : RecipFormation → PropertyCluster
  | .lexical  => lexicalProperties
  | .syntactic => syntacticProperties

/-- The two clusters are perfectly complementary: every property that
    holds for lexical reciprocal verbs fails for syntactic ones, and
    vice versa. This is the central empirical finding of the paper. -/
theorem properties_complementary :
    lexicalProperties.singularEvent = !syntacticProperties.singularEvent ∧
    lexicalProperties.productive = !syntacticProperties.productive ∧
    lexicalProperties.ecmReciprocals = !syntacticProperties.ecmReciprocals ∧
    lexicalProperties.frozenInput = !syntacticProperties.frozenInput ∧
    lexicalProperties.semanticDrift = !syntacticProperties.semanticDrift ∧
    lexicalProperties.retainsAccOnDativeSuppression =
      !syntacticProperties.retainsAccOnDativeSuppression ∧
    lexicalProperties.eventNominals = !syntacticProperties.eventNominals ∧
    lexicalProperties.phrasalIdioms = !syntacticProperties.phrasalIdioms ∧
    lexicalProperties.discontinuous = !syntacticProperties.discontinuous :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Symmetric Verbs (§2.3, §4.1)
-- ════════════════════════════════════════════════════

/-- Lexical reciprocal verbs are symmetric verbs: their reciprocity
    involves a singular atomic event in which both participants are
    identically involved (§2.3). Intransitive *kiss* and *collide*
    are symmetric — "John and Mary kissed" denotes one event of
    mutual kissing, not two directional sub-events.

    The `VerbDistributivity` class in `Events/StratifiedReference.lean`
    axiomatizes the same property: *meet* has `¬ SDR_univ agentOf meet`
    — it does not distribute over atomic agents, because the event is
    necessarily collective/atomic. -/
def isSymmetricVerb : RecipFormation → Bool
  | .lexical  => true
  | .syntactic => false

theorem symmetric_iff_singular :
    ∀ f : RecipFormation,
      isSymmetricVerb f = (predictedProperties f).singularEvent := by
  intro f; cases f <;> rfl

-- ════════════════════════════════════════════════════
-- § 4. θ-Role Bundling (§4.1)
-- ════════════════════════════════════════════════════

/-- A bundled θ-role: two entailment profiles merged into a single
    complex role assigned to one argument. Lexical reciprocalization
    bundles the external (agent-like) and internal (theme-like) roles
    of a transitive verb:

      V(ACC) [θ_i] [θ_j]  →  V_SYM [θ_i · θ_j]

    The subject of the resulting symmetric verb bears both the agent
    and theme entailments of the base transitive. -/
structure BundledRole where
  /-- The external (agent-like) component -/
  external : EntailmentProfile
  /-- The internal (theme-like) component -/
  internal : EntailmentProfile
  deriving DecidableEq, BEq, Repr

/-- Lexical reciprocalization: bundle a transitive verb's two roles. -/
def reciprocalBundle (subjectProfile objectProfile : EntailmentProfile) :
    BundledRole :=
  ⟨subjectProfile, objectProfile⟩

/-- A bundled role carries exactly two component profiles — this is
    what makes the subject of a reciprocal verb bear both Agent and
    Theme properties (depictive adjective case in Czech §3.1,
    comparative ellipsis §3.2). -/
def BundledRole.componentCount (_b : BundledRole) : Nat := 2

-- ════════════════════════════════════════════════════
-- § 5. The "I" Reading (§2.1, §4.3)
-- ════════════════════════════════════════════════════

/-! The "I" reading of embedded reciprocals (@cite{higginbotham-1980}):

    "John and Paul said they defeated each other in the final."

    (we) John and Paul said: "we defeated each other."
    (I)  John said he defeated Paul, and Paul said he defeated John.

    The "I" reading requires TWO conditions (§4.3, p. 287):
    (1) the embedded verb allows the sub-event reading, AND
    (2) the embedded subject is associated with exactly one θ-role.

    The puzzle: syntactic reciprocal verbs satisfy (1) — they DO have
    the sub-event reading — yet still lack the "I" reading. Condition
    (1) is necessary but not sufficient. The resolution: both types of
    reciprocal verb fail condition (2), because both associate the
    subject with two θ-roles (bundled or parasitic).

    Only periphrastic reciprocals satisfy both conditions: the sub-event
    reading is available (via the plural operator on *each other*), and
    the subject bears exactly one role (Agent). -/

/-- The "I" reading requires both sub-event availability AND a sole
    θ-role on the subject. -/
def RecipClass.allowsIReading (c : RecipClass) : Bool :=
  c.allowsSubEventReading && (c.subjectRoleCount == 1)

/-- The "I" reading is available iff the construction is periphrastic.
    - Periphrastic: sub-events ✓, sole role ✓ → "I" reading ✓
    - Lexical verb:  sub-events ✗, sole role ✗ → "I" reading ✗
    - Syntactic verb: sub-events ✓, sole role ✗ → "I" reading ✗

    The syntactic case is the puzzle: sub-events are present (condition 1
    met) but the sole-role requirement fails (condition 2 unmet). -/
theorem I_reading_iff_periphrastic :
    ∀ c : RecipClass, c.allowsIReading = (c == .periphrastic) := by
  intro c; cases c <;> native_decide

-- ════════════════════════════════════════════════════
-- § 6. Cross-Linguistic Data (§2.4, §5, §7)
-- ════════════════════════════════════════════════════

/-- Per-language formation locus from the ten-language sample. -/
structure LangRecipVerb where
  language : String
  iso : String
  formation : RecipFormation
  deriving DecidableEq, BEq, Repr

-- Class (ii): lexical reciprocal verbs (symmetric).
-- Note: `formation` here classifies the reciprocal VERB mechanism,
-- not the primary reciprocal strategy. English's primary strategy is
-- periphrastic (*each other*), but its reciprocal verbs (intransitive
-- *kiss*, *meet*, *collide*) are lexical — symmetric verbs formed in
-- the lexicon. This is why `rp_english.formation` in Typology.lean is
-- `none` (primary strategy is not verb formation) while we classify
-- English as `.lexical` (its reciprocal verbs, when they exist, are
-- lexically formed).
def hebrew    : LangRecipVerb := ⟨"Hebrew",    "heb", .lexical⟩
def russian   : LangRecipVerb := ⟨"Russian",   "rus", .lexical⟩
def hungarian : LangRecipVerb := ⟨"Hungarian", "hun", .lexical⟩
def english   : LangRecipVerb := ⟨"English",   "eng", .lexical⟩

-- Class (iii): syntactic reciprocal verbs (clitic se/si)
def french        : LangRecipVerb := ⟨"French",         "fra", .syntactic⟩
def italian       : LangRecipVerb := ⟨"Italian",         "ita", .syntactic⟩
def spanish       : LangRecipVerb := ⟨"Spanish",         "spa", .syntactic⟩
def czech         : LangRecipVerb := ⟨"Czech",           "ces", .syntactic⟩
def romanian      : LangRecipVerb := ⟨"Romanian",        "ron", .syntactic⟩
def serboCroatian : LangRecipVerb := ⟨"Serbo-Croatian",  "hbs", .syntactic⟩

def siloniSample : List LangRecipVerb :=
  [hebrew, russian, hungarian, english,
   french, italian, spanish, czech, romanian, serboCroatian]

theorem sample_size : siloniSample.length = 10 := by native_decide

theorem lexical_count :
    (siloniSample.filter (·.formation == .lexical)).length = 4 := by
  native_decide

theorem syntactic_count :
    (siloniSample.filter (·.formation == .syntactic)).length = 6 := by
  native_decide

/-- All lexical-formation languages produce symmetric verbs. -/
theorem lexical_are_symmetric :
    (siloniSample.filter (·.formation == .lexical)).all
      (fun l => isSymmetricVerb l.formation) := by native_decide

/-- All syntactic-formation languages produce non-symmetric verbs. -/
theorem syntactic_not_symmetric :
    (siloniSample.filter (·.formation == .syntactic)).all
      (fun l => !isSymmetricVerb l.formation) := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. Derivation: Formation Locus → "I" Reading (§3.5 → §4.3)
-- ════════════════════════════════════════════════════

/-! The paper's core argument is a derivation chain, not a conjunction
    of independent facts. Formation locus determines interpretive
    possibilities step by step.

    Generalization (29) from §3.5: "Plural events are not part of the
    lexicon's inventory." Since the lexicon has no access to plural
    operators, lexical operations cannot produce plural events. This
    forces lexical reciprocals to be symmetric verbs (singular events),
    which in turn blocks the sub-event reading.

    Both verb types converge on "no 'I' reading" but via different
    derivation paths:
    - Lexical:   singular event → no sub-events → condition 1 fails
    - Syntactic: sub-events present, BUT dual role → condition 2 fails

    Cross-module connections:
    - `meetProfile.agentSDR = false` in Champollion2017: same insight
    - `meet_agent_not_sdr` in StratifiedReference: axiomatizes it -/

/-- Step 1: Both reciprocal verb types give the subject two θ-roles
    (lexical via bundling §4.1, syntactic via parasitic assignment §4.2). -/
theorem recip_verb_dual_role (f : RecipFormation) :
    (toRecipClass f).subjectRoleCount = 2 := by
  cases f <;> rfl

/-- Step 2: Singular-event verbs lack the sub-event reading (§2.2–2.3).
    Bridges `PropertyCluster.singularEvent` to
    `RecipClass.allowsSubEventReading`. -/
theorem singular_event_no_subevents (f : RecipFormation)
    (h : (predictedProperties f).singularEvent = true) :
    (toRecipClass f).allowsSubEventReading = false := by
  cases f
  · rfl
  · exact absurd h (by decide)

/-- Step 3a: Sub-event availability is NECESSARY for the "I" reading
    (condition 1 of §4.3). Blocks via the first conjunct of `&&`. -/
theorem subevents_necessary_for_I (c : RecipClass)
    (h : c.allowsSubEventReading = false) :
    c.allowsIReading = false := by
  simp [RecipClass.allowsIReading, h]

/-- Step 3b: A sole θ-role on the subject is NECESSARY for the "I"
    reading (condition 2 of §4.3). Blocks via the second conjunct. -/
theorem sole_role_necessary_for_I (c : RecipClass)
    (h : c.subjectRoleCount ≠ 1) :
    c.allowsIReading = false := by
  cases c <;> simp_all [RecipClass.allowsIReading,
    RecipClass.allowsSubEventReading, RecipClass.subjectRoleCount]

/-- Lexical derivation (§3.5 → §2.2 → §4.3):
    singular event → no sub-events → condition 1 fails → no "I" reading. -/
theorem lexical_no_I_reading :
    (toRecipClass .lexical).allowsIReading = false := by
  apply subevents_necessary_for_I
  apply singular_event_no_subevents
  rfl

/-- Syntactic derivation (§4.2 → §4.3):
    dual role → condition 2 fails → no "I" reading.

    This resolves the PUZZLE: syntactic reciprocals HAVE sub-events
    (condition 1 met) but LACK the sole role (condition 2 unmet). -/
theorem syntactic_no_I_reading :
    (toRecipClass .syntactic).allowsIReading = false := by
  apply sole_role_necessary_for_I
  decide

/-- Both paths converge: neither verb type allows the "I" reading. -/
theorem no_I_reading_either_formation (f : RecipFormation) :
    (toRecipClass f).allowsIReading = false := by
  cases f
  · exact lexical_no_I_reading
  · exact syntactic_no_I_reading

-- ════════════════════════════════════════════════════
-- § 8. Verification Against Typology.lean
-- ════════════════════════════════════════════════════

/-- Hungarian formation agrees with Typology.lean. -/
theorem hungarian_agrees :
    rp_hungarian.formation = some hungarian.formation := by native_decide

/-- French formation agrees with Typology.lean. -/
theorem french_agrees :
    rp_french.formation = some french.formation := by native_decide

/-- Czech formation agrees with Typology.lean. -/
theorem czech_agrees :
    rp_czech.formation = some czech.formation := by native_decide

/-- Swahili is classified as lexical in Typology.lean (Nordlinger 2023).
    Siloni (2012) does not discuss Swahili directly, but the prediction
    is consistent: Swahili has verb-marked reciprocals (-ana) that
    license discontinuous constructions — a lexical property. -/
theorem swahili_consistent :
    rp_swahili.formation = some RecipFormation.lexical := by native_decide

/-- Greek is classified as lexical in Typology.lean.
    Consistent: Greek allows discontinuous reciprocals with *me*. -/
theorem greek_consistent :
    rp_greek.formation = some RecipFormation.lexical := by native_decide

/-- The discontinuity prediction from `predictedProperties` agrees
    with `RecipFormation.allowsDiscontinuous` in Typology.lean. -/
theorem discontinuity_bridge (f : RecipFormation) :
    (predictedProperties f).discontinuous = f.allowsDiscontinuous := by
  cases f <;> rfl

end Phenomena.ArgumentStructure.Studies.Siloni2012
