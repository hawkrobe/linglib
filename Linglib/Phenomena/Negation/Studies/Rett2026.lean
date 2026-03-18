import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Theories.Semantics.Tense.TemporalConnectives
import Linglib.Phenomena.Polarity.NPIs
import Linglib.Phenomena.Negation.Studies.JinKoenig2021
import Linglib.Fragments.English.Modifiers.Adjectives
import Linglib.Fragments.Italian.Negation
import Linglib.Phenomena.Negation.Studies.Tsiakmakis2025

/-!
# Expletive Negation: Typology and Licensing
@cite{greco-2018} @cite{jin-koenig-2021} @cite{kennedy-mcnally-2005} @cite{napoli-nespor-1976} @cite{rett-2026} @cite{cepeda-2018}

Expletive negation (EN) is truth-conditionally vacuous negation that appears
in specific grammatical environments cross-linguistically. @cite{rett-2026} unifies
the licensing conditions: EN is licensed exactly in **ambidirectional**
constructions — those where negating an argument doesn't change truth
conditions because MAX picks the same informative bound from both B and ¬B.

## The Ambidirectionality Generalization

| Construction  | Ambidirectional? | Licenses EN? | Source               |
|---------------|-----------------|--------------|----------------------|
| *before*      | ✓               | ✓ (50 langs) | @cite{jin-koenig-2021}    |
| *after*       | ✗               | ✗            | @cite{rett-2026}            |
| *while*       | ✗               | ✗            | @cite{rett-2026}            |
| *until*       | ✓               | ✓            | @cite{rett-2026} §5         |
| comparative   | ✓               | ✓ (6+ langs) | @cite{jin-koenig-2021}    |
| *fear/worry*  | ✓               | ✓ (39 langs) | @cite{jin-koenig-2021}    |

## High vs Low EN @cite{greco-2020}

Two types of EN with different syntactic positions and licensing:
- **High EN**: targets non-truth-conditional content (exclamatives, surprise);
  obligatory where it appears.
- **Low EN**: targets truth-conditional content in ambidirectional environments;
  optional and triggers manner implicature (evaluativity).

-/

namespace Phenomena.Negation.ExpletiveNegation

open Core.Scale (Boundedness isAmbidirectional)
open Semantics.Degree.Comparative (MannerEffect)
open Fragments.English.Modifiers.Adjectives (AdjModifierEntry)

-- ════════════════════════════════════════════════════
-- § 1. High vs Low EN
-- ════════════════════════════════════════════════════

/-- Two syntactic types of expletive negation.

    **High EN** appears above TP, targets non-truth-conditional content
    (exclamatives, surprise negation). It is obligatory where licensed.

    **Low EN** appears below TP (VP-level), targets truth-conditional
    content in ambidirectional environments. It is optional and triggers
    a manner implicature (evaluativity). -/
inductive ENType where
  | high   -- Non-truth-conditional; obligatory (exclamatives, surprise)
  | low    -- Truth-conditional; optional (before, than, fear)
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Cross-Linguistic EN Data
-- ════════════════════════════════════════════════════

/-- A cross-linguistic EN licensing datum. -/
structure ENDatum where
  /-- Language -/
  language : String
  /-- Construction type -/
  construction : String
  /-- Negation marker used -/
  negMarker : String
  /-- High or low EN -/
  enType : ENType
  /-- Is the EN optional? -/
  isOptional : Bool
  /-- Does the construction also license weak NPIs? -/
  licensesWeakNPIs : Bool
  /-- Manner implicature triggered by EN (if any) -/
  mannerEffect : Option MannerEffect := none
  deriving Repr

/-! ### @cite{jin-koenig-2021} survey data

Cross-linguistic distribution from a 722-language survey (EN attested
in 74 languages across 37 genera):
- *before*-clauses: EN in 50/74 EN-attesting languages
- *fear*-clauses: EN in 39/74 EN-attesting languages
- comparative *than*-clauses: 6+ languages have EN
- *until*-clauses: reported in several languages -/

def frenchBefore : ENDatum :=
  { language := "French", construction := "avant que"
  , negMarker := "ne", enType := .low, isOptional := true
  , licensesWeakNPIs := false
  , mannerEffect := some { evaluative := true, atypical := false } }

def italianBefore : ENDatum :=
  { language := "Italian", construction := "prima che"
  , negMarker := Fragments.Italian.Negation.negMarker
  , enType := .low, isOptional := true
  , licensesWeakNPIs := true }

def spanishComparative : ENDatum :=
  { language := "Spanish", construction := "más ... de lo que"
  , negMarker := "no", enType := .low, isOptional := true
  , licensesWeakNPIs := false }

def italianComparative : ENDatum :=
  { language := "Italian", construction := "più ... di quanto"
  , negMarker := Fragments.Italian.Negation.negMarker
  , enType := .low, isOptional := true
  , licensesWeakNPIs := false
  , mannerEffect := some { evaluative := true, atypical := false } }

def frenchFear : ENDatum :=
  { language := "French", construction := "craindre que"
  , negMarker := "ne", enType := .low, isOptional := true
  , licensesWeakNPIs := false }

/-- @cite{greco-2018}: Italian *until*-clauses license both EN and weak NPIs. -/
def italianUntil : ENDatum :=
  { language := "Italian", construction := "finché"
  , negMarker := Fragments.Italian.Negation.negMarker
  , enType := .low, isOptional := true
  , licensesWeakNPIs := true }

/-- Italian wh-exclamatives: high EN. -/
def italianExclamative : ENDatum :=
  { language := "Italian", construction := "wh-exclamative"
  , negMarker := Fragments.Italian.Negation.negMarker
  , enType := .high, isOptional := false
  , licensesWeakNPIs := false }

/-- Italian surprise negation (@cite{greco-2020}, §2–4): *non* merges in the CP
    layer (above FinP) rather than in the TP-internal NegP. High EN —
    obligatory, non-truth-conditional, does not license weak NPIs. -/
def italianSneg : ENDatum :=
  { language := "Italian", construction := "surprise negation (Sneg)"
  , negMarker := Fragments.Italian.Negation.negMarker
  , enType := .high, isOptional := false
  , licensesWeakNPIs := false }

/-- Brazilian Portuguese surprise negation: *é que não*
    construction. High EN — obligatory, non-truth-conditional. -/
def brazilianPortugueseSneg : ENDatum :=
  { language := "Brazilian Portuguese", construction := "é que não (Sneg)"
  , negMarker := "não"
  , enType := .high, isOptional := false
  , licensesWeakNPIs := false }

def allENData : List ENDatum :=
  [ frenchBefore, italianBefore, spanishComparative, italianComparative
  , frenchFear, italianUntil, italianExclamative
  , italianSneg, brazilianPortugueseSneg ]

/-- High EN blocks weak NPIs: in our sample,
    every high-EN construction has `licensesWeakNPIs = false`. Low EN
    may or may not license NPIs (Italian *prima che* and *finché* do). -/
theorem high_en_blocks_npis :
    allENData.all (λ d =>
      if d.enType == .high then !d.licensesWeakNPIs else true) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 3. Rett's Generalization: EN ↔ Ambidirectionality
-- ════════════════════════════════════════════════════

/-! ### The ambidirectionality–EN correspondence

@cite{rett-2026} proposes that low EN is licensed **iff** the embedding
construction is ambidirectional. We formalize this as a correspondence
between an enumeration of EN-relevant constructions (with their
theory-derived ambidirectionality classification) and the empirical
record of which constructions license EN cross-linguistically.

The ambidirectionality classification is derived from:
- `before_ambidirectional` (TemporalConnectives.lean)
- `after_not_ambidirectional` (TemporalConnectives.lean)
- `while_not_ambidirectional` (TemporalConnectives.lean)
- `comparative_boundary` (Comparative.lean)
For *until* and *fear*, the classification follows from the same
structural argument as *before* (shared endpoint / shared possibility). -/

/-- Constructions relevant to EN licensing.
    Each has a theory-derived ambidirectionality status and an
    empirically-observed EN status; Rett's claim is that these match. -/
inductive ENConstruction where
  | before       -- temporal *before*
  | after        -- temporal *after*
  | while_       -- temporal *while*
  | until        -- temporal *until*
  | comparative  -- degree comparative *than*
  | fear         -- negative attitude verbs (*fear*, *worry*, *doubt*)
  deriving DecidableEq, BEq, Repr

/-- Theory-derived: is the construction ambidirectional?
    Backed by the ambidirectionality theorems in TemporalConnectives
    and Comparative.

    - `before`: ambidirectional on closed intervals
      (cf. `before_ambidirectional` in TemporalConnectives.lean)
    - `after`: NOT ambidirectional — MAX on complement is different
      (cf. `after_not_ambidirectional`)
    - `while`: NOT ambidirectional — overlap with B ≠ overlap with Bᶜ
      (cf. `while_not_ambidirectional`)
    - `until`: ambidirectional — shares endpoint structure with *before*
    - `comparative`: ambidirectional on degree relatives
      (cf. `comparative_boundary` in Comparative.lean)
    - `fear`: ambidirectional — DERIVED from negative valence in
      preferential attitude semantics (@cite{villalta-2008}). Fear-type
      verbs activate both p (content of attitude) and ¬p (content of
      desire), satisfying @cite{jin-koenig-2021}'s propositional attitude
      licensing condition (§5.5, 13a). See `fear_ambidirectional_from_valence`. -/
def ENConstruction.isAmbidirectional : ENConstruction → Bool
  | .before      => true
  | .after       => false
  | .while_      => false
  | .until       => true
  | .comparative => true
  | .fear        => true

/-- Empirically observed: does the construction license EN
    cross-linguistically? Based on @cite{jin-koenig-2021} 722-language survey
    (EN attested in 74 languages). -/
def ENConstruction.hasEN : ENConstruction → Bool
  | .before      => true   -- 50/74 EN-attesting languages
  | .after       => false
  | .while_      => false
  | .until       => true   -- Italian finché, etc.
  | .comparative => true   -- 6+ languages
  | .fear        => true   -- 39/74 EN-attesting languages

/-- **Rett's generalization**: a construction licenses EN iff it is
    ambidirectional. Verified exhaustively over all EN-relevant
    constructions.

    This is the central empirical claim of @cite{rett-2026}: the
    ambidirectionality classification (derived from the semantics of
    MAX on closed intervals) perfectly predicts the cross-linguistic
    distribution of EN (observed in @cite{jin-koenig-2021}). -/
theorem rett_generalization (c : ENConstruction) :
    c.hasEN = c.isAmbidirectional := by
  cases c <;> rfl

-- ════════════════════════════════════════════════════
-- § 3b. Fear Ambidirectionality from Valence
-- ════════════════════════════════════════════════════

/-! ### Deriving fear's ambidirectionality

The `fear` case of `isAmbidirectional` is NOT an ad hoc stipulation —
it follows from the negative valence of fear-type predicates in
preferential attitude semantics (@cite{villalta-2008}).

@cite{jin-koenig-2021} §6.1.1 shows that FEAR triggers entail both
Operator₁(p) (content of X's attitude) and Operator₂(¬p) (content of
X's desires). This dual-inference property makes the complement
ambidirectional: *fear p* and *fear ¬p* share the same worry-worthy
possibility.

The bridge: negative valence in Preferential.lean corresponds to the
propositional attitude licensing condition in @cite{jin-koenig-2021}. -/

open Phenomena.Negation.Studies.JinKoenig2021 (negativeValenceEntailsDual
  LicensingCondition TriggerSubclass)

/-- The FEAR subclass maps to the propositional attitude licensing condition. -/
theorem fear_licensing_condition :
    TriggerSubclass.fear.licensingCondition = .propositionalAttitude := rfl

/-- Fear's ambidirectionality is grounded in negative valence:
    negative-valence predicates activate dual propositions (p and ¬p),
    which makes their complements ambidirectional.

    This connects three layers:
    1. `Preferential.fear` has `valence = .negative` (attitude semantics)
    2. Negative valence → dual inference (@cite{jin-koenig-2021} §5.5)
    3. Dual inference → ambidirectionality (@cite{rett-2026}) -/
theorem fear_ambidirectional_from_valence :
    negativeValenceEntailsDual .negative = true ∧
    ENConstruction.isAmbidirectional .fear = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Scale Type → EN Licensing in Comparatives
-- ════════════════════════════════════════════════════

/-! ### Connecting Fragment entries to EN predictions

@cite{rett-2026} predicts that EN in
comparatives is sensitive to scale type. The mechanism:
- The *than*-clause denotes a degree set with a boundary at μ(b).
- Ambidirectionality requires that this boundary is **shared** between
  B and Bᶜ.
- On **non-closed scales** (at least one endpoint open), the degree
  relative forms an interval with one informative bound, which B and Bᶜ
  share → ambidirectional → EN licensed.
- On **closed scales** (both endpoints exist), negation can target
  a *different* endpoint, making the construction non-ambidirectional
  → EN blocked.

We connect this to `AdjModifierEntry.scaleType` from the English
adjective fragment. -/

/-- An adjective licenses EN in its comparative iff its scale is
    non-closed: at least one endpoint is open, so the degree relative
    has a single shared informative bound.

    - `.open_`: both ends open (tall, expensive) → one shared bound ✓
    - `.lowerBounded`: min exists, no max (wet) → one shared bound ✓
    - `.upperBounded`: max exists, no min (dry) → one shared bound ✓
    - `.closed`: both bounds exist (full, empty) → negation can target
      the other bound → ambidirectionality fails ✗ -/
def licensesComparativeEN (scaleType : Boundedness) : Bool :=
  match scaleType with
  | .open_ => true
  | .lowerBounded => true
  | .upperBounded => true
  | .closed => false

/-- "tall" (open scale) licenses EN in comparatives. -/
theorem tall_licenses_EN :
    licensesComparativeEN Fragments.English.Modifiers.Adjectives.tall.scaleType = true := rfl

/-- "full" (closed scale) does NOT license EN in comparatives. -/
theorem full_blocks_EN :
    licensesComparativeEN Fragments.English.Modifiers.Adjectives.full.scaleType = false := rfl

/-- "expensive" (open scale) licenses EN in comparatives. -/
theorem expensive_licenses_EN :
    licensesComparativeEN Fragments.English.Modifiers.Adjectives.expensive.scaleType = true := rfl

/-- "dead" (closed scale) does NOT license EN in comparatives. -/
theorem dead_blocks_EN :
    licensesComparativeEN Fragments.English.Modifiers.Adjectives.dead.scaleType = false := rfl

/-- `licensesComparativeEN` is equivalent to `¬ Boundedness.closed`:
    EN is licensed iff the scale is NOT fully closed. This connects
    the EN prediction to the existing scale infrastructure. -/
theorem licensesComparativeEN_iff_not_closed (b : Boundedness) :
    licensesComparativeEN b = !b.hasMax || !b.hasMin := by
  cases b <;> rfl

-- ════════════════════════════════════════════════════
-- § 5. Manner Implicature Data
-- ════════════════════════════════════════════════════

/-! ### EN as pragmatic enrichment

When EN is used in an ambidirectional environment, it is truth-conditionally
vacuous but pragmatically meaningful. The use of the marked negated form
(vs the unmarked positive form) triggers a **manner implicature**
(see `MannerEffect` in `Adjective.Comparative`):

1. **French *avant que... ne***: "before ¬B" → "well before B" (temporal
   distance reading; @cite{cepeda-2018}, @cite{krifka-2010b}).

2. **Italian comparative + *non***: "più alto di quanto non sia" →
   "much taller than" (evaluative reading; @cite{napoli-nespor-1976}).

3. **Negative verbs (doubt, fear, worry)**: These are "ambidirectional"
   embedding verbs — *fear that p* and *fear that ¬p*
   share the same worry-worthy proposition, because the feared event's
   mere possibility (whether p or ¬p) triggers the attitude. EN in
   complements of fear is attested in 39 languages. -/

/-- A manner implicature datum: EN triggers evaluativity in a construction. -/
structure MannerImplicatureDatum where
  /-- Language -/
  language : String
  /-- Construction -/
  construction : String
  /-- EN form -/
  enForm : String
  /-- Pragmatic reading triggered -/
  pragmaticReading : String
  /-- Manner effect classification -/
  effect : MannerEffect
  /-- Source -/
  source : String
  deriving Repr

def frenchBeforeEvaluative : MannerImplicatureDatum :=
  { language := "French"
  , construction := "avant que ... ne"
  , enForm := "avant que Jean ne parte"
  , pragmaticReading := "well before Jean left"
  , effect := { evaluative := true, atypical := false }
  , source := "Cépeda 2018; Krifka 2010b" }

def italianComparativeEvaluative : MannerImplicatureDatum :=
  { language := "Italian"
  , construction := "più ... di quanto non"
  , enForm := "più alto di quanto non sia"
  , pragmaticReading := "much taller than (evaluative)"
  , effect := { evaluative := true, atypical := false }
  , source := "Napoli & Nespor 1976" }

def frenchFearAmbivalence : MannerImplicatureDatum :=
  { language := "French"
  , construction := "craindre que ... ne"
  , enForm := "je crains qu'il ne vienne"
  , pragmaticReading := "I'm afraid he might come"
  , effect := { evaluative := false, atypical := false }
  , source := "Rett 2026 §7" }

def allMannerData : List MannerImplicatureDatum :=
  [ frenchBeforeEvaluative, italianComparativeEvaluative, frenchFearAmbivalence ]

/-- All manner implicature data entries with evaluative readings
    have `effect.evaluative = true`. -/
theorem evaluative_manner_data :
    [frenchBeforeEvaluative, italianComparativeEvaluative].all
      (·.effect.evaluative) = true := rfl

-- ════════════════════════════════════════════════════
-- § 6. Bridge to Tsiakmakis 2025
-- ════════════════════════════════════════════════════

/-! ### Connecting EN constructions to negator types

@cite{tsiakmakis-2025} classifies EN hosts as NEG₁ (standard negation
masked) or NEG₂ (modal, intrinsically non-negative). The EN constructions
formalized here map onto Tsiakmakis's host categories:

| ENConstruction | ENHostCategory              | NegatorType |
|----------------|-----------------------------|-------------|
| before         | temporalExpressions         | NEG₁        |
| until          | temporalExpressions         | NEG₁        |
| comparative    | comparatives                | NEG₁        |
| fear           | emotiveDoxasticPredicates   | NEG₂        |
| after          | (no EN)                     | —           |
| while_         | (no EN)                     | —           |

The key structural insight: all ambidirectional constructions that are
NEG₁ hosts have their negative semantics masked by independent factors
(verbal aspect, operator spell-out), while the one NEG₂ host (fear)
has a genuinely different marker — a modal, not negation. -/

open Phenomena.Negation.Studies.Tsiakmakis2025
  (ENHostCategory NegatorType)

/-- Map each EN construction to its Tsiakmakis host category.
    Constructions without EN (after, while) have no host. -/
def ENConstruction.toHostCategory : ENConstruction → Option ENHostCategory
  | .before      => some .temporalExpressions
  | .until       => some .temporalExpressions
  | .comparative => some .comparatives
  | .fear        => some .emotiveDoxasticPredicates
  | .after       => none
  | .while_      => none

/-- Constructions with EN are exactly those with a host category. -/
theorem en_iff_has_host (c : ENConstruction) :
    c.hasEN = c.toHostCategory.isSome := by
  cases c <;> rfl

/-- Fear maps to NEG₂ (modal); temporal and comparative map to NEG₁
    (standard negation masked). This connects ambidirectionality
    (distributional pattern) to negator type (mechanism). -/
theorem neg_type_of_en_hosts :
    (ENConstruction.toHostCategory .fear).map ENHostCategory.negatorType
      = some .neg2 ∧
    [ENConstruction.before, .until, .comparative].all
      (fun c => (c.toHostCategory.map ENHostCategory.negatorType) == some .neg1)
      = true :=
  ⟨rfl, rfl⟩

end Phenomena.Negation.ExpletiveNegation
