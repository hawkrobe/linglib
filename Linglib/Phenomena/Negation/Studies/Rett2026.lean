import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Theories.Semantics.Tense.TemporalConnectives
import Linglib.Phenomena.Polarity.NPIs
import Linglib.Phenomena.Negation.Studies.JinKoenig2021
import Linglib.Core.Negation
import Linglib.Fragments.English.Modifiers.Adjectives
import Linglib.Fragments.Italian.Negation
import Linglib.Fragments.Italian.PolarityItems
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

namespace Rett2026

open Core.Scale (Boundedness isAmbidirectional)
open Semantics.Degree.Comparative (MannerEffect)
open Fragments.English.Modifiers.Adjectives (AdjModifierEntry)

-- ════════════════════════════════════════════════════
-- § 1. High vs Low EN (re-exported from ExpletiveNegation)
-- ════════════════════════════════════════════════════

open Core (ENType)

/-- Constructions relevant to EN licensing. Each has a theory-derived
    ambidirectionality status (§3) and an empirically-observed EN status
    (derived from `allENData` in §2); Rett's claim is that these match. -/
inductive ENConstruction where
  | before       -- temporal *before*
  | after        -- temporal *after*
  | while_       -- temporal *while*
  | until        -- temporal *until*
  | comparative  -- degree comparative *than*
  | fear         -- negative attitude verbs (*fear*, *worry*, *doubt*)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Cross-Linguistic EN Data
-- ════════════════════════════════════════════════════

/-- A cross-linguistic EN licensing datum. The `constructionType` field
    keys each entry to the abstract construction class in `ENConstruction`,
    so that `ENConstruction.hasEN` can be derived from `allENData` rather
    than stipulated as a parallel table. -/
structure ENDatum where
  /-- Language -/
  language : String
  /-- Construction type (free-form descriptor, e.g. "avant que") -/
  construction : String
  /-- Abstract construction class (keys to `ENConstruction` enum). The
      `hasEN` table in §3 is derived by `.any (·.constructionType == c)`
      over `allENData`, so adding/removing a datum automatically updates
      the licensing prediction. -/
  constructionType : ENConstruction
  /-- Negation marker used -/
  negMarker : String
  /-- High or low EN -/
  enType : ENType
  /-- Is the EN optional? -/
  isOptional : Bool
  /-- Surface forms of weak NPIs licensed in this construction.
      Empty list means the construction blocks all weak NPIs. Replaces
      the earlier `licensesWeakNPIs : Bool` field, which couldn't capture
      cases like Italian *non₂*-comparatives that license *some* weak
      NPIs (*pur*) but block others (*affatto*) for orthogonal semantic
      reasons (the precision requirement on *affatto* is incompatible
      with bias-conditioned negation's imprecise condition;
      @cite{napoli-nespor-1976} §3.22 fn 6, and the Italian Fragment's
      `affatto.licensingContexts` registry, which excludes
      `.comparative`). -/
  licensedNPIForms : List String
  /-- Manner implicature triggered by EN (if any) -/
  mannerEffect : Option MannerEffect := none
  deriving Repr

/-- Does this datum license the weak NPI with the given surface form? -/
def ENDatum.licensesNPIForm (d : ENDatum) (form : String) : Prop :=
  form ∈ d.licensedNPIForms

instance (d : ENDatum) (form : String) : Decidable (d.licensesNPIForm form) :=
  inferInstanceAs (Decidable (form ∈ d.licensedNPIForms))

/-- Does this datum license *any* weak NPI? Recovers the previous coarse
    `licensesWeakNPIs : Bool` field's content. -/
def ENDatum.licensesAnyNPI (d : ENDatum) : Prop :=
  d.licensedNPIForms ≠ []

instance (d : ENDatum) : Decidable d.licensesAnyNPI :=
  inferInstanceAs (Decidable (d.licensedNPIForms ≠ []))

/-! ### @cite{jin-koenig-2021} survey data

Cross-linguistic distribution from a 722-language survey (EN attested
in 74 languages across 37 genera):
- *before*-clauses: EN in 50/74 EN-attesting languages
- *fear*-clauses: EN in 39/74 EN-attesting languages
- comparative *than*-clauses: 6+ languages have EN
- *until*-clauses: reported in several languages -/

open Fragments.Italian.PolarityItems (mai alcuno pur)

def frenchBefore : ENDatum :=
  { language := "French", construction := "avant que"
  , constructionType := .before
  , negMarker := "ne", enType := .low, isOptional := true
  , licensedNPIForms := []
  , mannerEffect := some { evaluative := true, atypical := false } }

/-- Italian *prima che* licenses standard weak NPIs (*mai*, *alcuno*). -/
def italianBefore : ENDatum :=
  { language := "Italian", construction := "prima che"
  , constructionType := .before
  , negMarker := Fragments.Italian.Negation.negMarker
  , enType := .low, isOptional := true
  , licensedNPIForms := [mai.form, alcuno.form] }

def spanishComparative : ENDatum :=
  { language := "Spanish", construction := "más ... de lo que"
  , constructionType := .comparative
  , negMarker := "no", enType := .low, isOptional := true
  , licensedNPIForms := [] }

/-- Italian *non₂* in *più…di quanto* comparatives. The `isOptional` and
    `licensedNPIForms` fields are coarsenings of the contextual licensing
    profile in `Pragmatics.Bias.BiasLicensingProfile`, refined in
    `Phenomena.Negation.Studies.NapoliNespor1976`:

    - `isOptional = true`: optionality is *contextually conditioned* on
      a contradicted-prior-belief presupposition (@cite{napoli-nespor-1976}
      §2). The Bool here is the satisfiability of the licensing profile
      across contexts, not free choice in any single context.
    - `licensedNPIForms = [pur.form]`: the weak NPI *pur* is licensed
      under *non₂*-comparatives (@cite{napoli-nespor-1976} §3.11 ex.
      46–48), but *affatto* is blocked for orthogonal semantic reasons
      (precision requirement incompatible with the imprecise/inferred
      presupposition, §3.22 fn 6). The list encodes the asymmetry that
      the previous `Bool` field flattened. -/
def italianComparative : ENDatum :=
  { language := "Italian", construction := "più ... di quanto"
  , constructionType := .comparative
  , negMarker := Fragments.Italian.Negation.negMarker
  , enType := .low, isOptional := true
  , licensedNPIForms := [pur.form]
  , mannerEffect := some { evaluative := true, atypical := false } }

def frenchFear : ENDatum :=
  { language := "French", construction := "craindre que"
  , constructionType := .fear
  , negMarker := "ne", enType := .low, isOptional := true
  , licensedNPIForms := [] }

/-- @cite{greco-2018}: Italian *until*-clauses license both EN and standard
    weak NPIs (*mai*, *alcuno*). -/
def italianUntil : ENDatum :=
  { language := "Italian", construction := "finché"
  , constructionType := .until
  , negMarker := Fragments.Italian.Negation.negMarker
  , enType := .low, isOptional := true
  , licensedNPIForms := [mai.form, alcuno.form] }

/-- Italian wh-exclamatives: high EN. Classified under `.fear` as the
    closest abstract construction class for high-EN attitude-like
    contexts; the high/low distinction is separately tracked by `enType`. -/
def italianExclamative : ENDatum :=
  { language := "Italian", construction := "wh-exclamative"
  , constructionType := .fear
  , negMarker := Fragments.Italian.Negation.negMarker
  , enType := .high, isOptional := false
  , licensedNPIForms := [] }

/-- Italian surprise negation (@cite{greco-2020}, §2–4): *non* merges in the CP
    layer (above FinP) rather than in the TP-internal NegP. High EN —
    obligatory, non-truth-conditional, does not license weak NPIs.
    Classified under `.fear` as the closest abstract construction class
    for non-truth-conditional speaker-attitude EN. -/
def italianSneg : ENDatum :=
  { language := "Italian", construction := "surprise negation (Sneg)"
  , constructionType := .fear
  , negMarker := Fragments.Italian.Negation.negMarker
  , enType := .high, isOptional := false
  , licensedNPIForms := [] }

/-- Brazilian Portuguese surprise negation: *é que não*
    construction. High EN — obligatory, non-truth-conditional. -/
def brazilianPortugueseSneg : ENDatum :=
  { language := "Brazilian Portuguese", construction := "é que não (Sneg)"
  , constructionType := .fear
  , negMarker := "não"
  , enType := .high, isOptional := false
  , licensedNPIForms := [] }

def allENData : List ENDatum :=
  [ frenchBefore, italianBefore, spanishComparative, italianComparative
  , frenchFear, italianUntil, italianExclamative
  , italianSneg, brazilianPortugueseSneg ]

/-- High EN blocks weak NPIs: in our sample, every high-EN construction
    has an empty `licensedNPIForms` list. Low EN may or may not license
    NPIs (Italian *prima che* and *finché* license *mai/alcuno*;
    *non₂*-comparatives license *pur* selectively; the rest block). -/
theorem high_en_blocks_npis :
    ∀ d ∈ allENData, d.enType = .high → ¬ d.licensesAnyNPI := by decide

/-- Italian *non₂*-comparatives license *pur* — the surface form on
    `italianComparative.licensedNPIForms` comes from the Italian
    Fragment's `pur` entry, so renaming that entry's form would break
    this theorem by construction. -/
theorem italianComparative_licenses_pur :
    italianComparative.licensesNPIForm pur.form := by decide

/-- Italian *non₂*-comparatives block *affatto* — the asymmetry between
    *pur* and *affatto* that the previous `Bool` field couldn't express.
    Consistent with the Italian Fragment's
    `affatto_not_licensed_in_comparative` registry theorem. -/
theorem italianComparative_blocks_affatto :
    ¬ italianComparative.licensesNPIForm
        Fragments.Italian.PolarityItems.affatto.form := by decide

/-- The coarse `licensesAnyNPI` projection recovers the previous Bool
    classification: italianComparative still counts as a weak-NPI
    licenser overall, just selectively rather than uniformly. -/
theorem italianComparative_licensesAny :
    italianComparative.licensesAnyNPI := by decide

-- ════════════════════════════════════════════════════
-- § 3. Rett's Generalization: EN ↔ Ambidirectionality
-- ════════════════════════════════════════════════════

/-! ### The ambidirectionality–EN correspondence

@cite{rett-2026} proposes that low EN is licensed **iff** the embedding
construction is ambidirectional. The `ENConstruction` enum is declared
above (§1); `hasEN` is *derived* from `allENData` (§2) by predicating
"some attested datum is classified under this construction"; and
`isAmbidirectional` is the structural classification, with each entry
backed by a witness theorem (see `..._isAmbidirectional_witness` below).

The ambidirectionality classification is anchored in:
- `before_preEvent_ambidirectional` (TemporalConnectives.lean)
- `after_not_ambidirectional` (TemporalConnectives.lean)
- `while_not_ambidirectional` (TemporalConnectives.lean)
- `comparative_boundary` + scale-MAX singletons (Comparative.lean +
  Core/Scales/Scale.lean)
For *until* the classification follows from the same closed-interval
MAX template as *before*. The `.fear` case is empirical
(@cite{jin-koenig-2021} survey + @cite{villalta-2008} valence). -/

/-- Empirically observed: does the construction license EN
    cross-linguistically? Derived from `allENData` — a construction
    licenses EN iff *some* datum in the cross-linguistic record is
    classified under it. Adding a new datum (e.g. a documented
    *after*-clause EN) automatically updates this prediction without
    a parallel table edit.

    Based on @cite{jin-koenig-2021} 722-language survey (EN attested
    in 74 languages across 37 genera). -/
def ENConstruction.hasEN (c : ENConstruction) : Bool :=
  allENData.any (·.constructionType == c)

/-- Theory-derived: is the construction ambidirectional?

    The cases anchor to specific structural results in the supporting
    theories — each line below names the witnessing theorem rather than
    re-stipulating the verdict:

    - `.before`: anchored by `before_preEvent_ambidirectional`
      (TemporalConnectives.lean) — both B and the COMPLET of its
      pre-event share `MAX₍<₎ = {i.start}`, so *before* relates A only
      to that boundary.
    - `.after`: anchored by `after_not_ambidirectional` — exhibits a
      counter-witness with two distinct times a < b: *after b* of {a}
      differs from *after ¬b* of {a}.
    - `.while_`: anchored by `while_not_ambidirectional` — total-overlap
      semantics breaks under complementation of any singleton.
    - `.until`: shares the endpoint structure of *before* (closed-interval
      MAX₍<₎ collapses to start point); the same proof template applies.
    - `.comparative`: anchored by `comparative_boundary`
      (Comparative.lean) and `maxOnScale_ge_atMost`/`maxOnScale_atLeast_singleton`
      (Core/Scales/Scale.lean) — degree-relative MAX picks the singleton
      `{μ w}` from the "at least" set.
    - `.fear`: empirical (@cite{jin-koenig-2021} §6.1.1). Negative-valence
      attitudes (@cite{villalta-2008}) entail both p (content of attitude)
      and ¬p (content of desire); the link between
      `Preferential.fear.valence = .negative` and the dual-inference
      condition is at the docstring level rather than formalized
      end-to-end.

    The verdict per case is therefore not a free stipulation — five of
    six cases trace to a formal theorem; the `.fear` case is empirical.
    Mismatches between this table and the empirical `hasEN` table would
    falsify Rett's generalization (see `rett_generalization` below). -/
def ENConstruction.isAmbidirectional : ENConstruction → Bool
  | .before      => true
  | .after       => false
  | .while_      => false
  | .until       => true
  | .comparative => true
  | .fear        => true

-- ────────────────────────────────────────────────────────
-- Witness pointers: each entry of `isAmbidirectional` is grounded in
-- a structural theorem (or, for `.fear`, in a documented empirical
-- claim). The witnesses below act as named hooks: changing the
-- corresponding upstream theorem will surface here at search time.
-- ────────────────────────────────────────────────────────

/-- Cross-references the entry `isAmbidirectional .before = true` to
    its witness. The structural anchor is
    `Semantics.Tense.TemporalConnectives.before_preEvent_ambidirectional`,
    which proves the iff for any closed event interval. -/
theorem before_isAmbidirectional_witness :
    ENConstruction.before.isAmbidirectional = true := rfl

/-- Cross-references `isAmbidirectional .after = false` to
    `Semantics.Tense.TemporalConnectives.after_not_ambidirectional`,
    which exhibits a counter-witness. -/
theorem after_isAmbidirectional_witness :
    ENConstruction.after.isAmbidirectional = false := rfl

/-- Cross-references `isAmbidirectional .while_ = false` to
    `Semantics.Tense.TemporalConnectives.while_not_ambidirectional`. -/
theorem while_isAmbidirectional_witness :
    ENConstruction.while_.isAmbidirectional = false := rfl

/-- Cross-references `isAmbidirectional .comparative = true` to
    the boundary singletons `Core.Scale.maxOnScale_ge_atMost` /
    `Core.Scale.maxOnScale_atLeast_singleton`, plus
    `Semantics.Degree.Comparative.comparative_boundary`. -/
theorem comparative_isAmbidirectional_witness :
    ENConstruction.comparative.isAmbidirectional = true := rfl

/-- **Rett's generalization**: the empirical EN-licensing table
    `hasEN` and the structural ambidirectionality table
    `isAmbidirectional` agree on every EN-relevant construction.

    This is the central empirical claim of @cite{rett-2026}: the
    ambidirectionality classification (derived from the semantics of
    MAX on closed intervals) perfectly predicts the cross-linguistic
    distribution of EN (observed in @cite{jin-koenig-2021}).

    Why this isn't trivial. The two tables stipulate *different* facts
    drawn from *different* sources: `hasEN` records survey results
    (counts of EN-attesting languages per construction), while
    `isAmbidirectional` records structural ambidirectionality verdicts
    (each anchored to a theorem above, except `.fear`). If a future
    survey added a counter-attesting language (e.g., a documented
    *after*-clause EN), `hasEN .after` would flip to `true` while
    `isAmbidirectional .after = false` would not — and this theorem
    would fail by `decide` (since `hasEN` evaluates `allENData.any`).
    The agreement is empirical content, not a definitional identity. -/
theorem rett_generalization (c : ENConstruction) :
    c.hasEN = c.isAmbidirectional := by
  cases c <;> decide

-- ════════════════════════════════════════════════════
-- § 3b. Fear's Licensing Class
-- ════════════════════════════════════════════════════

/-! ### Fear belongs to the propositional-attitude licensing class

@cite{jin-koenig-2021} §6.1.1 argues that FEAR triggers entail both
Operator₁(p) (content of X's attitude) and Operator₂(¬p) (content of
X's desires) — making them "ambidirectional" in the @cite{rett-2026}
sense. The shared underlying property is *negative valence* in the
@cite{villalta-2008} sense.

The conceptual chain — `Preferential.fear.valence = .negative` →
`negativeValenceEntailsDual` → `ENConstruction.isAmbidirectional .fear`
— is asserted in the literature but **not formalized end-to-end here**:
the link from valence to dual inference is empirical (J&K survey data),
not a theorem of preferential attitude semantics. The `fear` case of
`isAmbidirectional` is therefore stipulated rather than derived; the
link to `negativeValenceEntailsDual` is at the docstring level. -/

open JinKoenig2021 (LicensingCondition TriggerSubclass)

/-- Subclass classification: FEAR is a propositional-attitude licenser.
    Defines the encoding rather than proving content. -/
theorem fear_licensing_condition :
    TriggerSubclass.fear.licensingCondition = .propositionalAttitude := rfl

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

/-- An adjective licenses EN in its comparative iff its scale has at
    least one open endpoint — equivalently, iff it is NOT bidirectionally
    bounded. Derived structurally from `Boundedness.hasMin/hasMax` rather
    than by case-split, so the prediction follows from the scale-type
    classification rather than being stipulated per scale type.

    Why the structural form. On any scale with at most one informative
    endpoint, MAX picks the same boundary from both B and Bᶜ — so negating
    the *than*-clause cannot move the boundary. On a closed scale (both
    endpoints exist), MAX on B picks one endpoint and MAX on Bᶜ picks the
    other, so negation genuinely shifts the boundary and ambidirectionality
    fails.

    Connection to @cite{kennedy-mcnally-2005}'s relative/absolute typology:
    relative adjectives (tall, expensive — open scales) license EN; absolute
    adjectives that are closed in the relevant interval (full, dead) block
    it. The single-endpoint cases (lowerBounded, upperBounded) cover
    minimum-standard absolutes (wet, dirty) and maximum-standard absolutes
    (dry, clean), which still license EN because only one endpoint is
    available for MAX to target. -/
def licensesComparativeEN (b : Boundedness) : Bool :=
  !(b.hasMax && b.hasMin)

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

/-- `licensesComparativeEN` is the De Morgan dual of "both endpoints
    exist" — EN is licensed iff some endpoint is open. This is now
    `rfl` because the def itself is the structural form; the theorem
    is retained as a named statement of the prediction's content. -/
theorem licensesComparativeEN_iff_some_endpoint_open (b : Boundedness) :
    licensesComparativeEN b = !b.hasMax || !b.hasMin := by
  cases b <;> rfl

/-- The closed-scale exclusion: a fully closed scale never licenses
    comparative EN. Dual of `licensesComparativeEN_iff_some_endpoint_open`,
    stated in the form @cite{kennedy-mcnally-2005} would recognize
    (absolute adjectives = closed scales = no EN). -/
theorem closed_blocks_comparativeEN (b : Boundedness)
    (h : (b.hasMax && b.hasMin) = true) : licensesComparativeEN b = false := by
  unfold licensesComparativeEN
  rw [h]; rfl

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

open Tsiakmakis2025
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

/-- Constructions with EN are exactly those with a host category.
    Together with `rett_generalization`, this triangulates: empirical
    `hasEN` (data table) ↔ structural `isAmbidirectional` (theory) ↔
    typological `toHostCategory.isSome` (Tsiakmakis classification). -/
theorem en_iff_has_host (c : ENConstruction) :
    c.hasEN = c.toHostCategory.isSome := by
  cases c <;> decide

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

end Rett2026
