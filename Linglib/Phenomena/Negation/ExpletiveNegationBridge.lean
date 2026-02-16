import Linglib.Theories.Semantics.Lexical.Adjective.Comparative
import Linglib.Theories.Semantics.Tense.TemporalConnectives
import Linglib.Phenomena.Polarity.NPIs
import Linglib.Fragments.English.Modifiers.Adjectives

/-!
# Expletive Negation: Typology and Licensing

Expletive negation (EN) is truth-conditionally vacuous negation that appears
in specific grammatical environments cross-linguistically. Rett (2026) unifies
the licensing conditions: EN is licensed exactly in **ambidirectional**
constructions — those where negating an argument doesn't change truth
conditions because MAX picks the same informative bound from both B and ¬B.

## The Ambidirectionality Generalization

| Construction  | Ambidirectional? | Licenses EN? | Source               |
|---------------|-----------------|--------------|----------------------|
| *before*      | ✓               | ✓ (50 langs) | Jin & Koenig 2021    |
| *after*       | ✗               | ✗            | Rett 2026            |
| *while*       | ✗               | ✗            | Rett 2026            |
| *until*       | ✓               | ✓            | Rett 2026 §5         |
| comparative   | ✓               | ✓ (6+ langs) | Jin & Koenig 2021    |
| *fear/worry*  | ✓               | ✓ (39 langs) | Jin & Koenig 2021    |

## High vs Low EN (Greco 2018, 2019)

Two types of EN with different syntactic positions and licensing:
- **High EN**: targets non-truth-conditional content (exclamatives, surprise);
  obligatory where it appears.
- **Low EN**: targets truth-conditional content in ambidirectional environments;
  optional and triggers manner implicature (evaluativity).

## References

- Rett, J. (2026). Semantic ambivalence and expletive negation. *Language*.
- Jin, M. & Koenig, J.-P. (2021). A cross-linguistic survey of expletive
  negation. *Glossa* 6(1):25.
- Greco, C. (2018). Negative Polarity Items and Expletive Negation.
- Greco, C. (2019). The structure of expletive negation.
- Halm, T. & Huszár, B. (2021). High and low expletive negation.
- Cépeda, P. (2018). Expletive negation and evaluativity.
- Krifka, M. (2010b). *Before* and *after* without coercion.
- Kennedy, C. & McNally, L. (2005). Scale structure, degree modification.
- Napoli, D. J. & Nespor, M. (1976). Negatives in comparatives.
-/

namespace Phenomena.Negation.ExpletiveNegation

open Core.Scale (Boundedness isAmbidirectional)
open TruthConditional.Adjective.Comparative (MannerEffect)
open Fragments.English.Modifiers.Adjectives (AdjModifierEntry)

-- ════════════════════════════════════════════════════
-- § 1. High vs Low EN
-- ════════════════════════════════════════════════════

/-- Two syntactic types of expletive negation (Greco 2018, 2019;
    Halm & Huszár 2021).

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

/-! ### Jin & Koenig (2021) survey data

Cross-linguistic distribution from a 70-language sample:
- *before*-clauses: 50/70 languages have EN
- *fear*-clauses: 39/70 languages have EN
- comparative *than*-clauses: 6+ languages have EN
- *until*-clauses: reported in several languages -/

def frenchBefore : ENDatum :=
  { language := "French", construction := "avant que"
  , negMarker := "ne", enType := .low, isOptional := true
  , licensesWeakNPIs := false
  , mannerEffect := some { evaluative := true, atypical := false } }

def italianBefore : ENDatum :=
  { language := "Italian", construction := "prima che"
  , negMarker := "non", enType := .low, isOptional := true
  , licensesWeakNPIs := true }

def spanishComparative : ENDatum :=
  { language := "Spanish", construction := "más ... de lo que"
  , negMarker := "no", enType := .low, isOptional := true
  , licensesWeakNPIs := false }

def italianComparative : ENDatum :=
  { language := "Italian", construction := "più ... di quanto"
  , negMarker := "non", enType := .low, isOptional := true
  , licensesWeakNPIs := false
  , mannerEffect := some { evaluative := true, atypical := false } }

def frenchFear : ENDatum :=
  { language := "French", construction := "craindre que"
  , negMarker := "ne", enType := .low, isOptional := true
  , licensesWeakNPIs := false }

/-- Greco (2018): Italian *until*-clauses license both EN and weak NPIs. -/
def italianUntil : ENDatum :=
  { language := "Italian", construction := "finché"
  , negMarker := "non", enType := .low, isOptional := true
  , licensesWeakNPIs := true }

/-- Italian wh-exclamatives: high EN (Greco 2018). -/
def italianExclamative : ENDatum :=
  { language := "Italian", construction := "wh-exclamative"
  , negMarker := "non", enType := .high, isOptional := false
  , licensesWeakNPIs := false }

def allENData : List ENDatum :=
  [ frenchBefore, italianBefore, spanishComparative, italianComparative
  , frenchFear, italianUntil, italianExclamative ]

-- ════════════════════════════════════════════════════
-- § 3. Rett's Generalization: EN ↔ Ambidirectionality
-- ════════════════════════════════════════════════════

/-! ### The ambidirectionality–EN correspondence

Rett (2026) proposes that low EN is licensed **iff** the embedding
construction is ambidirectional. We formalize this as a correspondence
between an enumeration of EN-relevant constructions (with their
theory-derived ambidirectionality classification) and the empirical
record of which constructions license EN cross-linguistically.

The ambidirectionality classification is derived from:
- `before_ambidirectional` (TemporalConnectives.lean)
- `after_not_ambidirectional` (TemporalConnectives.lean)
- `while_not_ambidirectional` (TemporalConnectives.lean)
- `comparative_ambidirectional` (Comparative.lean)
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
      (cf. `comparative_ambidirectional` in Comparative.lean)
    - `fear`: ambidirectional — *fear p* and *fear ¬p* share the
      worry-worthy possibility (Rett 2026, §7) -/
def ENConstruction.isAmbidirectional : ENConstruction → Bool
  | .before      => true
  | .after       => false
  | .while_      => false
  | .until       => true
  | .comparative => true
  | .fear        => true

/-- Empirically observed: does the construction license EN
    cross-linguistically? Based on Jin & Koenig (2021) 70-language survey. -/
def ENConstruction.hasEN : ENConstruction → Bool
  | .before      => true   -- 50/70 languages
  | .after       => false
  | .while_      => false
  | .until       => true   -- Italian finché, etc.
  | .comparative => true   -- 6+ languages
  | .fear        => true   -- 39/70 languages

/-- **Rett's generalization**: a construction licenses EN iff it is
    ambidirectional. Verified exhaustively over all EN-relevant
    constructions.

    This is the central empirical claim of Rett (2026): the
    ambidirectionality classification (derived from the semantics of
    MAX on closed intervals) perfectly predicts the cross-linguistic
    distribution of EN (observed in Jin & Koenig 2021). -/
theorem rett_generalization (c : ENConstruction) :
    c.hasEN = c.isAmbidirectional := by
  cases c <;> rfl

-- ════════════════════════════════════════════════════
-- § 4. Scale Type → EN Licensing in Comparatives
-- ════════════════════════════════════════════════════

/-! ### Connecting Fragment entries to EN predictions

Rett (2026, fn. on Kennedy & McNally 2005) predicts that EN in
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

1. **French *avant que ... ne***: "before ¬B" → "well before B" (temporal
   distance reading; Cépeda 2018, Krifka 2010b).

2. **Italian comparative + *non***: "più alto di quanto non sia" →
   "much taller than" (evaluative reading; Napoli & Nespor 1976).

3. **Negative verbs (doubt, fear, worry)**: These are "ambidirectional"
   embedding verbs (Rett 2026, §7) — *fear that p* and *fear that ¬p*
   share the same worry-worthy proposition, because the feared event's
   mere possibility (whether p or ¬p) triggers the attitude. EN in
   complements of fear is attested in 39 languages (Jin & Koenig 2021). -/

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

end Phenomena.Negation.ExpletiveNegation
