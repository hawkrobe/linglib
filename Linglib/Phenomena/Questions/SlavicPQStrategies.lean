import Linglib.Fragments.Russian.QuestionParticles
import Linglib.Fragments.Ukrainian.QuestionParticles
import Linglib.Fragments.Polish.QuestionParticles
import Linglib.Fragments.Bulgarian.QuestionParticles
import Linglib.Fragments.Serbian.QuestionParticles
import Linglib.Fragments.Slovenian.QuestionParticles
import Linglib.Fragments.Macedonian.QuestionParticles

/-!
# Cross-Slavic Polar Question Strategies

Typology of default (unbiased) polar question strategies across Slavic
languages, based on Šimík (2024 §4.1). Slavic languages show rich variation
in how they form PQs, using word order alternations, clause-initial particles,
verb-attached particles, and combinations thereof.

## Key Findings

1. **Verb movement languages** (Czech, Slovak, Upper Sorbian): InterPPQ
   (verb-initial positive) is the default unbiased PQ.
2. **Particle languages** (Bulgarian, Russian): verb-attached *li* introduces
   the default PQ.
3. **Clause-initial particle languages** (Ukrainian, Polish): *čy*/*czy* is
   obligatory in PQs.
4. Some languages use multiple strategies (Serbian: *da li*, *je li*;
   Slovenian: *ali*; Macedonian: *dali*).

## Architecture

Profile `particle` fields and BiasParticle `form` fields are derived from
Fragment entries (Phenomena imports Fragments, not vice versa). This ensures
single-source-of-truth: changing a particle form in the Fragment automatically
propagates here.

## References

- Šimík, R. (2024). Polar question semantics and bias: Lessons from Slavic/Czech.
  In B. Gehrke & R. Šimík (eds.), Topics in the semantics of Slavic languages.
- Todorović, N. (2023). Serbian polar questions. Glossa.
- Onoeva, M. & Staňková, A. (to appear). Corpus study of PQ strategies.
- Esipova, M. & Romero, M. (2023). Russian IntonPQs.
-/

namespace Phenomena.Questions.SlavicPQStrategies

-- ============================================================================
-- §1: PQ Encoding Strategies
-- ============================================================================

/-- How a language formally encodes its default (unbiased) polar question. -/
inductive PQStrategy where
  /-- Verb movement to clause-initial position (subject–verb inversion). -/
  | verbMovement
  /-- Clause-initial question particle. -/
  | clauseInitialParticle
  /-- Particle attached to the verb (or focused constituent). -/
  | verbAttachedParticle
  /-- Combination of particle + verb movement. -/
  | particlePlusMovement
  /-- Intonation only (no overt morphosyntactic marking). -/
  | intonationOnly
  deriving DecidableEq, BEq, Repr

/-- Whether the language permits declarative PQs (DeclPQs) as a separate
strategy from interrogative PQs. -/
inductive DeclPQAvailability where
  /-- DeclPQs available and convey evidential bias. -/
  | available
  /-- DeclPQs not available as a distinct strategy. -/
  | unavailable
  /-- DeclPQs marginal or register-restricted. -/
  | marginal
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §2: Slavic Language PQ Data
-- ============================================================================

/-- A Slavic language's PQ strategy profile. -/
structure SlavicPQProfile where
  /-- Language name -/
  language : String
  /-- ISO 639-1 or 639-3 code -/
  code : String
  /-- Default (unbiased) PQ strategy -/
  defaultStrategy : PQStrategy
  /-- Particle form (if applicable), derived from Fragment entries where possible -/
  particle : Option String := none
  /-- Whether DeclPQs are available -/
  declPQ : DeclPQAvailability := .unavailable
  /-- Whether adding negation triggers epistemic bias -/
  negationTriggersBias : Bool := true
  /-- Example number from Šimík 2024 -/
  exampleNum : Option String := none
  deriving Repr, BEq

-- Czech, Slovak, Upper Sorbian: verb movement (no particle Fragment entries)

/-- Czech: verb-initial (VSO) with rising/falling intonation.
No overt PQ particle. Default = InterPPQ (Šimík 2024 ex. 25). -/
def czech : SlavicPQProfile :=
  { language := "Czech", code := "cs"
  , defaultStrategy := .verbMovement
  , declPQ := .available
  , exampleNum := some "25" }

/-- Slovak: verb-initial, parallel to Czech (Šimík 2024 ex. 26). -/
def slovak : SlavicPQProfile :=
  { language := "Slovak", code := "sk"
  , defaultStrategy := .verbMovement
  , declPQ := .available
  , exampleNum := some "26" }

/-- Upper Sorbian: verb-initial (Šimík 2024 ex. 27). -/
def upperSorbian : SlavicPQProfile :=
  { language := "Upper Sorbian", code := "hsb"
  , defaultStrategy := .verbMovement
  , declPQ := .available
  , exampleNum := some "27" }

-- Slovenian, Ukrainian, Polish: clause-initial particle (derived from Fragments)

/-- Slovenian: clause-initial *ali* (optionally) + verb movement.
*ali* is reported as incompatible with DeclPQs (Šimík 2024 ex. 28). -/
def slovenian : SlavicPQProfile :=
  { language := "Slovenian", code := "sl"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Fragments.Slovenian.QuestionParticles.ali.form
  , declPQ := .unavailable
  , exampleNum := some "28" }

/-- Ukrainian: clause-initial *čy* (obligatory) (Šimík 2024 ex. 29). -/
def ukrainian : SlavicPQProfile :=
  { language := "Ukrainian", code := "uk"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Fragments.Ukrainian.QuestionParticles.cy.romanization
  , declPQ := .available
  , exampleNum := some "29" }

/-- Polish: clause-initial *czy* (obligatory in default PQ).
Verb-initial PQs are possible but unacceptable in quiz scenarios
(Šimík 2024 ex. 30d). -/
def polish : SlavicPQProfile :=
  { language := "Polish", code := "pl"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Fragments.Polish.QuestionParticles.czy.form
  , declPQ := .marginal
  , exampleNum := some "30" }

-- Serbian: particle combination

/-- Serbian: *da* (+ *li*) is the default strategy (Šimík 2024 ex. 31).
Serbian has the richest PQ repertoire among Slavic languages
(Todorović 2023). -/
def serbian : SlavicPQProfile :=
  { language := "Serbian", code := "sr"
  , defaultStrategy := .particlePlusMovement
  , particle := some Fragments.Serbian.QuestionParticles.daLi.form
  , declPQ := .unavailable
  , exampleNum := some "31" }

-- Macedonian, Bulgarian, Russian

/-- Macedonian: *dali* (clause-initial) for default PQs.
*dali* can introduce negative PQs without triggering bias, unlike
Bulgarian *li* (Šimík 2024 ex. 32). -/
def macedonian : SlavicPQProfile :=
  { language := "Macedonian", code := "mk"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Fragments.Macedonian.QuestionParticles.dali.romanization
  , declPQ := .unavailable
  , negationTriggersBias := false  -- dali + neg is unbiased
  , exampleNum := some "32" }

/-- Bulgarian: verb-attached *li* (Šimík 2024 ex. 33).
*li* encliticizes onto the focused constituent. -/
def bulgarian : SlavicPQProfile :=
  { language := "Bulgarian", code := "bg"
  , defaultStrategy := .verbAttachedParticle
  , particle := some Fragments.Bulgarian.QuestionParticles.li.romanization
  , declPQ := .marginal  -- colloquial only
  , exampleNum := some "33" }

/-- Russian: verb-attached *li* (formal) or IntonPQ (default).
*li*-PQs are rare in spoken Russian — IntonPQs dominate
(Onoeva & Staňková, to appear: only 6/500 were liPQs).
IntonPQs are arguably unbiased (Šimík 2024 §4.2.3). -/
def russian : SlavicPQProfile :=
  { language := "Russian", code := "ru"
  , defaultStrategy := .intonationOnly
  , particle := some Fragments.Russian.QuestionParticles.li.romanization
  , declPQ := .unavailable
  , exampleNum := some "34" }

def allProfiles : List SlavicPQProfile :=
  [ czech, slovak, upperSorbian, slovenian, ukrainian, polish
  , serbian, macedonian, bulgarian, russian ]

-- ============================================================================
-- §3: Typological Generalizations
-- ============================================================================

/-- Languages using verb movement as default PQ strategy.
These are the languages without an overt question particle in default PQs
(Šimík 2024 fn. 45). -/
def verbMovementLanguages : List SlavicPQProfile :=
  allProfiles.filter (·.defaultStrategy == .verbMovement)

/-- Languages using a clause-initial particle. -/
def particleLanguages : List SlavicPQProfile :=
  allProfiles.filter (·.defaultStrategy == .clauseInitialParticle)

/-- Verb movement languages all have DeclPQs available. -/
theorem verbMovement_implies_declPQ :
    verbMovementLanguages.all (·.declPQ == .available) = true := by native_decide

/-- The *li* family of particles spans Bulgarian, Russian, and (as *da li*) Serbian.
These trace back to proto-Slavic *li* (Šimík 2024 §4.2.1). -/
def liFamily : List SlavicPQProfile :=
  allProfiles.filter λ p =>
    match p.particle with
    | some s => s == "li" || s == "da li"
    | none => false

-- ============================================================================
-- §4: Bias-Related Particles (Šimík 2024 §4.2.4)
-- ============================================================================

/-- The *razve* family: cross-Slavic particles specialized for expressing
mirative/dubitative bias in PQs. These indicate surprise at or doubt about
the evidence (Šimík 2024 §4.2.4).

Russian *razve*, Ukrainian and Belarusian *xiba*, Polish *czyż(by)*,
Bulgarian *nima*, Czech *copak*/*cožpak*/*snad*, Serbian *zar*.

The `form` field is derived from Fragment entries where available. -/
structure BiasParticle where
  language : String
  form : String
  gloss : String
  /-- Compatible with outer (FALSUM) negation? -/
  outerNeg : Bool
  /-- Compatible with inner (VERUM ¬p) negation? -/
  innerNeg : Bool
  deriving Repr, BEq

def razve : BiasParticle :=
  { language := "Russian"
  , form := Fragments.Russian.QuestionParticles.razve_.romanization
  , gloss := "really/RAZVE"
  , outerNeg := true, innerNeg := true }

def nahodou : BiasParticle :=
  { language := "Czech", form := "náhodou", gloss := "by.chance"
  , outerNeg := true, innerNeg := false }

def copak : BiasParticle :=
  { language := "Czech", form := "copak", gloss := "RAZVE.CZ"
  , outerNeg := true, innerNeg := true }

def zar : BiasParticle :=
  { language := "Serbian"
  , form := Fragments.Serbian.QuestionParticles.zar_.form
  , gloss := "RAZVE.SR"
  , outerNeg := true, innerNeg := true }

/-- Russian *razve* is compatible with both inner and outer negation
(Repp & Geist 2022). It stays constant across VERUM and FALSUM
because both involve a conflict between epistemic and evidential bias. -/
theorem razve_both_negations :
    razve.outerNeg = true ∧ razve.innerNeg = true := ⟨rfl, rfl⟩

/-- Czech *náhodou* is restricted to outer negation only, unlike *razve*
(Staňková 2026, Šimík 2024 §5). -/
theorem nahodou_outer_only :
    nahodou.outerNeg = true ∧ nahodou.innerNeg = false := ⟨rfl, rfl⟩

/-- *razve* and *náhodou* differ in inner negation compatibility, despite
both being ordering source modifiers. This reflects different selectional
requirements: razve is compatible with both VERUM and FALSUM, while
náhodou only modifies FALSUM's epistemic possibility component. -/
theorem razve_nahodou_differ :
    razve.innerNeg ≠ nahodou.innerNeg := by decide

-- ============================================================================
-- §5: Fragment-Derived Cross-Linguistic Generalizations
-- ============================================================================

/-! These theorems verify empirical generalizations directly against Fragment
lexical data. Because profile/BiasParticle fields derive from Fragments,
there are no separate "bridge" theorems — the connection is by construction. -/

/-- All RAZVE-family Fragment entries require evidential bias. -/
theorem razve_family_all_evidential :
    Fragments.Russian.QuestionParticles.razve_.requiresEvidentialBias = true ∧
    Fragments.Ukrainian.QuestionParticles.xiba.requiresEvidentialBias = true ∧
    Fragments.Polish.QuestionParticles.czyzby.requiresEvidentialBias = true ∧
    Fragments.Bulgarian.QuestionParticles.nima.requiresEvidentialBias = true ∧
    Fragments.Serbian.QuestionParticles.zar_.requiresEvidentialBias = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- All neutral PQ Fragment entries do NOT require evidential bias. -/
theorem neutral_particles_no_evidential :
    Fragments.Russian.QuestionParticles.li.requiresEvidentialBias = false ∧
    Fragments.Ukrainian.QuestionParticles.cy.requiresEvidentialBias = false ∧
    Fragments.Polish.QuestionParticles.czy.requiresEvidentialBias = false ∧
    Fragments.Bulgarian.QuestionParticles.li.requiresEvidentialBias = false ∧
    Fragments.Serbian.QuestionParticles.daLi.requiresEvidentialBias = false ∧
    Fragments.Slovenian.QuestionParticles.ali.requiresEvidentialBias = false ∧
    Fragments.Macedonian.QuestionParticles.dali.requiresEvidentialBias = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Phenomena.Questions.SlavicPQStrategies
