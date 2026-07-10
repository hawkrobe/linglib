import Linglib.Features.QParticleLayer
import Linglib.Semantics.Questions.Bias
import Linglib.Fragments.Slavic.Russian.QuestionParticles
import Linglib.Fragments.Slavic.Bulgarian.QuestionParticles
import Linglib.Fragments.Slavic.Ukrainian.QuestionParticles
import Linglib.Fragments.Slavic.Polish.QuestionParticles
import Linglib.Fragments.Slavic.Slovenian.QuestionParticles
import Linglib.Fragments.Slavic.Serbian.QuestionParticles
import Linglib.Fragments.Slavic.Macedonian.QuestionParticles

/-!
# Šimík (2024): Polar Question Semantics and Bias in Slavic
[simik-2024] [bhatt-dayal-2020] [dayal-2025] [esipova-romero-2023]

Šimík's cross-Slavic survey of polar-question particles classifies each
particle by its left-peripheral layer in the [bhatt-dayal-2020] /
[dayal-2025] cartography `[SAP [PerspP [CP ...]]]`.

The fragments in `Fragments/{Russian,Bulgarian,Ukrainian,Polish,
Slovenian,Serbian,Macedonian}/QuestionParticles.lean` carry only
theory-neutral lexical primitives (form, position, distribution). This
study file overlays [simik-2024]'s layer assignments and bias
classification (`evidentialRequirement`) and proves the Slavic
generalization that the *neutral* PQ-particle of each surveyed language
sits at CP, while the *biased mirative* particles (the cross-Slavic
RAZVE family) sit at PerspP.

## Particle layer assignments

| Language    | Particle  | Layer   |
|-------------|-----------|---------|
| Russian     | li        | CP      |
| Russian     | razve     | PerspP  |
| Bulgarian   | li        | CP      |
| Bulgarian   | nima      | PerspP  |
| Ukrainian   | čy        | CP      |
| Ukrainian   | xiba      | PerspP  |
| Polish      | czy       | CP      |
| Polish      | czyżby    | PerspP  |
| Slovenian   | ali       | CP      |
| Serbian     | da li     | CP      |
| Serbian     | zar       | PerspP  |
| Macedonian  | dali      | CP      |

The Slavic data is the empirical anchor for the cross-linguistic claim
that the cartography in [dayal-2025] extends beyond Hindi-Urdu and
Japanese to a much wider typological range.

The file also records [simik-2024] §4.1's typology of default (unbiased)
PQ strategies across ten Slavic languages (`PQProfile`).
-/

namespace Simik2024

open Features (QParticleLayer)

/-! ## Layer assignment for each Slavic Q-particle.

Each `def` records Šimík's classification of a Fragment particle. The
`_` argument is unused because the layer assignment is a theoretical
overlay on the particle, not a computed property of its lexical fields. -/

def russianLi_layer        (_ : Particle) : QParticleLayer := .cp
def russianRazve_layer     (_ : Particle) : QParticleLayer := .perspP
def bulgarianLi_layer      (_ : Particle) : QParticleLayer := .cp
def bulgarianNima_layer    (_ : Particle) : QParticleLayer := .perspP
def ukrainianCy_layer      (_ : Particle) : QParticleLayer := .cp
def ukrainianXiba_layer    (_ : Particle) : QParticleLayer := .perspP
def polishCzy_layer        (_ : Particle) : QParticleLayer := .cp
def polishCzyzby_layer     (_ : Particle) : QParticleLayer := .perspP
def slovenianAli_layer     (_ : Particle) : QParticleLayer := .cp
def serbianDaLi_layer      (_ : Particle) : QParticleLayer := .cp
def serbianZar_layer       (_ : Particle) : QParticleLayer := .perspP
def macedonianDali_layer   (_ : Particle) : QParticleLayer := .cp

/-! ## Cross-Slavic generalizations -/

open Russian.QuestionParticles    in
open Bulgarian.QuestionParticles  in
open Ukrainian.QuestionParticles  in
open Polish.QuestionParticles     in
open Slovenian.QuestionParticles  in
open Serbian.QuestionParticles    in
open Macedonian.QuestionParticles in
/-- The neutral polar-question particle of every surveyed Slavic language
    sits at CP. Which particle counts as *neutral* is Šimík's
    classification, recorded below as `evidentialRequirement`. -/
theorem neutral_PQ_particles_are_CP :
    russianLi_layer Russian.QuestionParticles.li = .cp ∧
    bulgarianLi_layer Bulgarian.QuestionParticles.li = .cp ∧
    ukrainianCy_layer Ukrainian.QuestionParticles.cy = .cp ∧
    polishCzy_layer Polish.QuestionParticles.czy = .cp ∧
    slovenianAli_layer Slovenian.QuestionParticles.ali = .cp ∧
    serbianDaLi_layer Serbian.QuestionParticles.daLi = .cp ∧
    macedonianDali_layer Macedonian.QuestionParticles.dali = .cp :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

open Russian.QuestionParticles    in
open Bulgarian.QuestionParticles  in
open Ukrainian.QuestionParticles  in
open Polish.QuestionParticles     in
open Serbian.QuestionParticles    in
/-- The cross-Slavic *RAZVE* family — the mirative/dubitative particles
    that signal conflict between speaker's prior epistemic state and
    incoming contextual evidence — uniformly sits at PerspP. -/
theorem razve_family_is_PerspP :
    russianRazve_layer Russian.QuestionParticles.razve_ = .perspP ∧
    bulgarianNima_layer Bulgarian.QuestionParticles.nima = .perspP ∧
    ukrainianXiba_layer Ukrainian.QuestionParticles.xiba = .perspP ∧
    polishCzyzby_layer Polish.QuestionParticles.czyzby = .perspP ∧
    serbianZar_layer Serbian.QuestionParticles.zar_ = .perspP :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The cross-Slavic *RAZVE* family as a list. Šimík's bias
    classification (§4.2): these require contextual evidence for p
    (`evidentialRequirement`), while the neutral PQ particles impose no
    bias requirement. The layer assignments above correlate — RAZVE =
    PerspP, neutral = CP — which is Šimík's analysis, not a lexical
    fact, so both classifications live here rather than on the fragment
    entries. -/
def razveFamily : List Particle :=
  [Russian.QuestionParticles.razve_, Bulgarian.QuestionParticles.nima,
   Ukrainian.QuestionParticles.xiba, Polish.QuestionParticles.czyzby,
   Serbian.QuestionParticles.zar_]

/-- Evidential requirement per Šimík: `.forP` for the RAZVE family,
    none for the neutral particles. -/
def evidentialRequirement (p : Particle) :
    Option Semantics.Questions.Bias.ContextualEvidence :=
  if p ∈ razveFamily then some .forP else none

/-! ### Default PQ strategies

[simik-2024] §4.1's typology of default (unbiased) polar-question
strategies across ten Slavic languages. `particle` fields are derived
from Fragment entries. -/

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
  deriving DecidableEq, Repr

/-- Whether the language permits declarative PQs (DeclPQs) as a separate
strategy from interrogative PQs. -/
inductive DeclPQAvailability where
  /-- DeclPQs available and convey evidential bias. -/
  | available
  /-- DeclPQs not available as a distinct strategy. -/
  | unavailable
  /-- DeclPQs marginal or register-restricted. -/
  | marginal
  deriving DecidableEq, Repr

/-- A Slavic language's default polar-question strategy profile. -/
structure PQProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-1 or 639-3 code. -/
  code : String
  /-- Default (unbiased) PQ strategy. -/
  defaultStrategy : PQStrategy
  /-- Particle form (if applicable), derived from Fragment entries where possible. -/
  particle : Option String := none
  /-- Whether DeclPQs are available. -/
  declPQ : DeclPQAvailability := .unavailable
  /-- Whether adding negation triggers epistemic bias. -/
  negationTriggersBias : Bool := true
  deriving Repr, BEq

/-- Czech: verb-initial (VSO) with rising/falling intonation.
No overt PQ particle; the default is InterPPQ. -/
-- UNVERIFIED: ex. 25
def czech : PQProfile :=
  { language := "Czech", code := "cs"
  , defaultStrategy := .verbMovement
  , declPQ := .available }

/-- Slovak: verb-initial, parallel to Czech. -/
-- UNVERIFIED: ex. 26
def slovak : PQProfile :=
  { language := "Slovak", code := "sk"
  , defaultStrategy := .verbMovement
  , declPQ := .available }

/-- Upper Sorbian: verb-initial. -/
-- UNVERIFIED: ex. 27
def upperSorbian : PQProfile :=
  { language := "Upper Sorbian", code := "hsb"
  , defaultStrategy := .verbMovement
  , declPQ := .available }

/-- Slovenian: clause-initial *ali* (optionally) + verb movement.
*ali* is reported as incompatible with DeclPQs. -/
-- UNVERIFIED: ex. 28
def slovenian : PQProfile :=
  { language := "Slovenian", code := "sl"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Slovenian.QuestionParticles.ali.form
  , declPQ := .unavailable }

/-- Ukrainian: clause-initial *čy* (obligatory). -/
-- UNVERIFIED: ex. 29
def ukrainian : PQProfile :=
  { language := "Ukrainian", code := "uk"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Ukrainian.QuestionParticles.cy.form
  , declPQ := .available }

/-- Polish: clause-initial *czy* (obligatory in default PQ).
Verb-initial PQs are possible but unacceptable in quiz scenarios. -/
-- UNVERIFIED: ex. 30
def polish : PQProfile :=
  { language := "Polish", code := "pl"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Polish.QuestionParticles.czy.form
  , declPQ := .marginal }

/-- Serbian: *da* (+ *li*) is the default strategy. Serbian has the
richest PQ repertoire among Slavic languages (see [simik-2024]). -/
-- UNVERIFIED: ex. 31
def serbian : PQProfile :=
  { language := "Serbian", code := "sr"
  , defaultStrategy := .particlePlusMovement
  , particle := some Serbian.QuestionParticles.daLi.form
  , declPQ := .unavailable }

/-- Macedonian: *dali* (clause-initial) for default PQs.
*dali* can introduce negative PQs without triggering bias, unlike
Bulgarian *li*. -/
-- UNVERIFIED: ex. 32
def macedonian : PQProfile :=
  { language := "Macedonian", code := "mk"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Macedonian.QuestionParticles.dali.form
  , declPQ := .unavailable
  , negationTriggersBias := false }

/-- Bulgarian: verb-attached *li*, encliticizing onto the focused
constituent. DeclPQs are colloquial only. -/
-- UNVERIFIED: ex. 33
def bulgarian : PQProfile :=
  { language := "Bulgarian", code := "bg"
  , defaultStrategy := .verbAttachedParticle
  , particle := some Bulgarian.QuestionParticles.li.form
  , declPQ := .marginal }

/-- Russian: verb-attached *li* (formal) or IntonPQ (default).
*li*-PQs are rare in spoken Russian — IntonPQs dominate and are
arguably unbiased (see [simik-2024]). -/
-- UNVERIFIED: ex. 34
def russian : PQProfile :=
  { language := "Russian", code := "ru"
  , defaultStrategy := .intonationOnly
  , particle := some Russian.QuestionParticles.li.form
  , declPQ := .unavailable }

/-- All ten surveyed Slavic PQ profiles. -/
def allProfiles : List PQProfile :=
  [ czech, slovak, upperSorbian, slovenian, ukrainian, polish
  , serbian, macedonian, bulgarian, russian ]

/-- Languages using verb movement as default PQ strategy — the languages
without an overt question particle in default PQs. -/
def verbMovementLanguages : List PQProfile :=
  allProfiles.filter (·.defaultStrategy == .verbMovement)

/-- Languages using a clause-initial particle. -/
def particleLanguages : List PQProfile :=
  allProfiles.filter (·.defaultStrategy == .clauseInitialParticle)

/-- Verb movement languages all have DeclPQs available. -/
theorem verbMovement_implies_declPQ :
    verbMovementLanguages.all (·.declPQ == .available) = true := by decide

/-- Macedonian *dali* introduces negative PQs without triggering epistemic
bias, unlike Bulgarian *li*. -/
theorem dali_negation_unbiased :
    bulgarian.negationTriggersBias = true ∧
    macedonian.negationTriggersBias = false := ⟨rfl, rfl⟩

end Simik2024
