import Linglib.Semantics.Questions.Bias
import Linglib.Fragments.Slavic.Russian.QuestionParticles
import Linglib.Fragments.Slavic.Bulgarian.QuestionParticles
import Linglib.Fragments.Slavic.Ukrainian.QuestionParticles
import Linglib.Fragments.Slavic.Polish.QuestionParticles
import Linglib.Fragments.Slavic.Slovenian.QuestionParticles
import Linglib.Fragments.Slavic.Serbian.QuestionParticles
import Linglib.Fragments.Slavic.Macedonian.QuestionParticles
import Linglib.Fragments.Slavic.Czech.Particles

/-!
# Šimík (2024): Polar Question Semantics and Bias in Slavic
[simik-2024] [esipova-romero-2023]

Šimík's survey of polar-question semantics and bias across Slavic. §4.1
diagnoses each language's default (unbiased) PQ strategy by felicity in
a quiz scenario (ex. 24) — a TV moderator's question conveying no clue
about the answer — for ten languages (exx. 25–34). §4.2.4 surveys the
Russian mirative/dubitative particle *razve*, a conflict-resolving
particle presupposing contextual evidence for the prejacent against a
prior epistemic bias for its negation, and lists its kin across Slavic,
whose formal properties the chapter leaves open.

## Main declarations

* `PQProfile`, `allProfiles` — the §4.1 quiz-diagnosed strategy
  profiles of the ten surveyed languages.
* `razveFamily`, `evidentialRequirement`, `razveOriginalBias` — the
  §4.2.4 kin list and razve's bias profile.
* `razve_root_li_embedded`, `verbMovement_implies_declPQ`,
  `particle_NPQs_unbiased` — cross-Slavic generalizations over the
  fragments and profiles.
-/

namespace Simik2024

open Russian.QuestionParticles (li razve_)

/-! ### The razve family (§4.2.4)

Russian *razve* marks a conflict-resolving polar question: contextual
evidence supports the prejacent while the speaker's prior epistemic
state favored its negation ('Do you (really) speak Russian? [I thought
that you didn't.]', ex. 39). The chapter reports kin of similar meaning
across Slavic — Ukrainian *xiba*, Polish *czyż(by)*, Bulgarian *nima*,
Macedonian and Serbian *zar*, Czech *co(ž)pak* — while leaving their
precise semantics open. -/

/-- The §4.2.4 kin list: the cross-Slavic mirative/dubitative family. -/
def razveFamily : List Particle :=
  [razve_, Ukrainian.QuestionParticles.xiba, Polish.QuestionParticles.czyzby,
   Bulgarian.QuestionParticles.nima, Macedonian.QuestionParticles.zar,
   Serbian.QuestionParticles.zar_, Czech.Particles.copak]

/-- Contextual-evidence requirement: *razve* presupposes evidential bias
for the prejacent (§4.2.4), extended here to the kin the chapter reports
as similar in meaning. -/
def evidentialRequirement (p : Particle) :
    Option Semantics.Questions.Bias.ContextualEvidence :=
  if p ∈ razveFamily then some .forP else none

/-- *Razve*'s prior epistemic bias runs against the prejacent — the
'I thought that ¬p' component of exx. 39 and 42. -/
def razveOriginalBias : Option Semantics.Questions.Bias.OriginalBias :=
  some .againstP

/-- *Razve* is a root phenomenon while *li* is obligatory in subordinated
polar questions (§4.2.4) — read off the fragment cells. -/
theorem razve_root_li_embedded :
    ¬ razve_.LicensedInEmbed .subordinated ∧
      li.Licensed .polar .subordinated := by decide

/-! ### Default PQ strategies (§4.1)

The quiz scenario (ex. 24) diagnoses the default (unbiased) PQ strategy
of each language; strategies conveying epistemic or evidential bias are
infelicitous in it. `particle` fields are derived from Fragment
entries. -/

/-- How a language formally encodes its default (unbiased) polar question. -/
inductive PQStrategy where
  /-- Verb movement to clause-initial position (subject–verb inversion). -/
  | verbMovement
  /-- Clause-initial question particle. -/
  | clauseInitialParticle
  /-- Particle attached to the verb (or focused constituent). -/
  | verbAttachedParticle
  /-- Combination of particle + verb movement (the Macedonian V+*li*
      alternative, ex. 32b). -/
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
  /-- Whether adding negation to the default strategy triggers epistemic bias. -/
  negationTriggersBias : Bool := true
  deriving Repr, BEq

/-- Czech: obligatory verb movement (ex. 25); negation triggers positive
epistemic bias; DeclPQs convey evidential bias. -/
def czech : PQProfile :=
  { language := "Czech", code := "cs"
  , defaultStrategy := .verbMovement
  , declPQ := .available }

/-- Slovak: verb movement, parallel to Czech (ex. 26). -/
def slovak : PQProfile :=
  { language := "Slovak", code := "sk"
  , defaultStrategy := .verbMovement
  , declPQ := .available }

/-- Upper Sorbian: verb movement, fronting the auxiliary (ex. 27). -/
def upperSorbian : PQProfile :=
  { language := "Upper Sorbian", code := "hsb"
  , defaultStrategy := .verbMovement
  , declPQ := .available }

/-- Slovenian: verb movement with optional clause-initial *ali*
(ex. 28); *ali* is incompatible with DeclPQs. -/
def slovenian : PQProfile :=
  { language := "Slovenian", code := "sl"
  , defaultStrategy := .verbMovement
  , particle := some Slovenian.QuestionParticles.ali.form
  , declPQ := .available }

/-- Ukrainian: obligatory clause-initial *čy* (ex. 29); DeclPQs convey
evidential bias. -/
def ukrainian : PQProfile :=
  { language := "Ukrainian", code := "uk"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Ukrainian.QuestionParticles.cy.form
  , declPQ := .available }

/-- Polish: obligatory clause-initial *czy* (ex. 30); czy-NPQs remain
quiz-felicitous (ex. 30b), so negation does not trigger bias; DeclPQs
convey evidential bias. -/
def polish : PQProfile :=
  { language := "Polish", code := "pl"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Polish.QuestionParticles.czy.form
  , declPQ := .available
  , negationTriggersBias := false }

/-- Serbian: clause-initial *da* + clitic *li* (ex. 31a); negative and
declarative PQs convey biases. -/
def serbian : PQProfile :=
  { language := "Serbian", code := "sr"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Serbian.QuestionParticles.daLi.form
  , declPQ := .available }

/-- Macedonian: clause-initial *dali* (ex. 32a), which admits negation
without triggering bias, unlike Bulgarian *li*. -/
def macedonian : PQProfile :=
  { language := "Macedonian", code := "mk"
  , defaultStrategy := .clauseInitialParticle
  , particle := some Macedonian.QuestionParticles.dali.form
  , declPQ := .unavailable
  , negationTriggersBias := false }

/-- Bulgarian: *li* encliticized onto the focused constituent (ex. 33);
DeclPQs convey evidential bias. -/
def bulgarian : PQProfile :=
  { language := "Bulgarian", code := "bg"
  , defaultStrategy := .verbAttachedParticle
  , particle := some Bulgarian.QuestionParticles.li.form
  , declPQ := .available }

/-- Russian: quiz PQs use verb-attached *li* (ex. 34); colloquially
IntonPQs dominate and are arguably unbiased, though they can also be
used rhetorically ([esipova-romero-2023]); DeclPQs are hard to
distinguish from IntonPQs. -/
def russian : PQProfile :=
  { language := "Russian", code := "ru"
  , defaultStrategy := .verbAttachedParticle
  , particle := some Russian.QuestionParticles.li.form
  , declPQ := .available }

/-- All ten surveyed Slavic PQ profiles. -/
def allProfiles : List PQProfile :=
  [ czech, slovak, upperSorbian, slovenian, ukrainian, polish
  , serbian, macedonian, bulgarian, russian ]

/-- Languages using verb movement as default PQ strategy — the languages
without an obligatory question particle in default PQs. -/
def verbMovementLanguages : List PQProfile :=
  allProfiles.filter (·.defaultStrategy == .verbMovement)

/-- Languages using a clause-initial particle. -/
def particleLanguages : List PQProfile :=
  allProfiles.filter (·.defaultStrategy == .clauseInitialParticle)

/-- Verb movement languages all have DeclPQs available. -/
theorem verbMovement_implies_declPQ :
    verbMovementLanguages.all (·.declPQ == .available) = true := by decide

/-- Under their clause-initial particles, Polish and Macedonian negative
PQs stay quiz-felicitous (exx. 30b, 32a), unlike Bulgarian li-NPQs
(ex. 33b). -/
theorem particle_NPQs_unbiased :
    polish.negationTriggersBias = false ∧
    macedonian.negationTriggersBias = false ∧
    bulgarian.negationTriggersBias = true := ⟨rfl, rfl, rfl⟩

end Simik2024
