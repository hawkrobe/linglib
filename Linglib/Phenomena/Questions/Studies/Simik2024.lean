import Linglib.Theories.Semantics.Questions.QParticleLayer
import Linglib.Fragments.Russian.QuestionParticles
import Linglib.Fragments.Bulgarian.QuestionParticles
import Linglib.Fragments.Ukrainian.QuestionParticles
import Linglib.Fragments.Polish.QuestionParticles
import Linglib.Fragments.Slovenian.QuestionParticles
import Linglib.Fragments.Serbian.QuestionParticles
import Linglib.Fragments.Macedonian.QuestionParticles

/-!
# Šimík (2024): Polar Question Semantics and Bias in Slavic
@cite{simik-2024} @cite{bhatt-dayal-2020} @cite{dayal-2025}

Šimík's cross-Slavic survey of polar-question particles classifies each
particle by its left-peripheral layer in the @cite{bhatt-dayal-2020} /
@cite{dayal-2025} cartography `[SAP [PerspP [CP ...]]]`.

The fragments in `Fragments/{Russian,Bulgarian,Ukrainian,Polish,
Slovenian,Serbian,Macedonian}/QuestionParticles.lean` carry only theory-
neutral lexical primitives (form, gloss, bias profile). This study file
overlays @cite{simik-2024}'s layer assignments and proves the Slavic
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
that the cartography in @cite{dayal-2025} extends beyond Hindi-Urdu and
Japanese to a much wider typological range.
-/

namespace Phenomena.Questions.Studies.Simik2024

open Semantics.Questions (QParticleLayer)

/-! ## Layer assignment for each Slavic Q-particle.

Each `def` records Šimík's classification of a Fragment particle. The
`_` argument is unused because the layer assignment is a theoretical
overlay on the particle, not a computed property of its lexical fields. -/

def russianLi_layer        (_ : Fragments.Russian.QuestionParticles.QParticleEntry)    : QParticleLayer := .cp
def russianRazve_layer     (_ : Fragments.Russian.QuestionParticles.QParticleEntry)    : QParticleLayer := .perspP
def bulgarianLi_layer      (_ : Fragments.Bulgarian.QuestionParticles.QParticleEntry)  : QParticleLayer := .cp
def bulgarianNima_layer    (_ : Fragments.Bulgarian.QuestionParticles.QParticleEntry)  : QParticleLayer := .perspP
def ukrainianCy_layer      (_ : Fragments.Ukrainian.QuestionParticles.QParticleEntry)  : QParticleLayer := .cp
def ukrainianXiba_layer    (_ : Fragments.Ukrainian.QuestionParticles.QParticleEntry)  : QParticleLayer := .perspP
def polishCzy_layer        (_ : Fragments.Polish.QuestionParticles.QParticleEntry)     : QParticleLayer := .cp
def polishCzyzby_layer     (_ : Fragments.Polish.QuestionParticles.QParticleEntry)     : QParticleLayer := .perspP
def slovenianAli_layer     (_ : Fragments.Slovenian.QuestionParticles.QParticleEntry)  : QParticleLayer := .cp
def serbianDaLi_layer      (_ : Fragments.Serbian.QuestionParticles.QParticleEntry)    : QParticleLayer := .cp
def serbianZar_layer       (_ : Fragments.Serbian.QuestionParticles.QParticleEntry)    : QParticleLayer := .perspP
def macedonianDali_layer   (_ : Fragments.Macedonian.QuestionParticles.QParticleEntry) : QParticleLayer := .cp

/-! ## Cross-Slavic generalizations -/

open Fragments.Russian.QuestionParticles    in
open Fragments.Bulgarian.QuestionParticles  in
open Fragments.Ukrainian.QuestionParticles  in
open Fragments.Polish.QuestionParticles     in
open Fragments.Slovenian.QuestionParticles  in
open Fragments.Serbian.QuestionParticles    in
open Fragments.Macedonian.QuestionParticles in
/-- The neutral polar-question particle of every surveyed Slavic language
    sits at CP. The fragment-level evidence that this is the *neutral*
    particle is the conjunction of `requiresEvidentialBias = false` and
    `requiresEpistemicBias = false`. -/
theorem neutral_PQ_particles_are_CP :
    russianLi_layer Fragments.Russian.QuestionParticles.li = .cp ∧
    bulgarianLi_layer Fragments.Bulgarian.QuestionParticles.li = .cp ∧
    ukrainianCy_layer Fragments.Ukrainian.QuestionParticles.cy = .cp ∧
    polishCzy_layer Fragments.Polish.QuestionParticles.czy = .cp ∧
    slovenianAli_layer Fragments.Slovenian.QuestionParticles.ali = .cp ∧
    serbianDaLi_layer Fragments.Serbian.QuestionParticles.daLi = .cp ∧
    macedonianDali_layer Fragments.Macedonian.QuestionParticles.dali = .cp :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

open Fragments.Russian.QuestionParticles    in
open Fragments.Bulgarian.QuestionParticles  in
open Fragments.Ukrainian.QuestionParticles  in
open Fragments.Polish.QuestionParticles     in
open Fragments.Serbian.QuestionParticles    in
/-- The cross-Slavic *RAZVE* family — the mirative/dubitative particles
    that signal conflict between speaker's prior epistemic state and
    incoming contextual evidence — uniformly sits at PerspP. -/
theorem razve_family_is_PerspP :
    russianRazve_layer Fragments.Russian.QuestionParticles.razve_ = .perspP ∧
    bulgarianNima_layer Fragments.Bulgarian.QuestionParticles.nima = .perspP ∧
    ukrainianXiba_layer Fragments.Ukrainian.QuestionParticles.xiba = .perspP ∧
    polishCzyzby_layer Fragments.Polish.QuestionParticles.czyzby = .perspP ∧
    serbianZar_layer Fragments.Serbian.QuestionParticles.zar_ = .perspP :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Bridge between the layer assignment and the bias profile recorded
    in the fragments: every PerspP-layer Slavic particle in this study
    requires evidential bias, while every CP-layer particle does not. -/
theorem layer_correlates_with_bias :
    Fragments.Russian.QuestionParticles.li.requiresEvidentialBias = false ∧
    Fragments.Russian.QuestionParticles.razve_.requiresEvidentialBias = true ∧
    Fragments.Bulgarian.QuestionParticles.li.requiresEvidentialBias = false ∧
    Fragments.Bulgarian.QuestionParticles.nima.requiresEvidentialBias = true ∧
    Fragments.Ukrainian.QuestionParticles.cy.requiresEvidentialBias = false ∧
    Fragments.Ukrainian.QuestionParticles.xiba.requiresEvidentialBias = true ∧
    Fragments.Polish.QuestionParticles.czy.requiresEvidentialBias = false ∧
    Fragments.Polish.QuestionParticles.czyzby.requiresEvidentialBias = true ∧
    Fragments.Serbian.QuestionParticles.daLi.requiresEvidentialBias = false ∧
    Fragments.Serbian.QuestionParticles.zar_.requiresEvidentialBias = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Phenomena.Questions.Studies.Simik2024
