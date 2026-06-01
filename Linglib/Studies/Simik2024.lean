import Linglib.Features.QParticleLayer
import Linglib.Fragments.Slavic.Russian.QuestionParticles
import Linglib.Fragments.Slavic.Bulgarian.QuestionParticles
import Linglib.Fragments.Slavic.Ukrainian.QuestionParticles
import Linglib.Fragments.Slavic.Polish.QuestionParticles
import Linglib.Fragments.Slavic.Slovenian.QuestionParticles
import Linglib.Fragments.Slavic.Serbian.QuestionParticles
import Linglib.Fragments.Slavic.Macedonian.QuestionParticles

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

namespace Simik2024

open Features (QParticleLayer)

/-! ## Layer assignment for each Slavic Q-particle.

Each `def` records Šimík's classification of a Fragment particle. The
`_` argument is unused because the layer assignment is a theoretical
overlay on the particle, not a computed property of its lexical fields. -/

def russianLi_layer        (_ : Russian.QuestionParticles.QParticleEntry)    : QParticleLayer := .cp
def russianRazve_layer     (_ : Russian.QuestionParticles.QParticleEntry)    : QParticleLayer := .perspP
def bulgarianLi_layer      (_ : Bulgarian.QuestionParticles.QParticleEntry)  : QParticleLayer := .cp
def bulgarianNima_layer    (_ : Bulgarian.QuestionParticles.QParticleEntry)  : QParticleLayer := .perspP
def ukrainianCy_layer      (_ : Ukrainian.QuestionParticles.QParticleEntry)  : QParticleLayer := .cp
def ukrainianXiba_layer    (_ : Ukrainian.QuestionParticles.QParticleEntry)  : QParticleLayer := .perspP
def polishCzy_layer        (_ : Polish.QuestionParticles.QParticleEntry)     : QParticleLayer := .cp
def polishCzyzby_layer     (_ : Polish.QuestionParticles.QParticleEntry)     : QParticleLayer := .perspP
def slovenianAli_layer     (_ : Slovenian.QuestionParticles.QParticleEntry)  : QParticleLayer := .cp
def serbianDaLi_layer      (_ : Serbian.QuestionParticles.QParticleEntry)    : QParticleLayer := .cp
def serbianZar_layer       (_ : Serbian.QuestionParticles.QParticleEntry)    : QParticleLayer := .perspP
def macedonianDali_layer   (_ : Macedonian.QuestionParticles.QParticleEntry) : QParticleLayer := .cp

/-! ## Cross-Slavic generalizations -/

open Russian.QuestionParticles    in
open Bulgarian.QuestionParticles  in
open Ukrainian.QuestionParticles  in
open Polish.QuestionParticles     in
open Slovenian.QuestionParticles  in
open Serbian.QuestionParticles    in
open Macedonian.QuestionParticles in
/-- The neutral polar-question particle of every surveyed Slavic language
    sits at CP. The fragment-level evidence that this is the *neutral*
    particle is the conjunction of `requiresEvidentialBias = false` and
    `requiresEpistemicBias = false`. -/
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

/-- Bridge between the layer assignment and the bias profile recorded
    in the fragments: every PerspP-layer Slavic particle in this study
    requires evidential bias, while every CP-layer particle does not. -/
theorem layer_correlates_with_bias :
    Russian.QuestionParticles.li.requiresEvidentialBias = false ∧
    Russian.QuestionParticles.razve_.requiresEvidentialBias = true ∧
    Bulgarian.QuestionParticles.li.requiresEvidentialBias = false ∧
    Bulgarian.QuestionParticles.nima.requiresEvidentialBias = true ∧
    Ukrainian.QuestionParticles.cy.requiresEvidentialBias = false ∧
    Ukrainian.QuestionParticles.xiba.requiresEvidentialBias = true ∧
    Polish.QuestionParticles.czy.requiresEvidentialBias = false ∧
    Polish.QuestionParticles.czyzby.requiresEvidentialBias = true ∧
    Serbian.QuestionParticles.daLi.requiresEvidentialBias = false ∧
    Serbian.QuestionParticles.zar_.requiresEvidentialBias = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Simik2024
