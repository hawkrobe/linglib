import Linglib.Features.QParticleLayer
import Linglib.Semantics.Questions.Singleton
import Linglib.Fragments.HindiUrdu.Particles
import Linglib.Fragments.Japanese.Particles
import Linglib.Fragments.English.QuestionParticles

/-!
# Bhatt & Dayal (2020): PQP analysis of Hindi-Urdu *kya:* [bhatt-dayal-2020]

Polar Question Particle analysis: Hindi-Urdu *kya:* sits at PerspP, not CP.
Combined with [dayal-2025]'s three-layer cartography
`[SAP [PerspP [CP ...]]]` and [sauerland-yatsushiro-2017]'s analysis
of Japanese *kke* as a meta question particle (MQP).

This study file is the canonical home for the layer assignments of
the four typologically representative particles that motivate the
three-way `cp / perspP / sap` split:

| Layer  | Language    | Particle        | Distribution         |
|--------|-------------|-----------------|----------------------|
| CP     | Japanese    | *ka*            | matrix + subord + QS |
| PerspP | Hindi-Urdu  | *kya:*          | matrix + QS, no sub  |
| SAP    | Japanese    | *kke*           | matrix + quotation   |
| SAP    | English     | *quick(ly)*     | matrix only          |

The layer of each particle is DERIVED from its fragment's
embedding-distribution facet by `layerOf` — the cartography's defining
correlation (layer ↔ embedding distribution), stated once as a
classifier rather than stipulated per particle.
-/

namespace BhattDayal2020

open Features (QParticleLayer)
open Question (IsSingleton SingletonQuestion declarative polar
  isSingleton_declarative not_isSingleton_polar_of_nontrivial)
open HindiUrdu.Particles (kya)
open Japanese.Particles (ka kke)
open English.QuestionParticles (quick)

-- ============================================================================
-- §1 — The layer classifier (derived, not stipulated)
-- ============================================================================

/-- The [dayal-2025] cartography's defining correlation, as a
    classifier: a question particle's left-peripheral layer is read off
    its embedding distribution — subordinated-licensed → CP
    (clause-typing); subordinated-excluded but quasi-subordinated-
    licensed → PerspP; quasi-subordinated-excluded but matrix-licensed →
    SAP. Defined for question particles only — Japanese *koto* (a
    declarative complementizer, kept in the fragment for the *ka*
    contrast at [dayal-2025] (15)) is outside its intended domain. -/
def layerOf (p : Particle) : Option QParticleLayer :=
  if p.LicensedInEmbed .subordinated then some .cp
  else if p.LicensedInEmbed .quasiSubordinated then some .perspP
  else if p.LicensedInEmbed .matrix then some .sap
  else none

/-- `layerOf`'s intended domain: the question particles this study
    classifies. Membership is a claim about what the particle *does*
    (question-forming), not about its distribution — Japanese *koto*
    (declarative complementizer) has an embedding facet but is
    deliberately outside. -/
def qParticles : List Particle := [ka, kya, kke, quick]

/-- The four representative layer assignments, DERIVED from the
    fragments' embedding facets: *ka* CP ([dayal-2025]), *kya:* PerspP
    ([bhatt-dayal-2020]), *kke* SAP ([sauerland-yatsushiro-2017]),
    *quick* SAP ([dayal-2025] ex. (19)). Formerly four stipulated
    constants; now one classifier plus kernel-checked facts. -/
theorem layers_derived :
    layerOf ka = some .cp ∧
    layerOf kya = some .perspP ∧
    layerOf kke = some .sap ∧
    layerOf quick = some .sap := by decide

/-- Every particle in the classifier's domain receives a layer. -/
theorem qParticles_layered : ∀ p ∈ qParticles, (layerOf p).isSome := by decide

-- ============================================================================
-- §2 — Singleton-Alternative Presupposition (eq. 23)
-- ============================================================================

/-! [bhatt-dayal-2020] eq. 23:
`⟦kya:⟧ = λp[∃q ∈ Q[∀q′[q′ ∈ Q → q′ = q]].Q`
i.e. *kya:* is interpreted only when its sister question `Q` has a
singleton alternative set, in which case the particle is the identity
on `Q`. The presupposition is exactly `Question.IsSingleton`; the
well-typed analogue of "felicitous sister content" is the subtype
`SingletonQuestion W` (a question paired with a proof that its
alternative set is a singleton). The "highlighted" terminology of
[roelofsen-farkas-2015] corresponds to `declarative p` in this
setting (one-cell denotation, in contrast to the two-cell `polar p`).

[bhatt-dayal-2020] fn. 11 cites the parallel Mandarin *nandao*
analysis as the model for kya:; the shared `IsSingleton` predicate
captures that convergence by construction. See
`Zheng2025` for the nandao binding. -/

universe u
variable {W : Type u}

/-- **Empirical prediction (felicitous case)**: kya: composes
    felicitously with a one-cell "highlighted" polar — i.e. with the
    declarative content `declarative p`, the singleton-alternative
    analogue of the standard two-cell polar. The canonical good input. -/
theorem kya_felicitous_declarative (p : Set W) :
    IsSingleton (declarative (W := W) p) :=
  isSingleton_declarative p

/-- **Empirical prediction (defined case)**: kya: on a felicitous
    sister returns the question unchanged — packaged as a
    `SingletonQuestion` whose underlying issue is the input declarative.
    Mathlib pattern: subtype + `.val` rather than `Option`. -/
theorem kya_interp_declarative (p : Set W) :
    (SingletonQuestion.ofDeclarative (W := W) p).issue = declarative p := rfl

/-- **Empirical prediction (infelicitous case)**: kya: cannot license
    a two-cell Hamblin polar with a non-trivial proposition — the
    presupposition fails because such a polar has two alternatives. -/
theorem kya_infelicitous_two_cell_polar {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    ¬ IsSingleton (polar (W := W) p) :=
  not_isSingleton_polar_of_nontrivial hne hnu

/-- **Bridge to fragment**: the PerspP layer derived from kya:'s
    embedding facet (`layers_derived`) is the surface signal of the
    singleton-presupposition analysis — the PerspP-layer particle is
    the one whose interpretation is given by the `IsSingleton`
    presupposition + identity on `SingletonQuestion`. -/
theorem kya_perspP_signals_singletonPresup :
    layerOf kya = some .perspP := layers_derived.2.1

end BhattDayal2020
