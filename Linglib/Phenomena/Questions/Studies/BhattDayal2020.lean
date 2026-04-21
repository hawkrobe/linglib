import Linglib.Theories.Semantics.Questions.QParticleLayer
import Linglib.Core.Question.Singleton
import Linglib.Fragments.HindiUrdu.Particles
import Linglib.Fragments.Japanese.Particles
import Linglib.Fragments.English.QuestionParticles

/-!
# Bhatt & Dayal (2020): PQP analysis of Hindi-Urdu *kya:* @cite{bhatt-dayal-2020}

Polar Question Particle analysis: Hindi-Urdu *kya:* sits at PerspP, not CP.
Combined with @cite{dayal-2025}'s three-layer cartography
`[SAP [PerspP [CP ...]]]` and @cite{sauerland-yatsushiro-2017}'s analysis
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

The layer assignments are theoretical overlays on the fragment particles —
the fragments themselves carry only theory-neutral distributional fields.
-/

namespace Phenomena.Questions.TypologyBridge

open Semantics.Questions (QParticleLayer)
open Core.Question (IsSingleton SingletonQuestion declarative polar
  isSingleton_declarative not_isSingleton_polar_of_nontrivial)
open Fragments.HindiUrdu.Particles (kya)
open Fragments.Japanese.Particles (ka kke)
open Fragments.English.QuestionParticles (quick)

-- ============================================================================
-- §1 — Layer Assignments (per-paper theoretical overlay)
-- ============================================================================

/-- Bhatt & Dayal (2020): Hindi-Urdu *kya:* sits at PerspP. -/
def hindi_urdu_kya_layer (_ : Fragments.HindiUrdu.Particles.ParticleEntry) :
    QParticleLayer := .perspP

/-- @cite{dayal-2025}: Japanese *ka* is the canonical CP-layer Q-morpheme. -/
def japanese_ka_layer (_ : Fragments.Japanese.Particles.ParticleEntry) :
    QParticleLayer := .cp

/-- @cite{sauerland-yatsushiro-2017}: Japanese *kke* is an MQP at SAP. -/
def japanese_kke_layer (_ : Fragments.Japanese.Particles.ParticleEntry) :
    QParticleLayer := .sap

/-- @cite{dayal-2025} ex. (19): English *quick/quickly* is an MQP-adverb at SAP. -/
def english_quick_layer (_ : Fragments.English.QuestionParticles.QParticleEntry) :
    QParticleLayer := .sap

-- ============================================================================
-- §2 — Q-Particle Datum (Fragment-driven typology row)
-- ============================================================================

/-- A row in the cross-linguistic Q-particle typology: a Fragment particle
    plus its theoretical layer assignment and a language label. -/
structure QParticleDatum where
  language : String
  form : String
  layer : QParticleLayer
  /-- Appears in matrix questions? -/
  inMatrix : Bool
  /-- Appears in subordinated interrogatives? -/
  inSubordinated : Bool
  /-- Appears in quasi-subordinated interrogatives? -/
  inQuasiSub : Bool
  /-- Appears in quotations? -/
  inQuotation : Bool
  deriving Repr

/-- Japanese *ka* — clause-typing particle (CP). -/
def japanese_ka : QParticleDatum where
  language := "Japanese"
  form := ka.romaji
  layer := japanese_ka_layer ka
  inMatrix := ka.inMatrix
  inSubordinated := ka.inSubordinated
  inQuasiSub := ka.inQuasiSub
  -- Japanese ka is grammatical in quotation (subsumed by inSubordinated/inMatrix in fragment).
  inQuotation := true

/-- Hindi-Urdu *kya:* — polar question particle (PerspP). -/
def hindi_urdu_kya : QParticleDatum where
  language := "Hindi-Urdu"
  form := kya.form
  layer := hindi_urdu_kya_layer kya
  -- kya is a PQP licensed in matrix + quasi-sub but not in subordinated clauses.
  inMatrix := true
  inSubordinated := kya.inSubordinated
  inQuasiSub := kya.inQuasiSub
  inQuotation := false

/-- Japanese *kke* — meta question particle (SAP). -/
def japanese_kke : QParticleDatum where
  language := "Japanese"
  form := kke.romaji
  layer := japanese_kke_layer kke
  inMatrix := kke.inMatrix
  inSubordinated := kke.inSubordinated
  inQuasiSub := kke.inQuasiSub
  -- @cite{sauerland-yatsushiro-2017}: kke is licensed in quotation as well as matrix.
  inQuotation := true

/-- English *quick/quickly* — MQP-like adverb (SAP). -/
def english_quick : QParticleDatum where
  language := "English"
  form := quick.form
  layer := english_quick_layer quick
  inMatrix := quick.inMatrix
  inSubordinated := quick.inSubordinated
  inQuasiSub := quick.inQuasiSub
  inQuotation := quick.inQuotation

def allQParticleData : List QParticleDatum :=
  [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick]

-- ============================================================================
-- §3 — Typology Theorems (layer ⇒ embedding distribution)
-- ============================================================================

/-- CP-layer particles appear in subordinated position. -/
theorem cp_particles_in_subordination :
    ∀ d ∈ allQParticleData,
      d.layer = .cp → d.inSubordinated = true := by
  intro d hd _
  simp [allQParticleData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp_all [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick,
              japanese_ka_layer, hindi_urdu_kya_layer, japanese_kke_layer,
              english_quick_layer, ka, kya, kke, quick]

/-- PerspP-layer particles do NOT appear in subordinated position. -/
theorem perspP_particles_not_in_subordination :
    ∀ d ∈ allQParticleData,
      d.layer = .perspP → d.inSubordinated = false := by
  intro d hd _
  simp [allQParticleData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp_all [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick,
              japanese_ka_layer, hindi_urdu_kya_layer, japanese_kke_layer,
              english_quick_layer, ka, kya, kke, quick]

/-- SAP-layer particles do NOT appear in quasi-subordinated position. -/
theorem sap_particles_not_in_quasi_sub :
    ∀ d ∈ allQParticleData,
      d.layer = .sap → d.inQuasiSub = false := by
  intro d hd _
  simp [allQParticleData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp_all [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick,
              japanese_ka_layer, hindi_urdu_kya_layer, japanese_kke_layer,
              english_quick_layer, ka, kya, kke, quick]

-- ============================================================================
-- §4 — Singleton-Alternative Presupposition (eq. 23)
-- ============================================================================

/-! @cite{bhatt-dayal-2020} eq. 23:
`⟦kya:⟧ = λp[∃q ∈ Q[∀q′[q′ ∈ Q → q′ = q]].Q`
i.e. *kya:* is interpreted only when its sister question `Q` has a
singleton alternative set, in which case the particle is the identity
on `Q`. The presupposition is exactly `Core.Question.IsSingleton`; the
well-typed analogue of "felicitous sister content" is the subtype
`SingletonQuestion W` (a question paired with a proof that its
alternative set is a singleton). The "highlighted" terminology of
@cite{roelofsen-farkas-2015} corresponds to `declarative p` in this
setting (one-cell denotation, in contrast to the two-cell `polar p`).

@cite{bhatt-dayal-2020} fn. 11 cites the parallel Mandarin *nandao*
analysis as the model for kya:; the shared `IsSingleton` predicate
captures that convergence by construction. See
`Phenomena.Questions.Studies.Zheng2025` for the nandao binding. -/

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

/-- **Bridge to fragment**: the kya: entry's `polarQuestion` field is
    the surface signal of the singleton-presupposition analysis — the
    fragment data field flags the particle whose interpretation is
    given by the `IsSingleton` presupposition + identity on
    `SingletonQuestion`. -/
theorem kya_polarQuestion_signals_singletonPresup :
    Fragments.HindiUrdu.Particles.kya.polarQuestion = true := rfl

end Phenomena.Questions.TypologyBridge
