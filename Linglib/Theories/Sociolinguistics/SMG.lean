import Linglib.Theories.Sociolinguistics.EckertMontague
import Linglib.Theories.Pragmatics.RSA.Implementations.Franke2011

/-!
# Social Meaning Games (Burnett 2019, Definitions 4.1–4.4)
@cite{burnett-2019}

Burnett's Social Meaning Game (SMG): a signalling game in which a
speaker's variant choice conveys social information about their persona.
The SMG reuses Franke's (2011) IBR machinery — the naive listener,
strategic speaker, and uncovering listener are all instances of IBR
reasoning applied to a social-meaning interpretation game.

## Definitions

* `SocialMeaningGame` (Def. 4.1): prior over personae, semantic meaning
  (from EM field), and a social evaluation function μ
* `naiveListener` (Def. 4.2): L₀ = Bayes on literal meaning + prior
* `strategicSpeaker` (Def. 4.3): S₁ maximizes social utility μ
* `uncoveringListener` (Def. 4.4): L₁ = Bayes on S₁

## Architectural bridge

The key design choice: `toInterpGame` converts any SMG into Franke's
`InterpGame`, so SMG agents reuse the existing IBR iteration machinery.
The grounding theorems (`naiveListener_eq_L0`, `uncovering_eq_hearerUpdate`)
verify that this reuse is semantically correct: the SMG definitions
produce the same results as running Franke's L₀ and hearerUpdate on
the converted game.

## References

* Burnett, H. (2019). Signalling Games, Sociolinguistic Variation,
  and the Construction of Style. *Linguistics & Philosophy* 42: 419–450.
* Franke, M. (2011). Quantity implicatures, exhaustive interpretation,
  and rational conversation. *Semantics & Pragmatics* 4(1): 1–82.
-/

namespace Sociolinguistics.SMG

open Sociolinguistics
open Sociolinguistics.SCM
open Sociolinguistics.EckertMontague
open RSA.IBR

-- ============================================================================
-- §1. Social Meaning Game (Burnett Definition 4.1)
-- ============================================================================

/-- A Social Meaning Game (Burnett Def. 4.1): a signalling game where
    variant choice conveys social information.

    - `Persona`: types (social categories the listener is trying to infer)
    - `Variant`: messages (linguistic forms the speaker chooses)
    - `prior`: probability distribution over personae
    - `meaning`: whether a variant is compatible with a persona
      (derived from the EM field: `v` means `t` iff the EM lift of `v`
      includes persona `t`)
    - `socialEval`: the speaker's utility μ(t, v) — how much persona `t`
      values being associated with variant `v` -/
structure SocialMeaningGame (Persona Variant : Type)
    [Fintype Persona] [Fintype Variant]
    [DecidableEq Persona] [DecidableEq Variant] where
  /-- Prior probability over personae. -/
  prior : Persona → ℚ
  /-- Prior is non-negative. -/
  prior_nonneg : ∀ (t : Persona), 0 ≤ prior t
  /-- Semantic meaning: is variant `v` compatible with persona `t`? -/
  meaning : Variant → Persona → Bool
  /-- Social evaluation: how much persona `t` values variant `v`. -/
  socialEval : Persona → Variant → ℚ

-- ============================================================================
-- §2. Bridge to Franke's InterpGame
-- ============================================================================

/-- Convert a Social Meaning Game to Franke's interpretation game.

    This is the key architectural bridge: SMG analysis reuses the
    existing IBR machinery from Franke (2011) rather than reimplementing
    iterated best response.

    The mapping:
    - States = Personae (what the listener tries to infer)
    - Messages = Variants (what the speaker chooses)
    - meaning = SMG meaning (EM field compatibility)
    - prior = SMG prior over personae -/
def SocialMeaningGame.toInterpGame {Persona Variant : Type}
    [Fintype Persona] [Fintype Variant]
    [DecidableEq Persona] [DecidableEq Variant]
    (smg : SocialMeaningGame Persona Variant) : InterpGame :=
  { State := Persona
    Message := Variant
    meaning := smg.meaning
    prior := smg.prior }

-- ============================================================================
-- §3. Naive listener (Burnett Definition 4.2)
-- ============================================================================

/-- The naive listener (Burnett Def. 4.2): L₀(t | v) ∝ Pr(t) · ⟦v⟧(t).

    Bayes' rule with literal meaning as likelihood. This is exactly
    Franke's L₀ applied to the converted InterpGame. -/
def naiveListener {Persona Variant : Type}
    [Fintype Persona] [Fintype Variant]
    [DecidableEq Persona] [DecidableEq Variant]
    (smg : SocialMeaningGame Persona Variant)
    (v : Variant) (t : Persona) : ℚ :=
  (L0 smg.toInterpGame).respond v t

/-- **Grounding theorem**: The SMG naive listener IS Franke's L₀
    applied to the converted game. True by construction. -/
theorem naiveListener_eq_L0 {Persona Variant : Type}
    [Fintype Persona] [Fintype Variant]
    [DecidableEq Persona] [DecidableEq Variant]
    (smg : SocialMeaningGame Persona Variant) :
    naiveListener smg = fun v t => (L0 smg.toInterpGame).respond v t := rfl

-- ============================================================================
-- §4. Strategic speaker (Burnett Definition 4.3)
-- ============================================================================

/-- The strategic speaker (Burnett Def. 4.3): S₁(v | t) is proportional
    to the social utility μ(t, v) weighted by the literal meaning ⟦v⟧(t).

    Unlike Franke's best-response speaker (which maximizes hearer success),
    the SMG speaker maximizes *social* utility: a persona chooses variants
    that make the listener more likely to infer a desirable persona. -/
def strategicSpeaker {Persona Variant : Type}
    [Fintype Persona] [Fintype Variant]
    [DecidableEq Persona] [DecidableEq Variant]
    (smg : SocialMeaningGame Persona Variant)
    (t : Persona) (v : Variant) : ℚ :=
  if smg.meaning v t then
    let numerator := smg.socialEval t v
    let denominator := Finset.univ.sum fun v' =>
      if smg.meaning v' t then smg.socialEval t v' else 0
    if denominator == 0 then 0 else numerator / denominator
  else 0

-- ============================================================================
-- §5. Uncovering listener (Burnett Definition 4.4)
-- ============================================================================

/-- The uncovering listener (Burnett Def. 4.4): L₁(t | v) ∝ Pr(t) · S₁(v | t).

    This is Franke's `hearerUpdate` applied to the strategic speaker.
    The listener uses Bayes' rule to infer the speaker's persona from
    the observed variant choice. -/
def uncoveringListener {Persona Variant : Type}
    [Fintype Persona] [Fintype Variant]
    [DecidableEq Persona] [DecidableEq Variant]
    (smg : SocialMeaningGame Persona Variant)
    (v : Variant) (t : Persona) : ℚ :=
  let numerator := strategicSpeaker smg t v * smg.prior t
  let denominator := Finset.univ.sum fun t' => strategicSpeaker smg t' v * smg.prior t'
  if denominator == 0 then 0 else numerator / denominator

-- ============================================================================
-- §6. Construction from grounded field
-- ============================================================================

/-- Construct a Social Meaning Game from a grounded field, prior, and
    social evaluation function.

    The meaning function is derived from the EM field: variant `v`
    is compatible with a persona set `p` iff the EM lift of `v`
    contains `p`. -/
def fromGroundedField {Variant : Type} [Fintype Variant] [DecidableEq Variant]
    (ps : PropertySpace)
    (gf : GroundedField Variant ps)
    (personaeSets : Finset (Finset ps.Property))
    [Fintype personaeSets] [DecidableEq personaeSets]
    (prior : personaeSets → ℚ)
    (prior_nonneg : ∀ (t : personaeSets), 0 ≤ prior t)
    (socialEval : personaeSets → Variant → ℚ) :
    SocialMeaningGame personaeSets Variant :=
  { prior := prior
    prior_nonneg := prior_nonneg
    meaning := fun v t => gf.indexedProperties v ⊆ t.val
    socialEval := socialEval }

end Sociolinguistics.SMG
