import Linglib.Theories.Syntax.Minimalist.Ellipsis.DeletionDomain
import Linglib.Theories.Syntax.Minimalist.Voice

/-!
# @cite{merchant-2013} — Voice and Ellipsis

Voice mismatches between an elided phrase and its antecedent are tolerated
under VP-ellipsis but blocked under sluicing, fragment answers, gapping,
and stripping. This *uneven distribution* follows from the structural
position of VoiceP relative to the [E]-bearing head.

## Core Insight

VP-ellipsis targets vP (complement of Voice), so Voice is *external* to
the ellipsis site — mismatches are invisible to the identity condition.
Sluicing and other clausal ellipses target TP (which *contains* VoiceP),
so Voice is *internal* — mismatches violate identity.

## Argument Structure Alternations (§3.3)

No argument structure alternation — causative/inchoative, dative, middle,
prepositional — is tolerated under *any* kind of ellipsis. The heads
regulating these alternations all sit at or below v, hence are always
inside the deletion domain regardless of ellipsis height.

## Formalization

Every grammaticality judgment is verified against `canMismatch` from
`DeletionDomain.lean`. Cross-linguistic data (German, Greek) supplements
the English paradigm.
-/

namespace Merchant2013

open Minimalist
open Minimalist.Ellipsis

-- ════════════════════════════════════════════════════
-- § 1. Ellipsis Types Beyond VPE and Sluicing
-- ════════════════════════════════════════════════════

/-- Fragment answers: movement to Spec,CP + TP-deletion.
    Same [E] position as sluicing (@cite{merchant-2004}). -/
def fragmentAnswers : EllipsisType := ⟨.C, "fragment answers"⟩

/-- Gapping: elides material containing VoiceP. [E] at C or higher. -/
def gapping : EllipsisType := ⟨.C, "gapping"⟩

/-- Stripping (bare argument ellipsis): subcase of gapping. -/
def stripping : EllipsisType := ⟨.C, "stripping"⟩

/-- Pseudogapping: remnant extracted from vP; deletion domain includes
    VoiceP. [E] at T or higher. -/
def pseudogapping : EllipsisType := ⟨.T, "pseudogapping"⟩

-- ════════════════════════════════════════════════════
-- § 2. Voice Mismatch Data
-- ════════════════════════════════════════════════════

/-- A voice mismatch datum across an ellipsis boundary. -/
structure VoiceMismatchDatum where
  description : String
  antecedentVoice : VoiceFlavor
  targetVoice : VoiceFlavor
  ellipsisType : EllipsisType
  grammatical : Bool
  language : String := "English"
  deriving Repr

-- § 2.1 VP-ellipsis: voice mismatches tolerated (§1.1, exx. 1–2)

/-- (1a) Active → passive under VPE.
    "The janitor must remove the trash whenever it is apparent
     that it should be ⟨removed⟩." -/
def ex1a : VoiceMismatchDatum :=
  { description := "Active → passive under VPE"
    antecedentVoice := .agentive, targetVoice := .passive
    ellipsisType := englishVPE, grammatical := true }

/-- (2a) Passive → active under VPE.
    "The system can be used by anyone who wants to ⟨use it⟩." -/
def ex2a : VoiceMismatchDatum :=
  { description := "Passive → active under VPE"
    antecedentVoice := .passive, targetVoice := .agentive
    ellipsisType := englishVPE, grammatical := true }

-- § 2.2 Sluicing: voice mismatches blocked (§1.2, exx. 5–7, 25)

/-- (5) "*Joe was murdered, but we don't know who." -/
def ex5 : VoiceMismatchDatum :=
  { description := "Sluicing: pass → act blocked"
    antecedentVoice := .passive, targetVoice := .agentive
    ellipsisType := sluicing, grammatical := false }

/-- (6a) German: "*Erika hat jemanden ermordet, aber sie wissen nicht, wer." -/
def ex6a : VoiceMismatchDatum :=
  { description := "German sluicing: act → pass blocked"
    antecedentVoice := .agentive, targetVoice := .passive
    ellipsisType := sluicing, grammatical := false, language := "German" }

/-- (25a) Greek: "*O Jannis skotose kapjon, ala δen kserume pjos." -/
def ex25a : VoiceMismatchDatum :=
  { description := "Greek sluicing: act → pass blocked (synthetic)"
    antecedentVoice := .agentive, targetVoice := .passive
    ellipsisType := sluicing, grammatical := false, language := "Greek" }

-- § 2.3 Fragment answers (§1.2, ex. 9)

/-- (9a) German: "Wer hat den Jungen untersucht? — *Von einer Psychologin." -/
def ex9a : VoiceMismatchDatum :=
  { description := "Fragment: act → pass blocked"
    antecedentVoice := .agentive, targetVoice := .passive
    ellipsisType := fragmentAnswers, grammatical := false, language := "German" }

-- § 2.4 Gapping (§1.2, ex. 10)

/-- (10a) "*Some bring roses and lilies by others." -/
def ex10a : VoiceMismatchDatum :=
  { description := "Gapping: act → pass blocked"
    antecedentVoice := .agentive, targetVoice := .passive
    ellipsisType := gapping, grammatical := false }

-- § 2.5 Stripping (§1.2, ex. 11)

/-- (11a) "*MAX brought the roses, not by AMY!" -/
def ex11a : VoiceMismatchDatum :=
  { description := "Stripping: act → pass blocked"
    antecedentVoice := .agentive, targetVoice := .passive
    ellipsisType := stripping, grammatical := false }

-- ════════════════════════════════════════════════════
-- § 3. Voice Mismatch Predictions
-- ════════════════════════════════════════════════════

/-- VP-ellipsis data matches canMismatch. -/
theorem vpe_voice_predicted :
    ex1a.grammatical = canMismatch englishVPE voiceMismatch ∧
    ex2a.grammatical = canMismatch englishVPE voiceMismatch := ⟨rfl, rfl⟩

/-- Sluicing data matches canMismatch across three languages. -/
theorem sluicing_voice_predicted :
    ex5.grammatical  = canMismatch sluicing voiceMismatch ∧
    ex6a.grammatical = canMismatch sluicing voiceMismatch ∧
    ex25a.grammatical = canMismatch sluicing voiceMismatch := ⟨rfl, rfl, rfl⟩

/-- All high ellipsis types block voice mismatches. -/
theorem high_ellipsis_voice_predicted :
    ex9a.grammatical  = canMismatch fragmentAnswers voiceMismatch ∧
    ex10a.grammatical = canMismatch gapping voiceMismatch ∧
    ex11a.grammatical = canMismatch stripping voiceMismatch := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Argument Structure Alternation Data (§3.3)
-- ════════════════════════════════════════════════════

/-- A datum for argument structure alternation under ellipsis. -/
structure ArgStructureDatum where
  description : String
  alternationType : MismatchDimension
  ellipsisType : EllipsisType
  grammatical : Bool
  deriving Repr

-- § 4.1 Causative/inchoative (§3.3.1, exx. 30–31)

/-- (30a) "This can freeze. *Please do." -/
def ex30a : ArgStructureDatum :=
  { description := "Causative/inchoative blocked under VPE"
    alternationType := transitivityMismatch
    ellipsisType := englishVPE, grammatical := false }

/-- (31a) Greek: "*Eklisan ena δromo, alla δen ksero pjos ⟨eklise⟩" -/
def ex31a : ArgStructureDatum :=
  { description := "Causative/inchoative blocked under sluicing"
    alternationType := transitivityMismatch
    ellipsisType := sluicing, grammatical := false }

-- § 4.2 Middle (§3.3.1, exx. 35–36)

/-- (35a) "*They market ethanol well in the Midwest, but regular gas doesn't." -/
def ex35a : ArgStructureDatum :=
  { description := "Trans → middle blocked under VPE"
    alternationType := middleAlternation
    ellipsisType := englishVPE, grammatical := false }

/-- (36a) "*Ethanol markets well in the Midwest, though they don't in the South." -/
def ex36a : ArgStructureDatum :=
  { description := "Middle → trans blocked under VPE"
    alternationType := middleAlternation
    ellipsisType := englishVPE, grammatical := false }

-- § 4.3 Dative alternation (§3.3.2, exx. 37–39)

/-- (39a) "*They served₁ someone the meal, but I don't know to whom." -/
def ex39a : ArgStructureDatum :=
  { description := "Dative alternation blocked under sluicing"
    alternationType := dativeAlternation
    ellipsisType := sluicing, grammatical := false }

-- § 4.4 Prepositional alternation (§3.3.2, exx. 42–44)

/-- (43a) "*They embroidered something with peace signs, but I don't know
     what on ⟨they embroidered peace signs t⟩" -/
def ex43a : ArgStructureDatum :=
  { description := "Prep alternation blocked under sluicing"
    alternationType := prepAlternation
    ellipsisType := sluicing, grammatical := false }

/-- (44) "*She embroiders peace signs on jackets more often than
     she does with swastikas." -/
def ex44 : ArgStructureDatum :=
  { description := "Prep alternation blocked under pseudogapping"
    alternationType := prepAlternation
    ellipsisType := pseudogapping, grammatical := false }

-- ════════════════════════════════════════════════════
-- § 5. Argument Structure Predictions
-- ════════════════════════════════════════════════════

/-- Per-datum verification: each datum's grammaticality equals the
    canMismatch prediction for its alternation type and ellipsis type. -/
theorem argStructure_data_predicted :
    ex30a.grammatical = canMismatch ex30a.ellipsisType ex30a.alternationType ∧
    ex31a.grammatical = canMismatch ex31a.ellipsisType ex31a.alternationType ∧
    ex35a.grammatical = canMismatch ex35a.ellipsisType ex35a.alternationType ∧
    ex36a.grammatical = canMismatch ex36a.ellipsisType ex36a.alternationType ∧
    ex39a.grammatical = canMismatch ex39a.ellipsisType ex39a.alternationType ∧
    ex43a.grammatical = canMismatch ex43a.ellipsisType ex43a.alternationType ∧
    ex44.grammatical  = canMismatch ex44.ellipsisType ex44.alternationType := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- All v-level alternations are blocked under high-[E] ellipsis types
    (sluicing, VPE, fragment answers, gapping, pseudogapping) — because
    v is inside the deletion domain when [E] is at Voice or above.
    Under vVPE ([E] on v), these alternations ARE tolerated
    (@cite{kalyakin-2026}). -/
theorem v_alternations_blocked_high_ellipsis :
    canMismatch sluicing dativeAlternation = false ∧
    canMismatch sluicing prepAlternation = false ∧
    canMismatch sluicing middleAlternation = false ∧
    canMismatch englishVPE dativeAlternation = false ∧
    canMismatch englishVPE prepAlternation = false ∧
    canMismatch englishVPE middleAlternation = false ∧
    canMismatch fragmentAnswers dativeAlternation = false ∧
    canMismatch gapping middleAlternation = false ∧
    canMismatch pseudogapping prepAlternation = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════
-- § 6. Key Theoretical Claims
-- ════════════════════════════════════════════════════

/-- The uneven distribution: voice mismatches are tolerated in VP-ellipsis
    (low [E]) but blocked in all clausal ellipses (high [E]). -/
theorem uneven_distribution :
    canMismatch englishVPE voiceMismatch = true ∧
    canMismatch sluicing voiceMismatch = false ∧
    canMismatch fragmentAnswers voiceMismatch = false ∧
    canMismatch gapping voiceMismatch = false ∧
    canMismatch stripping voiceMismatch = false ∧
    canMismatch pseudogapping voiceMismatch = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Voice is the discriminating dimension: the only mismatch that
    distinguishes VP-ellipsis from sluicing. All v-level and V-level
    dimensions are blocked under both. -/
theorem voice_uniquely_discriminates :
    canMismatch englishVPE voiceMismatch ≠ canMismatch sluicing voiceMismatch ∧
    canMismatch englishVPE transitivityMismatch =
      canMismatch sluicing transitivityMismatch ∧
    canMismatch englishVPE dativeAlternation =
      canMismatch sluicing dativeAlternation ∧
    canMismatch englishVPE lexicalMismatch =
      canMismatch sluicing lexicalMismatch := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; cases h
  · native_decide
  · native_decide
  · native_decide

/-- Merchant's negative prediction: if voice mismatches were tolerated
    in sluicing (high [E]), monotonicity would force them to be tolerated
    in VP-ellipsis (low [E]) too. No language can have the reverse of
    the attested pattern. -/
theorem no_inverse_language :
    canMismatch sluicing voiceMismatch = true →
    canMismatch englishVPE voiceMismatch = true :=
  fun h => mismatch_monotone voiceMismatch sluicing englishVPE h rfl

/-- Voice's discriminating power follows from its spine position:
    it sits between the VPE boundary (Voice) and the sluicing boundary (C).
    All other mismatch dimensions sit at v or below. -/
theorem voice_between_boundaries :
    voiceMismatch.headPosition = .Voice ∧
    transitivityMismatch.headPosition = .v ∧
    dativeAlternation.headPosition = .v ∧
    prepAlternation.headPosition = .v ∧
    middleAlternation.headPosition = .v ∧
    lexicalMismatch.headPosition = .V := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 7. End-to-End Argumentation Chain
-- ════════════════════════════════════════════════════

/-- End-to-end chain: Voice severing (@cite{kratzer-1996}) →
    Merchant's deletion domain theory (@cite{merchant-2013}) →
    voice mismatch asymmetry.

    Step 1 (Voice.lean): Active and passive are distinct Voice flavors;
    Voice is an independent head above vP.

    Step 2 (DeletionDomain.lean): VPE's [E] sits on Voice, deleting vP.
    Voice is external → mismatches invisible to identity.

    Step 3 (this file): Active→passive and passive→active under VPE
    are both grammatical, matching `canMismatch`. -/
theorem end_to_end_voice_chain :
    -- Step 1: Active and passive are distinct Voice flavors
    VoiceFlavor.agentive ≠ VoiceFlavor.passive ∧
    -- Step 2: Voice is external to VPE's deletion domain
    canMismatch englishVPE voiceMismatch = true ∧
    -- Step 3: Empirical data matches
    ex1a.grammatical = true ∧
    ex2a.grammatical = true := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro h; cases h

/-- The *again* diagnostic (§4): under VPE, only repetitive *again*
    (high, VoiceP-adjunction) survives; restitutive *again* (low,
    VP-adjunction) is inside the deletion domain. This confirms
    that VPE targets vP, not VP. -/
theorem again_confirms_vp_boundary :
    againSurvives .vP_adjunction englishVPE = true ∧
    againSurvives .VP_adjunction englishVPE = false := by native_decide

end Merchant2013
