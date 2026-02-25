import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Syntax.Minimalism.Core.ClauseSpine

/-!
# Mam Voice System Fragment

Minimalist infrastructure for the SJO Mam verbal domain, connecting the
language-specific clause sizes to the ClauseSpine and VoiceHead abstractions.

## Key Claims (Elkins, Imanishi & Coon 2026)

1. Mam transitive clauses project Voice⁰, which bears [uOblique].
2. Mam "aspectless" complements are VoiceP-sized — they lack aspect
   morphology but still project Voice.
3. Mam infinitival complements are VP-sized (Elkins et al. 2026, §6.1) — they project
   only V, without Voice, Appl, or v.
4. The directional auxiliary (Dir⁰) is a Mam-specific head that also
   bears [uOblique] and can host =(y)a'. Dir is modeled as a light verb
   (V1 in the verbal template Voice > V1(Dir) > Appl > V2(root)) but is
   NOT added to `Cat` as it is not universal.

## References

- Elkins, N., Y. Imanishi & J. Coon (2026). Wh-movement and oblique
  extraction in SJO Mam.
-/

namespace Fragments.Mam

-- ============================================================================
-- § 1: Mam Voice Head
-- ============================================================================

/-- Mam agentive Voice head with [uOblique] probe.

    In Mam, Voice⁰ probes for an oblique feature on a passing
    Ā-moved constituent. When an oblique DP moves through Spec,VoiceP,
    Agree values [uOblique] as [+oblique], which is then spelled out
    as =(y)a' at PF. -/
def mamVoice : Minimalism.VoiceHead :=
  { flavor := .agentive
  , hasD := true
  , phaseHead := true
  , features := [.unvalued (.oblique false)] }

-- ============================================================================
-- § 2: Clause Spines
-- ============================================================================

/-- Mam transitive clause spine: full CP with Voice.
    Projects V, Appl, v, Voice, T, C. =(y)a' possible. -/
def mamTransitiveSpine : Minimalism.ClauseSpine := Minimalism.ClauseSpine.cP

/-- Mam aspectless complement spine: VoiceP-sized.
    Projects V, Appl, v, Voice. Still has Voice → =(y)a' possible. -/
def mamAspectlessSpine : Minimalism.ClauseSpine := Minimalism.ClauseSpine.voiceP

/-- Mam infinitival complement spine: VP-sized (Elkins et al. 2026, §6.1).
    Projects only V — no Voice, no Appl, no v. =(y)a' impossible because
    there is no Voice⁰ to bear [uOblique]. -/
def mamInfinitivalSpine : Minimalism.ClauseSpine := Minimalism.ClauseSpine.bareVP

-- ============================================================================
-- § 3: Directional Auxiliary
-- ============================================================================

/-- Mam directional auxiliary head (Dir⁰).

    Dir is NOT a universal category — it is specific to Mayan languages.
    We model it as a language-specific type rather than adding to `Cat`
    (which would cascade to fValue, catFamily, epSemanticType, etc.).

    In Elkins et al.'s analysis, Dir⁰ occupies V1 position in the
    verbal template (Voice > V1(Dir) > Appl > V2(root)). Like Voice⁰,
    Dir⁰ bears [uOblique] and can host =(y)a'. Both Voice and Dir
    independently Agree with an oblique passing through their specifier,
    yielding multiple =(y)a' along the movement path. -/
structure MamDirHead where
  /-- Whether the directional is cislocative (toward speaker) or
      translocative (away from speaker) -/
  cislocative : Bool
  deriving DecidableEq, BEq, Repr

/-- Cislocative directional: movement toward deictic center -/
def dirCis : MamDirHead := { cislocative := true }

/-- Translocative directional: movement away from deictic center -/
def dirTrans : MamDirHead := { cislocative := false }

-- ============================================================================
-- § 4: Projection Theorems
-- ============================================================================

/-- Mam transitive spine projects Voice. -/
theorem mamTransitive_has_voice :
    mamTransitiveSpine.projects .Voice = true := by native_decide

/-- Mam aspectless spine projects Voice. -/
theorem mamAspectless_has_voice :
    mamAspectlessSpine.projects .Voice = true := by native_decide

/-- Mam infinitival spine does NOT project Voice. -/
theorem mamInfinitival_lacks_voice :
    mamInfinitivalSpine.projects .Voice = false := by native_decide

/-- Mam Voice head carries [uOblique]. -/
theorem mamVoice_has_uOblique :
    Minimalism.hasUnvaluedFeature mamVoice.features (.oblique false) = true := by
  native_decide

/-- Mam Voice is a phase head. -/
theorem mamVoice_is_phase : mamVoice.phaseHead = true := rfl

/-- Mam Voice assigns a θ-role (agentive). -/
theorem mamVoice_assigns_theta : mamVoice.assignsTheta = true := rfl

end Fragments.Mam
