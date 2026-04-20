import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Syntax.Minimalism.Core.ClauseSpine
import Linglib.Theories.Interfaces.SyntaxPhonology.Minimalism.Spellout
import Linglib.Core.VoiceSystem

/-!
# Mam Voice System Fragment
@cite{elkins-torrence-brown-2026} @cite{scott-2023}

Minimalist infrastructure for the Mam verbal domain, connecting the
language-specific clause sizes to the ClauseSpine and VoiceHead abstractions.

**Variety note**: Oblique extraction (=(y)a') data is from SJO (San Juan
Ostuncalco) Mam via @cite{elkins-torrence-brown-2026}. Antipassive voice
data draws on SJA (San Juan Atitán) Mam via @cite{scott-2023}. These are
distinct varieties; shared infrastructure (clause spines, Voice heads) is
parameterized where possible.

## Key Claims

1. Mam transitive clauses project Voice⁰, which bears [uOblique].
2. Mam "aspectless" complements are VoiceP-sized — they lack aspect
   morphology but still project Voice.
3. Mam infinitival complements are VP-sized — they project
   only V, without Voice, Appl, or v.
4. The directional auxiliary (Dir⁰) is a Mam-specific head that also
   bears [uOblique] and can host =(y)a'. Dir is modeled as a light verb
   (V1 in the verbal template Voice > V1(Dir) > Appl > V2(root)) but is
   NOT added to `Cat` as it is not universal.

-/

namespace Fragments.Mayan.Mam

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

/-- Mam infinitival complement spine: VP-sized.
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
  /-- Whether this Dir head carries [uOblique], enabling Agree with
      passing obliques. Like Voice⁰, Dir⁰ can independently trigger
      =(y)a' spellout when oblique extraction passes through its
      domain. -/
  hasUOblique : Bool := false
  deriving DecidableEq, Repr

/-- Dir⁰'s probe features when it carries [uOblique]. -/
def MamDirHead.features (d : MamDirHead) : Minimalism.FeatureBundle :=
  if d.hasUOblique then [.unvalued (.oblique false)] else []

/-- Cislocative directional with [uOblique]: movement toward deictic center.
    Carries the same oblique probe as Voice⁰ (Elkins et al. §3.1, ex. 8). -/
def dirCis : MamDirHead := { cislocative := true, hasUOblique := true }

/-- Translocative directional with [uOblique]: movement away from deictic center. -/
def dirTrans : MamDirHead := { cislocative := false, hasUOblique := true }

-- ============================================================================
-- § 4: Dir Probe Theorems
-- ============================================================================

/-- Cislocative Dir carries [uOblique]. -/
theorem dirCis_has_uOblique : dirCis.hasUOblique = true := rfl

/-- Translocative Dir carries [uOblique]. -/
theorem dirTrans_has_uOblique : dirTrans.hasUOblique = true := rfl

/-- Dir's probe features match Voice's: both carry [uOblique].
    This ensures both heads can independently Agree with a passing
    oblique, yielding multiple =(y)a' along the movement path. -/
theorem dir_features_match_voice :
    dirCis.features = mamVoice.features := by native_decide

-- ============================================================================
-- § 5: Projection Theorems
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

-- ============================================================================
-- § 6: Spellout Vocabulary
-- ============================================================================

/-- Vocabulary entry for =(y)a': maps [+oblique] on Voice⁰ to the exponent
    "=(y)a'". This is the Vocabulary Insertion rule in DM terms. -/
def eqYaVocab : Minimalism.VocabEntry :=
  { features := [.valued (.oblique true)]
  , exponent := "=(y)a'"
  , context := some .Voice }

/-- The Mam Voice vocabulary: just the =(y)a' entry. -/
def mamVoiceVocab : Minimalism.Vocabulary := [eqYaVocab]

-- ============================================================================
-- § 7: Passive Voice (Co-occurrence with =(y)a')
-- ============================================================================

/-- Mam passive Voice head: carries [uOblique] just like agentive Voice.
    The oblique probe is independent of Voice flavor — changing flavor
    from agentive to non-thematic does not remove [uOblique]. This is
    why =(y)a' co-occurs with passive *-njtz* (Elkins et al. §7.2). -/
def mamPassiveVoice : Minimalism.VoiceHead :=
  { flavor := .nonThematic
  , hasD := false
  , phaseHead := false
  , features := [.unvalued (.oblique false)] }

/-- Passive and agentive Voice differ in flavor but share the same
    oblique probe features. =(y)a' (conditioned by features) and
    *-njtz* (conditioned by flavor) are structurally independent. -/
theorem passive_voice_same_features :
    mamPassiveVoice.features = mamVoice.features ∧
    mamPassiveVoice.flavor ≠ mamVoice.flavor := by
  exact ⟨rfl, by decide⟩

-- ============================================================================
-- § 8: Antipassive Voice (@cite{scott-2023}, §2.5.4.1)
-- ============================================================================

/-- Mam antipassive Voice head.

    In antipassive constructions, the agent is still introduced by Voice
    but receives absolutive case (Set B marking) instead of ergative (Set A).
    The object is demoted to an oblique introduced by a relational noun.
    The verb bears the antipassive suffix -(a)n.

    Antipassive Voice is NOT a phase head — the subject gets ABS, not ERG.
    This is the key structural difference from agentive Voice: the clause
    is syntactically intransitive despite having an agent.

    In agent focus / ergative extraction contexts, the antipassive
    co-occurs with the suffix -ta (@cite{scott-2023}, §2.7.1.3). -/
def mamAntipassiveVoice : Minimalism.VoiceHead :=
  { flavor := .antipassive
  , hasD := true
  , phaseHead := false
  , features := [] }

/-- Antipassive Voice assigns a θ-role (the agent is present). -/
theorem mamAntipassive_assigns_theta :
    mamAntipassiveVoice.assignsTheta = true := rfl

/-- Antipassive Voice is NOT a phase head. -/
theorem mamAntipassive_not_phase :
    mamAntipassiveVoice.phaseHead = false := rfl

/-- Antipassive and agentive Voice differ in phase-head status but both
    assign θ-roles. This captures the transitivity alternation: same
    agent, different case on the subject. -/
theorem antipassive_vs_agentive :
    mamAntipassiveVoice.assignsTheta = mamVoice.assignsTheta ∧
    mamAntipassiveVoice.phaseHead ≠ mamVoice.phaseHead := ⟨rfl, by decide⟩

-- ============================================================================
-- § 9: Voice System Profile
-- ============================================================================

/-- Mam voice system: two-way asymmetrical (agentive/passive).

    Unlike Toba Batak's symmetrical pivot system, Mam's agentive voice
    is the basic form (phase head, overt agent) and passive is derived
    (non-phase, implicit agent). Voice does not determine pivot for
    extraction — instead, Voice carries [uOblique] which conditions
    extraction morphology (=(y)a'). -/
def mamVoiceSystem : Interfaces.VoiceSystemProfile :=
  { language := "Mam"
    voices := [ ⟨"Agentive Voice", .agent⟩, ⟨"Passive Voice", .patient⟩,
                ⟨"Antipassive Voice", .agent⟩ ]
    symmetry := .asymmetrical
    notes := "Agentive is basic (phase head); passive/antipassive are derived. " ++
             "Antipassive demotes object to oblique, subject gets ABS (Scott 2023). " ++
             "Voice data from SJA (Scott 2023) and SJO (Elkins et al. 2026)" }

theorem mam_voice_system_asymmetrical :
    mamVoiceSystem.symmetry = .asymmetrical := rfl

theorem mam_voice_count :
    mamVoiceSystem.voiceCount = 3 := rfl

/-- Mam is not a simple active/passive system — it also has antipassive. -/
theorem mam_not_simple_active_passive :
    ¬ mamVoiceSystem.isActivePassive := by decide

theorem mam_no_oblique_pivots :
    ¬ mamVoiceSystem.distinguishesObliques := by decide

end Fragments.Mayan.Mam
