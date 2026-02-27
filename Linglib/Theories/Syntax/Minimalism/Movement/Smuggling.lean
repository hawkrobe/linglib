import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# Smuggling (Collins 2005) @cite{collins-2005}

Collins (2005, p. 97) defines smuggling as follows:

> Suppose a constituent YP contains XP. Furthermore, suppose XP is
> inaccessible to Z because of the presence of W (a barrier, phase boundary,
> or intervener for the MLC / Relativized Minimality). If YP moves to a
> position c-commanding W, we say that YP **smuggles** XP past W.

The canonical application is passive: PartP (containing the object) moves
to Spec-VoiceP, smuggling the object past the external argument in Spec-vP.
The object can then raise to Spec-TP without violating Relativized Minimality,
because the intervening external argument no longer c-commands it.

Storment (2026, NLLT) extends this to quotative inversion (QI): VP moves
to Spec-VoiceP, making the theme subject accessible to T⁰ for Case
licensing. The quote is clause-external (adjoined high). This yields
surface order *"Quote" V Subject*.

## Key Insight: Phase Permeability

Smuggling requires the complement of Voice to remain accessible for
extraction. Agentive Voice (v*) is a phase head; its complement is frozen
by PIC once the phase is complete. Non-thematic Voice (anticausative) is
NOT a phase head, so its complement remains accessible.

This connects to the existing `VoiceHead.phaseHead` field:
- `voiceAgent.phaseHead = true` → vP is a phase → complement frozen → no smuggling
- `voiceAnticausative.phaseHead = false` → vP is not a phase → complement extractable

Collins (2005, p. 98) makes the same point: "neither the moved PartP nor
an unaccusative vP are strong phases."

## References

- Collins, C. (2005). A Smuggling Approach to the Passive in English.
  *Syntax* 8(2): 81–120. @cite{collins-2005}
- Storment, J. (2026). Quotative inversion as an unaccusativity diagnostic.
  *Natural Language & Linguistic Theory*. @cite{storment-2026}
-/

namespace Minimalism

-- ============================================================================
-- § 1: Smuggling Availability
-- ============================================================================

/-- Whether a Voice head permits complement extraction (smuggling).

    Smuggling requires the complement of Voice to remain accessible.
    Phase heads freeze their complement (PIC), so smuggling is available
    only with non-phase Voice. This is the structural precondition for
    quotative inversion, passivization-via-smuggling, and related
    complement-fronting operations.

    **Derived from `phaseHead`**: this is not a new primitive but a
    direct consequence of phase theory applied to Voice. -/
def VoiceHead.permitsSmuggling (v : VoiceHead) : Bool :=
  !v.phaseHead

-- ============================================================================
-- § 2: Verification Theorems
-- ============================================================================

/-- Agentive Voice blocks smuggling (v* is a phase head). -/
theorem agentive_blocks_smuggling : voiceAgent.permitsSmuggling = false := rfl

/-- Non-thematic Voice permits smuggling (not a phase head).
    This is why anticausative / unaccusative verbs allow complement fronting
    (Storment 2026: quotative inversion; Collins 2005: passive). -/
theorem nonthematic_permits_smuggling :
    voiceAnticausative.permitsSmuggling = true := rfl

/-- Causer Voice blocks smuggling (phase head, like agentive). -/
theorem causer_blocks_smuggling : voiceCauser.permitsSmuggling = false := rfl

/-- Expletive (middle) Voice permits smuggling (not a phase head). -/
theorem middle_permits_smuggling : voiceMiddle.permitsSmuggling = true := rfl

/-- Impersonal Voice permits smuggling (not a phase head).
    Finnish impersonal "passive" is structurally similar to anticausative. -/
theorem impersonal_permits_smuggling :
    voiceImpersonal.permitsSmuggling = true := rfl

-- ============================================================================
-- § 3: Structural Correspondence
-- ============================================================================

/-- Smuggling availability is the exact complement of phasehood. -/
theorem smuggling_iff_not_phase (v : VoiceHead) :
    v.permitsSmuggling = !v.phaseHead := rfl

/-- θ-assigning Voice blocks smuggling.
    Agentive and causer Voice are both θ-assigners and phase heads,
    so they block complement extraction. -/
theorem theta_blocks_smuggling (v : VoiceHead)
    (_h : v.assignsTheta = true) (hp : v.phaseHead = true) :
    v.permitsSmuggling = false := by
  simp [VoiceHead.permitsSmuggling, hp]

/-- Non-θ Voice with `phaseHead = false` permits smuggling.
    This covers the canonical unaccusative case. -/
theorem no_theta_permits_smuggling (v : VoiceHead)
    (_h : v.assignsTheta = false) (hp : v.phaseHead = false) :
    v.permitsSmuggling = true := by
  simp [VoiceHead.permitsSmuggling, hp]

-- ============================================================================
-- § 4: Quotative Inversion as Smuggling Application
-- ============================================================================

/-- A verb licenses quotative inversion iff:
    (1) its Voice head permits smuggling (non-phase vP), and
    (2) it has a complement to smuggle (the quote).

    This captures Storment's (2026) two conditions:
    - Unaccusativity (non-thematic Voice → non-phase → smuggling available)
    - Quote complement (something to front)

    `hasComplement` corresponds to `ComplementType ≠ .none` at the
    VerbEntry level; the bridge in Unaccusativity/Bridge.lean verifies
    this against the English fragment. -/
def licensesQI (voice : VoiceHead) (hasComplement : Bool) : Bool :=
  voice.permitsSmuggling && hasComplement

/-- QI requires both conditions: smuggling + complement. -/
theorem qi_requires_both (v : VoiceHead) (c : Bool) :
    licensesQI v c = true → v.permitsSmuggling = true ∧ c = true := by
  simp [licensesQI, Bool.and_eq_true]

/-- Agentive Voice blocks QI regardless of complement availability.
    This is why *"spoke Mary" is ungrammatical even though speak is
    a manner-of-speaking verb — agentive Voice makes vP a phase. -/
theorem agentive_blocks_qi (c : Bool) :
    licensesQI voiceAgent c = false := by
  simp [licensesQI, agentive_blocks_smuggling]

/-- Non-thematic Voice with a complement licenses QI.
    This is why "'I'm tired,' whispered Mary" is grammatical —
    whisper projects non-thematic Voice (theme subject), and the
    quote is the complement. -/
theorem nonthematic_with_complement_licenses_qi :
    licensesQI voiceAnticausative true = true := by
  simp [licensesQI, nonthematic_permits_smuggling]

/-- Non-thematic Voice without complement does NOT license QI.
    Bare unaccusative use ("Mary arrived") has no quote to smuggle. -/
theorem nonthematic_without_complement_no_qi :
    licensesQI voiceAnticausative false = false := by
  simp [licensesQI]

-- ============================================================================
-- § 5: Passive as Smuggling Application (Collins 2005)
-- ============================================================================

/-- A Voice head licenses passive smuggling iff:
    (1) its vP is not a phase (complement remains accessible), and
    (2) there is a PartP (participial phrase) to smuggle.

    Collins (2005, §5): PartP (= [Part V DP_object]) is complement of v.
    In passive, PartP moves to Spec-VoiceP, smuggling the object DP past
    the external argument in Spec-vP. The object can then raise to
    Spec-TP without violating Relativized Minimality.

    The structural parallel with QI is exact:
    - QI: VP smuggles theme past agent (Storment 2026)
    - Passive: PartP smuggles object past external argument (Collins 2005)

    Collins (2005, p. 98): passive v is not v* — it assigns θ but does
    not check Case (dissociated onto Voice/*by*). Without Case-checking,
    v is not a strong phase head, so PartP is extractable. -/
def licensesPassiveSmuggling (voice : VoiceHead) (hasPartP : Bool) : Bool :=
  voice.permitsSmuggling && hasPartP

/-- Passive smuggling requires both conditions. -/
theorem passive_smuggling_requires_both (v : VoiceHead) (p : Bool) :
    licensesPassiveSmuggling v p = true →
    v.permitsSmuggling = true ∧ p = true := by
  simp [licensesPassiveSmuggling, Bool.and_eq_true]

/-- Passive Voice licenses smuggling when PartP is present.
    This is the canonical passive derivation from Collins (2005). -/
theorem passive_voice_licenses_smuggling :
    licensesPassiveSmuggling voicePassive true = true := by
  simp [licensesPassiveSmuggling, VoiceHead.permitsSmuggling, voicePassive]

/-- Agentive Voice blocks passive smuggling — v* is a phase head,
    so PartP is frozen by PIC. Active transitives do not undergo
    smuggling: the object gets Case from v directly. -/
theorem active_blocks_smuggling (p : Bool) :
    licensesPassiveSmuggling voiceAgent p = false := by
  simp [licensesPassiveSmuggling, agentive_blocks_smuggling]

/-- Passive smuggling and QI smuggling share the same structural
    precondition: non-phase Voice. The difference is the smuggled
    constituent (PartP vs VP) and the Voice flavor (passive vs
    anticausative). -/
theorem smuggling_shared_precondition :
    voicePassive.permitsSmuggling = true ∧
    voiceAnticausative.permitsSmuggling = true := ⟨rfl, rfl⟩

/-- Passive Voice checks Case but does not assign θ (feature
    dissociation). This is what makes passive v defective (non-phase):
    Case-checking is the property that distinguishes v* from v
    (Chomsky 2001, Collins 2005 p. 96). -/
theorem passive_dissociation_enables_smuggling :
    voicePassive.checksCase = true ∧
    voicePassive.phaseHead = false ∧
    voicePassive.permitsSmuggling = true := ⟨rfl, rfl, rfl⟩

end Minimalism
