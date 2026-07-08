import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Smuggling [collins-2005]

[collins-2005] defines smuggling as follows:

> Suppose a constituent YP contains XP. Furthermore, suppose XP is
> inaccessible to Z because of the presence of W (a barrier, phase boundary,
> or intervener for the MLC / Relativized Minimality ([rizzi-1990])). If YP moves to a
> position c-commanding W, we say that YP **smuggles** XP past W.

The canonical application is passive: PartP (containing the object) moves
to Spec-VoiceP, smuggling the object past the external argument in Spec-vP.
The object can then raise to Spec-TP without violating Relativized Minimality ([rizzi-1990]),
because the intervening external argument no longer c-commands it.

[storment-2026] extends this to quotative inversion (QI): VP moves
to Spec-VoiceP, making the theme subject accessible to T⁰ for Case
licensing. The quote is clause-external (adjoined high). This yields
surface order *"Quote" V Subject*.

## Key Insight: Phase Permeability

Smuggling requires the complement of Voice to remain accessible for
extraction. Agentive Voice (v*) is a phase head; its complement is frozen
by PIC once the phase is complete. Non-thematic Voice (anticausative) is
NOT a phase head, so its complement remains accessible.

This connects to `Voice.Head.IsPhasal`:
- `Voice.agentive.IsPhasal` → vP is a phase → complement frozen → no smuggling
- `¬ Voice.anticausative.IsPhasal` → vP is not a phase → complement extractable.

[collins-2005] makes the same point: "neither the moved PartP nor
an unaccusative vP are strong phases."

-/

namespace Minimalist

-- ============================================================================
-- § 1: Smuggling Availability
-- ============================================================================

/-- Whether a Voice head permits complement extraction (smuggling).

    Smuggling requires the complement of Voice to remain accessible.
    Phase heads freeze their complement (PIC), so smuggling is available
    only with non-phase Voice. This is the structural precondition for
    quotative inversion, passivization-via-smuggling, and related
    complement-fronting operations.

    **Derived from `IsPhasal`**: this is not a new primitive but a
    direct consequence of phase theory applied to Voice. -/
def Voice.Head.permitsSmuggling (v : Voice.Head) : Bool :=
  ! decide v.IsPhasal

-- ============================================================================
-- § 2: Verification Theorems
-- ============================================================================

/-- Agentive Voice blocks smuggling (v* is a phase head). -/
theorem agentive_blocks_smuggling : Voice.agentive.permitsSmuggling = false := rfl

/-- Non-thematic Voice permits smuggling (not a phase head).
    This is why anticausative / unaccusative verbs allow complement fronting
    ([storment-2026]: quotative inversion; [collins-2005]: passive). -/
theorem nonthematic_permits_smuggling :
    Voice.anticausative.permitsSmuggling = true := rfl

/-- Causer Voice blocks smuggling (phase head, like agentive). -/
theorem causer_blocks_smuggling : Voice.causer.permitsSmuggling = false := rfl

/-- Expletive (middle) Voice permits smuggling (not a phase head). -/
theorem middle_permits_smuggling : Voice.middle.permitsSmuggling = true := rfl

/-- Impersonal Voice permits smuggling (not a phase head).
    Finnish impersonal "passive" is structurally similar to anticausative. -/
theorem impersonal_permits_smuggling :
    Voice.impersonal.permitsSmuggling = true := rfl

-- ============================================================================
-- § 3: Structural Correspondence
-- ============================================================================

/-- Smuggling availability is the exact complement of phasehood. -/
theorem smuggling_iff_not_phase (v : Voice.Head) :
    v.permitsSmuggling = ! decide v.IsPhasal := rfl

/-- θ-assigning Voice that is also a phase head blocks smuggling.
    Agentive and causer Voice are both θ-assigners and phase heads,
    so they block complement extraction. -/
theorem theta_blocks_smuggling (v : Voice.Head)
    (_h : v.AssignsTheta) (hp : v.IsPhasal) :
    v.permitsSmuggling = false := by
  simp [Voice.Head.permitsSmuggling, hp]

/-- Non-θ Voice that is also non-phasal permits smuggling.
    This covers the canonical unaccusative case. -/
theorem no_theta_permits_smuggling (v : Voice.Head)
    (_h : ¬ v.AssignsTheta) (hp : ¬ v.IsPhasal) :
    v.permitsSmuggling = true := by
  simp [Voice.Head.permitsSmuggling, hp]

-- ============================================================================
-- § 4: Quotative Inversion as Smuggling Application
-- ============================================================================

/-- A verb licenses quotative inversion iff:
    (1) its Voice head permits smuggling (non-phase vP), and
    (2) it has a complement to smuggle (the quote).

    This captures [storment-2026]'s two conditions:
    - Unaccusativity (non-thematic Voice → non-phase → smuggling available)
    - Quote complement (something to front)

    `hasComplement` corresponds to `ComplementType ≠.none` at the
    VerbEntry level; the bridge in ArgumentStructure/Studies/Storment2026.lean verifies
    this against the English fragment. -/
def licensesQI (voice : Voice.Head) (hasComplement : Bool) : Bool :=
  voice.permitsSmuggling && hasComplement

/-- QI requires both conditions: smuggling + complement. -/
theorem qi_requires_both (v : Voice.Head) (c : Bool) :
    licensesQI v c = true → v.permitsSmuggling = true ∧ c = true := by
  simp [licensesQI, Bool.and_eq_true]

/-- Agentive Voice blocks QI regardless of complement availability.
    This is why *"spoke Mary" is ungrammatical even though speak is
    a manner-of-speaking verb — agentive Voice makes vP a phase. -/
theorem agentive_blocks_qi (c : Bool) :
    licensesQI Voice.agentive c = false := by
  simp [licensesQI, agentive_blocks_smuggling]

/-- Non-thematic Voice with a complement licenses QI.
    This is why "'I'm tired,' whispered Mary" is grammatical —
    whisper projects non-thematic Voice (theme subject), and the
    quote is the complement. -/
theorem nonthematic_with_complement_licenses_qi :
    licensesQI Voice.anticausative true = true := by
  simp [licensesQI, nonthematic_permits_smuggling]

/-- Non-thematic Voice without complement does NOT license QI.
    Bare unaccusative use ("Mary arrived") has no quote to smuggle. -/
theorem nonthematic_without_complement_no_qi :
    licensesQI Voice.anticausative false = false := by
  simp [licensesQI]

-- ============================================================================
-- § 5: Passive as Smuggling Application ([collins-2005])
-- ============================================================================

/-- A Voice head licenses passive smuggling iff:
    (1) its vP is not a phase (complement remains accessible), and
    (2) there is a PartP (participial phrase) to smuggle.

    [collins-2005]: PartP (= [Part V DP_object]) is complement of v.
    In passive, PartP moves to Spec-VoiceP, smuggling the object DP past
    the external argument in Spec-vP. The object can then raise to
    Spec-TP without violating Relativized Minimality ([rizzi-1990]).

    The structural parallel with QI is exact:
    - QI: VP smuggles theme past agent
    - Passive: PartP smuggles object past external argument

    [collins-2005]: passive v is not v* — it assigns θ but does
    not check Case (dissociated onto Voice/*by*). Without Case-checking,
    v is not a strong phase head, so PartP is extractable. -/
def licensesPassiveSmuggling (voice : Voice.Head) (hasPartP : Bool) : Bool :=
  voice.permitsSmuggling && hasPartP

/-- Passive smuggling requires both conditions. -/
theorem passive_smuggling_requires_both (v : Voice.Head) (p : Bool) :
    licensesPassiveSmuggling v p = true →
    v.permitsSmuggling = true ∧ p = true := by
  simp [licensesPassiveSmuggling, Bool.and_eq_true]

/-- Passive Voice licenses smuggling when PartP is present.
    This is the canonical passive derivation from [collins-2005]. -/
theorem passive_voice_licenses_smuggling :
    licensesPassiveSmuggling Voice.passive true = true := by
  decide

/-- Agentive Voice blocks passive smuggling — v* is a phase head,
    so PartP is frozen by PIC. Active transitives do not undergo
    smuggling: the object gets Case from v directly. -/
theorem active_blocks_smuggling (p : Bool) :
    licensesPassiveSmuggling Voice.agentive p = false := by
  simp [licensesPassiveSmuggling, agentive_blocks_smuggling]

/-- Passive smuggling and QI smuggling share the same structural
    precondition: non-phase Voice. The difference is the smuggled
    constituent (PartP vs VP) and the Voice flavor (passive vs
    anticausative). -/
theorem smuggling_shared_precondition :
    Voice.passive.permitsSmuggling = true ∧
    Voice.anticausative.permitsSmuggling = true := by decide

/-- Passive Voice checks Case but does not assign θ (feature
    dissociation). This is what makes passive v defective (non-phase):
    Case-checking is the property that distinguishes v* from v
    ([chomsky-2001], [collins-2005] p. 96). -/
theorem passive_dissociation_enables_smuggling :
    Voice.passive.ChecksCase ∧
    ¬ Voice.passive.IsPhasal ∧
    Voice.passive.permitsSmuggling = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Minimalist
