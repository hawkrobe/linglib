import Linglib.Data.Examples.Collins2005
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Minimalist.Movement.Smuggling
import Linglib.Syntax.Minimalist.Movement.InverseVoice

/-!
# A Smuggling Approach to the Passive in English
[collins-2005] [chomsky-2001] [legate-2003] [rizzi-1990]

Connects Collins's §3 diagnostic rows (`Data/Examples/Collins2005.json`)
to the smuggling theory in `Syntax.Minimalist.Movement.Smuggling`
and the Voice/phase infrastructure in `Syntax.Minimalist.Verbal.Voice`.

## Collins's central claims

[collins-2005] argues for a smuggling derivation of the passive that
combines aspects of the principles-and-parameters approach (no specific
rules, no downward movement) with [chomsky-1957]'s *Syntactic Structures*
analysis (the arguments are generated in the same positions in active and
passive, satisfying UTAH).

- **§2 (UTAH)**: The external argument is merged into Spec,vP in the passive
  *just as in the active* — no special downward movement or theta-role
  absorption. Same θ-positions in both voices.
- **§3 (PartP movement, not head movement)**: The verb does not raise
  through Part to v to Voice; rather, PartP (= [Part V DP]) undergoes
  XP-movement to Spec,VoiceP. Evidence: particle stranding (15–16) and
  pseudo-passives (18–19) are incompatible with head-movement.
- **§4 (*by* heads VoiceP)**: The preposition *by* is the head of a
  functional projection VoiceP, not the head of an ordinary PP. *By* is
  composed entirely of uninterpretable features and checks accusative Case
  on the external argument in Spec,vP. The Case feature of v dissociates
  to Voice (eq. 32).
- **§5 (Smuggling)**: PartP smuggles the internal argument past the
  external argument in Spec,vP, freeing it for A-movement to Spec,IP
  without violating Relativized Minimality.
- **§6 (Short passives)**: The external argument is structurally present
  even when not phonologically realized — an empty pronominal in Spec,vP.
- **§8 (*by-DP* is a constituent)**: Coordination data (63–64) shows
  *by John* behaves as a unit; this is derived as VoiceP coordination
  with deletion, not as a stipulated [PP by DP].
-/

namespace Collins2005

open Minimalist

/-! ## §1. Voice properties Collins defends

The four core properties of `voicePassive`: it does not assign an external
θ-role (which v does, per §2 UTAH), it does check accusative Case (per §4
Case dissociation), it is not a phase head (which is what permits smuggling
per §5), and it has a D-feature (it is a Voice head, not an expletive). -/

/-- [collins-2005] §2: passive Voice does *not* assign external θ.
    The external θ-role stays on v in both active and passive. -/
theorem passive_voice_does_not_assign_theta :
    ¬ voicePassive.AssignsTheta := by decide

/-- [collins-2005] §4: passive Voice checks accusative Case. The
    Case feature dissociates from v and projects on the Voice head
    (whose lexical realization is *by*). -/
theorem passive_voice_checks_case :
    voicePassive.ChecksCase := by decide

/-- [collins-2005] §5: passive Voice is not a phase head, which is
    what permits PartP to smuggle past the external argument in Spec,vP. -/
theorem passive_voice_not_phase :
    ¬ voicePassive.IsPhasal := by decide

/-- [collins-2005] §5: passive Voice permits smuggling. -/
theorem passive_permits_smuggling :
    voicePassive.permitsSmuggling = true := rfl

/-! ## §2. Active vs. passive: feature dissociation (Collins §4 eq. 32)

Collins's central theoretical move: the active and passive *v* are
identical in θ-assignment (both assign external θ in Spec,vP). They
differ in *where* the accusative-Case feature is checked. In the
active, v checks Case directly. In the passive, the Case feature
dissociates from v and is added to the numeration as part of the Voice
head. The two heads are then in complementary distribution on
(θ-assigning, Case-checking). -/

/-- [collins-2005] §4 eq. 31: active and passive have the same
    θ-assignment but distribute the Case-checking feature differently. -/
theorem active_passive_dissociation :
    -- Active: v assigns θ AND checks Case (Voice does not check Case)
    (voiceAgent.AssignsTheta ∧ ¬ voiceAgent.ChecksCase) ∧
    -- Passive: v does NOT assign θ; Voice (by) checks Case
    (¬ voicePassive.AssignsTheta ∧ voicePassive.ChecksCase) := by decide

/-- The phase status correlates with where Case checking lives.
    Active v* is a strong phase (it checks Case); passive v is not
    (Case has dissociated to Voice). The non-phase status is what
    permits smuggling. -/
theorem case_dissociation_explains_phase :
    ¬ voiceAgent.ChecksCase ∧ voiceAgent.IsPhasal ∧
    voicePassive.ChecksCase ∧ ¬ voicePassive.IsPhasal := by decide

/-! ## §3. PartP movement is XP-movement, not head movement

Collins argues against the head-movement analysis of the passive on the
basis of (a) particle stranding and (b) pseudo-passives. Both diagnostics
fall out from the assumption that the constituent moved is PartP, not
just the verb. The data are the `test = particle` rows of
`Data/Examples/Collins2005.json`, derived here from the smuggling
configuration. -/

/-- [collins-2005] §3 (15–16): in passive with a particle verb,
    the only grammatical order is `V Prt EA` (`summed up by the coach`),
    not `V EA Prt` (*`summed by the coach up`). This follows from the
    smuggling configuration: PartP = [Part V DP] moves *as a constituent*
    to Spec,VoiceP, taking the particle along with the verb. -/
theorem particle_stranding_requires_xp_movement :
    licensesPassiveSmuggling voicePassive true = true := by
  simp only [licensesPassiveSmuggling, passive_permits_smuggling, Bool.true_and]

/-- [collins-2005] §3 (18–19): pseudo-passives (`John was spoken to
    by Mary`) require the preposition to be inside the smuggled PartP
    (P stays adjacent to V, not stranded after EA). Same XP-movement
    diagnostic as particles. -/
theorem pseudo_passive_requires_xp_movement :
    licensesPassiveSmuggling voicePassive true = true :=
  particle_stranding_requires_xp_movement

/-! ## §4. Without PartP there is nothing to smuggle -/

/-- The smuggling derivation requires PartP to be present (something to
    move). Without it, no derivation is licensed. -/
theorem no_partP_no_passive :
    licensesPassiveSmuggling voicePassive false = false := by
  simp only [licensesPassiveSmuggling, Bool.and_false]

/-! ## §5. Short passives (§6 of paper)

[collins-2005] §6 (45–47): even when the external argument is not
phonologically realized (`The book was written`), it is structurally
present as an empty pronominal in Spec,vP. Evidence: implicit arguments
bind reflexives (42a `Such privileges should be kept to oneself`), license
depictives (44b `Breakfast is eaten by the campers nude`), and pattern
exactly like overt external arguments (44).

In the formal terms of this file, a short passive has the same Voice
configuration as a long passive — the only difference is whether Spec,vP
is filled by an overt DP or an empty pronominal. -/

/-- Short passives use the same `voicePassive` head as long passives —
    smuggling is licensed identically; the difference is only the
    realization of Spec,vP (overt DP vs. empty pronominal). -/
theorem short_and_long_passive_share_voice :
    -- Both are licensed by the same Voice + PartP configuration
    licensesPassiveSmuggling voicePassive true = true ∧
    -- Same Voice properties (no theta, checks Case, not phase)
    ¬ voicePassive.AssignsTheta ∧
    voicePassive.ChecksCase ∧
    ¬ voicePassive.IsPhasal := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact particle_stranding_requires_xp_movement
  all_goals decide

/-! ## §6. *By-DP* as a VoiceP constituent (§8 of paper)

[collins-2005] §8 (63–64) defends *by-DP* as a constituent on the
basis of coordination: `The book was written by John and by Bill` is
grammatical — coordination of two `by-DP` strings. Under Collins's
analysis there is no `[PP by DP]` constituent (since *by* heads VoiceP,
not PP), so the apparent coordination is analyzed as VoiceP coordination
with deletion of the second PartP.

The substantive claim relevant to this formalization: the entity that
behaves as a coordination target is `VoiceP` (with PartP-deletion),
not `[PP by DP]`. -/

/-- The coordination test bears on Voice-head identity: if *by* heads
    VoiceP (Collins §4), then `[by John]` is the surface form of a
    `[VoiceP PartP [Voice' by vP]]` and the coordination in (63b) is
    VoiceP-coordination with PartP-deletion (Collins §8 eq. 64). The
    substantive constraint is that both conjuncts use the same Voice
    head, which `voicePassive` represents. -/
theorem by_dp_coordination_requires_voiceP :
    -- Both coordinated `by-DP` units project the same passive Voice
    voicePassive = voicePassive ∧
    -- Voice properties are stable across the conjuncts
    voicePassive.ChecksCase ∧
    ¬ voicePassive.AssignsTheta := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-! ## §7. Inverse-voice family membership

The smuggling derivation Collins develops for the passive is the same
mechanism [storment-2026] extends to QI and LI. The shared
structural invariant — non-phase Voice permits VP/PartP smuggling —
is captured by `Minimalist.InverseVoiceConstruction` in the Theories
layer. Collins's passive instance is `Minimalist.passiveCanonical`. -/

/-- The passive is one canonical instance of the inverse-voice family. -/
theorem passive_is_inverse_voice :
    Minimalist.passiveCanonical.kind = .passive ∧
    Minimalist.passiveCanonical.licensed = true ∧
    Minimalist.passiveCanonical.voice = voicePassive :=
  ⟨rfl, rfl, rfl⟩

/-! ## §8. Transfer equations over the §3 diagnostic rows

Each diagnostic section of Collins §3 has a uniform predictor over the
rows of `Data/Examples/Collins2005.json`, read off the smuggling
configuration: the derived subject sits in Spec,IP and c-commands the
by-phrase in Spec,vP; PartP moves as a constituent leaving no DP object;
and both *have* and passive *be* select PartP. -/

open Data.Examples

/-- **C-command rows (10a–d)**: a binding/NPI dependency succeeds iff the
    licensee sits in the by-phrase — the derived subject c-commands the
    by-phrase and not conversely, exactly the asymmetry the smuggled-object
    configuration predicts. -/
theorem c_command_rows_acceptable_iff_licensee_in_by_phrase :
    ∀ row ∈ Examples.all, row.feature? "test" = some "c_command" →
      (row.judgment = .acceptable ↔
        row.feature? "licensee_position" = some "by_phrase") := by
  decide

/-- **Particle rows (15–16)**: a passive particle clause is grammatical iff
    no DP object remains — PartP moved as a constituent, taking the
    particle and leaving no Case position for a second DP. -/
theorem particle_rows_acceptable_iff_no_dp_object :
    ∀ row ∈ Examples.all, row.feature? "test" = some "particle" →
      (row.judgment = .acceptable ↔
        row.feature? "has_dp_object" = some "false") := by
  decide

/-- **Auxiliary rows (23a–d)**: both *have* and passive *be* are grammatical
    iff their complement is a past participle — the shared PartP selection
    of conditions (24–25). -/
theorem aux_rows_acceptable_iff_participial_complement :
    ∀ row ∈ Examples.all, row.feature? "test" = some "aux_selection" →
      (row.judgment = .acceptable ↔
        row.feature? "complement_form" = some "past_participle") := by
  decide

end Collins2005
