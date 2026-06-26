import Linglib.Syntax.Minimalist.Linearization.Cyclic
import Linglib.Fragments.Malayic.VoiceSystem
import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Voice and Extraction in Malayic
[erlewine-sommerlot-2025]

[erlewine-sommerlot-2025] propose a new analysis of Malayic clausal
morphosyntax that derives the interaction between voice morphology and
nominal A'-extraction from cyclic linearization ([fox-pesetsky-2005]).

## Core claims

1. The verbal domain involves two functional heads: **Voice** (higher,
   phase head) and ***v*** (lower, introduces external argument).
   The active prefix *meN-* reflects both: *me-* on Voice, *N-* on *v*.

2. **VoiceP is a phase** with exactly one nominal specifier. Only the
   subject — the nominal in Spec,VoiceP — can A'-extract from the
   basic clause types (active, *di-* passive, bare passive).

3. **Object extraction** involves the theme moving to Spec,VoiceP (the
   single nominal specifier) and then A'-moving to Spec,CP, while the
   agent stays low in Spec,*v*P. This is possible only when Voice is
   realized as a **null allomorph**.

4. **meN-deletion derived**: overt Voice (*me-*) in object extraction
   creates an ordering paradox at cyclic linearization. At VoiceP
   Spell-out, Voice precedes the agent; at CP Spell-out, the agent
   (having moved to Spec,TP or staying high) precedes Voice. The
   contradiction forces Voice to be null.

5. **Cross-linguistic variation** (Desa, SI/SM, polite/familiar Madurese)
   reduces to parametric differences in vocabulary items for Voice and *v*.

## PIC mode

[erlewine-sommerlot-2025]'s analysis derives the meN-deletion
constraint from cyclic linearization alone, without invoking the
Phase Impenetrability Condition. This positions them at
`PICStrength.linearizationBound` (per `Syntax/Minimalist/Phase.lean`):
no opacity constraint per se, only ordering constraints from
`SpelloutAndCheck`. Same regime adopted by
[sande-clem-dabkowski-2026] for Guébie discontinuous harmony,
[branan-davis-2019] for agreement-edge unlocking, and others.
The structural diagnostic that the meN-deletion derivation is
ruled out is precisely *not* a PIC-violation but a Cyclic Linearization
contradiction — see `men_deletion` below.

## Formalization strategy

We model each derivation as a sequence of Spell-out domains, where each
domain is the left-to-right sequence of overt terminals. The cyclic
linearization machinery from `Linearization/Cyclic.lean` checks for
ordering contradictions. The key theorem is that object extraction with
overt Voice creates a contradiction, while null Voice does not.
-/

namespace ErlewineSommerlot2025

open Minimalist.Linearization
open Malayic.VoiceSystem

-- ============================================================================
-- § 1: VoiceP Linearizations
-- ============================================================================

/-! ### Overt terminals at VoiceP Spell-out

At VoiceP Spell-out, the phase is:
```
[VoiceP  DP_spec  Voice  [vP  (DP_agent)  v+V  (DP_theme)]]
```
The specifier of VoiceP is the nominal that has moved there to satisfy
the single-specifier requirement. In active clauses, this is the agent;
in passives, the theme; in object extraction, the theme.

We record the left-to-right sequence of overt terminals. Null heads
(Voice = ∅, v_PASS = ∅) are omitted from the sequence.
-/

-- Active clause: agent in Spec,VoiceP; theme is complement of V
-- Overt: [agent, Voice(me-), v(N-)+V, theme]
def voiceP_active : List String := ["agent", "me-", "NV", "theme"]

-- Active with short N- only (Desa free variation)
def voiceP_active_short : List String := ["agent", "NV", "theme"]

-- Di-passive: theme in Spec,VoiceP; no agent in Spec,vP (or optional PP)
-- Overt: [theme, Voice(di-), V]
def voiceP_diPassive : List String := ["theme", "di-", "V"]

-- Bare passive: theme in Spec,VoiceP; agent in Spec,vP; Voice = ∅, v = ∅
-- Overt: [theme, agent, V]
def voiceP_barePassive : List String := ["theme", "agent", "V"]

-- Object extraction with NULL Voice: theme in Spec,VoiceP; agent in Spec,vP
-- Voice = ∅; v_ACT = N- (Desa) or ∅ (SI/SM)
def voiceP_objExtr_null : List String := ["theme", "agent", "NV"]
def voiceP_objExtr_null_sism : List String := ["theme", "agent", "V"]

-- Object extraction with OVERT Voice (hypothetical — leads to crash)
-- Theme in Spec,VoiceP; Voice = me-; agent in Spec,vP
def voiceP_objExtr_overt : List String := ["theme", "me-", "agent", "NV"]

-- ============================================================================
-- § 2: CP Linearizations
-- ============================================================================

/-! ### Overt terminals at CP Spell-out

At CP Spell-out, material that has moved out of VoiceP is ordered
relative to VoiceP-internal material and any new CP-level material
(complementizer, auxiliaries). The key principle: moved material
precedes VoiceP-internal material in the CP Spell-out domain.
-/

-- Active clause: agent moves from Spec,VoiceP to Spec,TP
-- CP: [agent, Aux, me-, NV, theme]
def cp_active : List String := ["agent", "Aux", "me-", "NV", "theme"]
def cp_active_short : List String := ["agent", "Aux", "NV", "theme"]

-- Subject extraction from active: agent further moves to Spec,CP
-- CP: [agent, Aux, me-, NV, theme]  (same linear order)
def cp_subjExtr : List String := ["agent", "Aux", "me-", "NV", "theme"]

-- Di-passive: theme moves from Spec,VoiceP to Spec,TP
-- CP: [theme, Aux, di-, V]
def cp_diPassive : List String := ["theme", "Aux", "di-", "V"]

-- Bare passive: theme moves to Spec,TP; agent stays in Spec,vP (low)
-- CP: [theme, Aux, agent, V]
def cp_barePassive : List String := ["theme", "Aux", "agent", "V"]

-- Object extraction (SI/SM, ex. 56): theme → Spec,CP; agent → Spec,TP
-- Both move simultaneously out of VoiceP in order-preserving fashion
-- Voice is null → not in linearization
-- CP: [theme, agent, Aux, V]
def cp_objExtr_sism : List String := ["theme", "agent", "Aux", "V"]

-- Object extraction (Desa, ex. 44): theme → Spec,CP; agent stays low
-- No auxiliary precedes agent (Desa-specific: EPP relaxed)
-- CP: [theme, agent, NV]
def cp_objExtr_desa : List String := ["theme", "agent", "NV"]

-- Object extraction with OVERT Voice (hypothetical crash)
-- agent has moved past Voice → agent < me- at CP, but me- < agent at VoiceP
-- CP: [theme, agent, Aux, me-, NV]
def cp_objExtr_overt : List String := ["theme", "agent", "Aux", "me-", "NV"]

-- ============================================================================
-- § 3: Core Derivation Theorems
-- ============================================================================

/-! ### Grammatical derivations

Each grammatical derivation produces consistent ordering across phases.
-/

/-- Active clause is consistently linearizable.
    [erlewine-sommerlot-2025] (36). -/
theorem active_consistent :
    SpelloutAndCheck [voiceP_active, cp_active] := by decide

/-- Active clause with short *N-* prefix (Desa free variation). -/
theorem active_short_consistent :
    SpelloutAndCheck [voiceP_active_short, cp_active_short] := by decide

/-- Subject extraction from active is consistent.
    The subject (agent) was already leftmost in VoiceP and moves further
    left through Spec,TP to Spec,CP — classic edge movement (Scenario 1
    of [fox-pesetsky-2005]). -/
theorem subject_extraction_consistent :
    SpelloutAndCheck [voiceP_active, cp_subjExtr] := by decide

/-- *di-* passive is consistently linearizable.
    [erlewine-sommerlot-2025] (37a). -/
theorem di_passive_consistent :
    SpelloutAndCheck [voiceP_diPassive, cp_diPassive] := by decide

/-- Bare passive is consistently linearizable.
    [erlewine-sommerlot-2025] (37b)/(39c). -/
theorem bare_passive_consistent :
    SpelloutAndCheck [voiceP_barePassive, cp_barePassive] := by decide

/-- Object extraction with null Voice (Desa) is consistent.
    [erlewine-sommerlot-2025] (44). -/
theorem obj_extraction_desa_consistent :
    SpelloutAndCheck [voiceP_objExtr_null, cp_objExtr_desa] := by decide

/-- Object extraction with null Voice (SI/SM) is consistent.
    [erlewine-sommerlot-2025] (54)–(56). -/
theorem obj_extraction_sism_consistent :
    SpelloutAndCheck [voiceP_objExtr_null_sism, cp_objExtr_sism] := by decide

/-! ### The ordering paradox: overt Voice in object extraction

This is the paper's central formal result. When Voice is overt (*me-*),
VoiceP Spell-out establishes *me-* < agent (Voice precedes agent in
Spec,*v*P). But at CP Spell-out, the agent has moved past Voice,
establishing agent < *me-*. The two are contradictory.

[erlewine-sommerlot-2025] (57).
-/

/-- **meN-deletion theorem**: object extraction with overt Voice
    creates an ordering paradox.

    VoiceP: [theme, **me-**, **agent**, NV]  →  me- < agent
    CP:     [theme, **agent**, Aux, **me-**, NV]  →  agent < me-

    These two statements contradict: me- < agent ∧ agent < me-. -/
theorem men_deletion :
    ¬ SpelloutAndCheck [voiceP_objExtr_overt, cp_objExtr_overt] := by decide

/-- The specific contradiction: VoiceP says me- before agent;
    CP says agent before me-. -/
theorem men_deletion_witness :
    -- me- < agent from VoiceP
    (allPrecs voiceP_objExtr_overt).any
      (λ s => s.before == "me-" && s.after == "agent") = true ∧
    -- agent < me- from CP
    (allPrecs cp_objExtr_overt).any
      (λ s => s.before == "agent" && s.after == "me-") = true ∧
    -- combined is inconsistent
    HasContradiction
      (allPrecs voiceP_objExtr_overt ++ allPrecs cp_objExtr_overt) := by decide

-- ============================================================================
-- § 4: Cross-Linguistic Predictions
-- ============================================================================

/-! ### Desa vs SI/SM: the *N-* contrast

In Desa, the short nasal prefix *N-* (realization of *v_ACT*) survives
in object extraction because it is on the lower head *v*, which is not
implicated in the ordering paradox. In SI/SM, *N-* is lost because
*v_ACT* only realizes as *N-* when Voice is linearly adjacent — and in
object extraction, Voice is null (pruned), so the adjacency condition
fails.

[erlewine-sommerlot-2025] §2.3, (3) vs (22), (25).
-/

/-- Desa object extraction: verb bears short *N-* but not *me-*.
    Desa (3): *Opai yang inya m-ewa'* 'What did s/he bring?'
    *m-* = *N-* (v_ACT), no *me-* (Voice). -/
theorem desa_n_survives :
    desa.vExponent .objectExtraction = some "N-" ∧
    desa.voiceExponent .objectExtraction = none := ⟨rfl, rfl⟩

/-- SI/SM object extraction: verb bears NO prefix at all.
    SI/SM (22): *baju-baju yang Ali tidak basuh*
    No *meN-*, no *N-*, bare stem *basuh*. -/
theorem sism_full_deletion :
    standardSISM.vExponent .objectExtraction = none ∧
    standardSISM.voiceExponent .objectExtraction = none := ⟨rfl, rfl⟩

-- ============================================================================
-- § 5: Madurese Register Variation
-- ============================================================================

/-! ### Polite vs familiar Madurese

[jeoung-2017] documents that polite Madurese has three voices
(active, *e-* passive, bare passive) plus object extraction, while
familiar Madurese has only two voices (active, *e-* passive). The
contrast reduces to whether Voice has a null elsewhere allomorph.

[erlewine-sommerlot-2025] §5.3, (76)–(83).
-/

/-- Polite Madurese allows object extraction (null Voice available). -/
theorem polite_madurese_obj_extr :
    politeMadurese.clauseAvailable .objectExtraction = true := rfl

/-- Familiar Madurese blocks object extraction (no null Voice). -/
theorem familiar_madurese_no_obj_extr :
    familiarMadurese.clauseAvailable .objectExtraction = false := rfl

/-- The register contrast is exactly the null-Voice parameter. -/
theorem madurese_minimal_pair :
    politeMadurese.hasNullVoice ≠ familiarMadurese.hasNullVoice := by decide

-- ============================================================================
-- § 6: Nonnominal Extraction Is Voice-Insensitive
-- ============================================================================

/-! ### PP A'-movement

[erlewine-sommerlot-2025] correctly predict that nonnominal
constituents (PPs) can A'-extract freely, regardless of voice, because
VoiceP hosts nonnominal specifiers in addition to its one nominal
specifier ((35b), (42)). PP extraction from active clauses retains
*meN-* ((40a), (41a)).

We model this as: a PP in an additional specifier of VoiceP moves to
Spec,CP. It is ordered before Voice at VoiceP Spell-out and remains
before Voice at CP Spell-out — no contradiction regardless of whether
Voice is overt.
-/

-- PP extraction from active: PP occupies additional spec of VoiceP
-- VoiceP: [PP, agent, me-, NV, theme]  (PP is leftmost, then agent)
-- CP: [PP, agent, Aux, me-, NV, theme]
theorem pp_extraction_with_overt_voice :
    SpelloutAndCheck [["PP", "agent", "me-", "NV", "theme"],
                      ["PP", "agent", "Aux", "me-", "NV", "theme"]] := by
  decide

-- ============================================================================
-- § 7: Summary Prediction Table
-- ============================================================================

/-- Summary: for every basic clause type, the derivation with
    appropriate null/overt Voice assignments is consistently linearizable.
    Object extraction requires null Voice (derived, not stipulated). -/
theorem all_grammatical_derivations_consistent :
    -- Active (with me-N-)
    SpelloutAndCheck [voiceP_active, cp_active] ∧
    -- Active (with N- only, Desa)
    SpelloutAndCheck [voiceP_active_short, cp_active_short] ∧
    -- Di-passive
    SpelloutAndCheck [voiceP_diPassive, cp_diPassive] ∧
    -- Bare passive
    SpelloutAndCheck [voiceP_barePassive, cp_barePassive] ∧
    -- Object extraction, null Voice (Desa)
    SpelloutAndCheck [voiceP_objExtr_null, cp_objExtr_desa] ∧
    -- Object extraction, null Voice (SI/SM)
    SpelloutAndCheck [voiceP_objExtr_null_sism, cp_objExtr_sism] ∧
    -- Object extraction, overt Voice → CRASH
    ¬ SpelloutAndCheck [voiceP_objExtr_overt, cp_objExtr_overt] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 8: Bridge to Core Minimalist Voice Theory
-- ============================================================================

/-! ### Connecting Malayic Voice/v to Core VoiceHead

[erlewine-sommerlot-2025]'s two-head system (Voice + v) maps onto
Core's single `VoiceHead` type ([kratzer-1996], [schaefer-2008]).

- v_ACT (introduces agent) → agentive Voice flavor
- v_PASS (no θ) → passive Voice flavor
- VoiceP is ALWAYS a phase in E&S's system, diverging from Core's
  flavor-default tabulation in which passive Voice is non-phasal
  ([collins-2005], [chomsky-2001]). This divergence is captured
  by the `malayic_passive_phase_diverges` theorem below.

The phase divergence is theoretically significant: E&S need VoiceP to be
a phase in ALL clause types to trigger cyclic linearization at VoiceP
Spell-out, including in passives. Phase.lean's `Transfer` corresponds
to each Spell-out domain in `Linearization/Cyclic.lean`, but operates on
`SyntacticObject` rather than terminal strings.
-/

/-- Map Malayic v-flavor to Core VoiceFlavor.
    v_ACT introduces the external argument → agentive.
    v_PASS licenses EA without θ → passive. -/
def vFlavorToCore : LittleVFlavor → Minimalist.VoiceFlavor
  | .act  => .agentive
  | .pass => .passive

/-- Map each Malayic clause type to its Core VoiceHead equivalent.
    Active and object-extraction Voice are agentive (flavor-default phasal).
    `di-`passive and bare passive use `phaseOverride := some true` to express
    E&S 2025's claim that VoiceP is universally a phase, diverging from the
    Core default for passive Voice ([chomsky-2001], [collins-2005],
    encoded in `VoiceFlavor.defaultPhasal`). -/
def clauseToVoiceHead : VoiceConstruction → Minimalist.VoiceHead
  | .active          => { flavor := .agentive, hasD := true }
  | .diPassive       => { flavor := .passive,  hasD := true, phaseOverride := some true }
  | .barePassive     => { flavor := .passive,  hasD := true, phaseOverride := some true }
  | .objectExtraction => { flavor := .agentive, hasD := true }

/-- The VoiceFlavor component is consistent with the v-flavor mapping. -/
theorem voice_flavor_consistent (ct : VoiceConstruction) :
    (clauseToVoiceHead ct).flavor = vFlavorToCore ct.vFlavor := by
  cases ct <;> rfl

/-- All Malayic clause types treat VoiceP as a phase head. -/
theorem voice_always_phase (ct : VoiceConstruction) :
    (clauseToVoiceHead ct).IsPhasal := by cases ct <;> decide

/-- Phase divergence: Malayic passives are phases, but Core's default
    passive Voice (following [collins-2005]) is not. -/
theorem malayic_passive_phase_diverges :
    (clauseToVoiceHead .diPassive).IsPhasal ∧
    ¬ Minimalist.voicePassive.IsPhasal := by decide

/-- Active clause type maps to Core's agentive Voice, which IS a phase
    head — consistent across both analyses. -/
theorem active_consistent_with_core :
    (clauseToVoiceHead .active).flavor = .agentive ∧
    ((clauseToVoiceHead .active).IsPhasal ↔ Minimalist.voiceAgent.IsPhasal) := by
  refine ⟨rfl, ?_⟩; decide

end ErlewineSommerlot2025
