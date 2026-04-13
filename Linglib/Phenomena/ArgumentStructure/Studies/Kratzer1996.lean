import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# Linking Theory Predictions → Hand-Annotated θ-Roles
@cite{kratzer-1996} @cite{rappaport-hovav-levin-1998}

Two accounts of argument realization make predictions about external
argument theta roles. This bridge file tests each account's predictions
independently against hand-annotated `subjectTheta` in the English
verb fragment. Both are instantiated as `LinkingTheory` (see
`Theories/Interfaces/SyntaxSemantics/Linking.lean`).

## Account 1: Severing

Voice flavor determines the theta role: Voice_AG → agent, Voice_CAUSE →
stimulus. The prediction chain is: verb → Voice selection → theta role.
`Ctx = VoiceFlavor`; `predict` ignores the verb.

The current Voice typology has only two θ-assigning flavors, so it can
only distinguish agent from stimulus. It correctly predicts ~71% of verbs
(all agents + all stimuli), but systematically fails for:
- **Experiencer subjects** (know, believe, enjoy,...): Voice_AG predicts
  agent, but the actual role is experiencer. The typology lacks a
  Voice_EXPERIENCER flavor.
- **Theme subjects** (arrive, glow, whisper,...): Voice_nonThematic
  predicts none (no external argument), but the subject IS the internal
  argument that moved. The severing account correctly predicts no
  *external* argument; the subject's theta role comes from V, not Voice.

## Account 2: Lexicalist (@cite{levin-1993}, Rappaport @cite{rappaport-hovav-levin-1998})

The verb's lexical semantics determines the theta role, bypassing Voice.
`Ctx = Unit`; `predict` ignores structure. Uses attitude,
causalSource, objectTheta, factivePresup, levinClass, unaccusative,
controlType — all verb-internal semantic properties.

Correctly predicts ~93% of verbs. Fails for 6 genuinely irreducible
cases (sweep, remember, forget, dare, bother, hesitate) and 6 verbs
with missing annotations.
-/

-- ════════════════════════════════════════════════════════════════════════
-- NOTE: The per-verb θ-role comparison theorems (Parts I–II) have been
-- removed following the removal of `subjectTheta`/`objectTheta` fields
-- from VerbCore. The severing vs. lexicalist linking theory comparison
-- infrastructure lives in VoiceTheta.lean. The causative alternation
-- tree derivations (Part III) remain below.
-- ════════════════════════════════════════════════════════════════════════

namespace Phenomena.ArgumentStructure.Studies.Kratzer1996

open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════════════════════════
-- PART III: Tree-Based Derivations — Causative Alternation
-- ════════════════════════════════════════════════════════════════════════

/-! The causative alternation is the structural prediction of Voice
severing: transitive "John broke the vase" has agentive Voice with an
agent in Spec,VoiceP; anticausative "The vase broke" has non-thematic
Voice with no specifier. Both share the same VP core. Event-structure
predictions are verified in `Core/Voice.lean` via `buildDecomposition`. -/

section TreeDerivations

open Minimalism

-- Leaf tokens

def voice_ag_t  := mkLeafPhon .Voice [.v]  "Voice[AG]"  200
def voice_nth_t := mkLeafPhon .Voice [.v]  "Voice[∅]"   210
def voice_mid_t := mkLeafPhon .Voice [.v]  "Voice[MID]" 211
def v_head_t    := mkLeafPhon .v     [.V]  "v"          201
def V_broke_t   := mkLeafPhon .V     [.D]  "broke"      212
def V_sank_t    := mkLeafPhon .V     [.D]  "sank"       213
def V_opened_t  := mkLeafPhon .V     [.D]  "opened"     214
def DP_john_t   := mkLeafPhon .D     []    "John"       206
def DP_vase_t   := mkLeafPhon .D     []    "the vase"   215
def DP_ship_t   := mkLeafPhon .D     []    "the ship"   216
def DP_door_t   := mkLeafPhon .D     []    "the door"   217

-- Tree derivations

/-- Transitive: "John broke the vase"
    `[VoiceP John [Voice' Voice_AG [vP v [VP broke [DP the vase]]]]]` -/
def transitiveTree : SyntacticObject :=
  merge DP_john_t
    (merge voice_ag_t
      (merge v_head_t
        (merge V_broke_t DP_vase_t)))

/-- Anticausative: "The vase broke"
    `[VoiceP Voice_∅ [vP v [VP broke [DP the vase]]]]` -/
def anticausativeTree : SyntacticObject :=
  merge voice_nth_t
    (merge v_head_t
      (merge V_broke_t DP_vase_t))

/-- Unaccusative: "The ship sank"
    `[VoiceP Voice_∅ [vP v [VP sank [DP the ship]]]]` -/
def unaccusativeTree : SyntacticObject :=
  merge voice_nth_t
    (merge v_head_t
      (merge V_sank_t DP_ship_t))

/-- Middle: "The door opened"
    `[VoiceP Voice_MID [vP v [VP opened [DP the door]]]]` -/
def middleTree : SyntacticObject :=
  merge voice_mid_t
    (merge v_head_t
      (merge V_opened_t DP_door_t))

-- C-command predictions

/-- Agent c-commands theme in the transitive. -/
theorem transitive_agent_ccommands_theme :
    cCommandsInB transitiveTree DP_john_t DP_vase_t = true := by native_decide

/-- Theme does NOT c-command agent. -/
theorem transitive_theme_not_ccommands_agent :
    cCommandsInB transitiveTree DP_vase_t DP_john_t = false := by native_decide

/-- Anticausative contains theme but no agent DP. -/
theorem anticausative_contains_theme :
    containsB anticausativeTree DP_vase_t = true := by native_decide

/-- Unaccusative contains theme. -/
theorem unaccusative_contains_theme :
    containsB unaccusativeTree DP_ship_t = true := by native_decide

/-- Middle contains theme. -/
theorem middle_contains_theme :
    containsB middleTree DP_door_t = true := by native_decide

-- Causative alternation

/-- The transitive and anticausative share the VP core:
    both contain V("broke") and DP("the vase"). -/
theorem causative_pair_shared_vp :
    containsB transitiveTree V_broke_t = true ∧
    containsB transitiveTree DP_vase_t = true ∧
    containsB anticausativeTree V_broke_t = true ∧
    containsB anticausativeTree DP_vase_t = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- The transitive has an agent DP; the anticausative does not. -/
theorem causative_pair_agent_contrast :
    containsB transitiveTree DP_john_t = true ∧
    containsB anticausativeTree DP_john_t = false := by
  constructor <;> native_decide

/-- Voice determines the alternation: agentive assigns θ,
    non-thematic does not. This is @cite{kratzer-1996}'s severing
    verified structurally on the tree derivations. -/
theorem causative_pair_voice_contrast :
    voiceAgent.assignsTheta = true ∧
    voiceAnticausative.assignsTheta = false := ⟨rfl, rfl⟩

end TreeDerivations

end Phenomena.ArgumentStructure.Studies.Kratzer1996
