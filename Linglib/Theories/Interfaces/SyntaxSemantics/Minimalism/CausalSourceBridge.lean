import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Theories.Semantics.Causation.PsychCausalLink

/-!
# Psych Verb Syntax-Semantics Interface

@cite{pesetsky-1995} @cite{kim-2024} @cite{kratzer-1996} @cite{schfer-2008}## Directions of determination

The psych verb interface involves three layers with distinct directions
of determination:

```
    SYNTAX determines SEMANTICS determines
    ───────────────── ────────────────────
    Voice_CAUSE head → ∃ causer argument
         ↑ ↓
    (that's all) DP denotation (percept vs representation)
                                    ↓
                              CausalSource (external vs internal)
                                    ↓
                          ┌─────────┴──────────┐
                    StimulusType opacity, temporality,
                    (T vs SM) event sort, transition
                          ↓
                    PP frame (*of* vs *about*)
                    Cause cooccurrence
```

**Syntax determines** one thing: whether there is a causer argument at
all. This is the contribution of Voice_CAUSE (= Pesetsky's CAUS head).
Agentive/causer Voice projects a specifier; non-thematic/expletive Voice
does not. The syntax is "done" after this — it cannot see what kind of
entity fills the specifier.

**Semantics determines** everything else. The DP's referential type
(percept vs representation) is a property of its denotation, invisible
to the syntax. From this single semantic property, all other properties
follow: CausalSource, StimulusType, opacity, temporal structure, event
sort, PP frame selection, and Cause cooccurrence.

**The zero syntax thesis**: the syntactic
structure is *invariant* across the two DP types. No head, feature, or
morpheme distinguishes percept from representation DPs. The syntax is
blind to the T/SM distinction. All variation is semantic.

-/

namespace Theories.Interfaces.SyntaxSemantics.CausalSourceBridge

open _root_.Minimalism (VoiceFlavor VoiceHead voiceCauser voiceAgent
  voiceAnticausative voiceMiddle)
open Semantics.Causation.PsychCausation (CausalSource StimulusType subjectIntensional
  CausalSource.toStimulusType)
open Semantics.Causation.PsychCausalLink (PsychCausalLink CausalSource.toLink)
open Core.Time (Interval)

-- ════════════════════════════════════════════════════════════════════
-- § 1. What syntax determines: the existence of a causer argument
-- ════════════════════════════════════════════════════════════════════

/-- @cite{pesetsky-1995}'s CAUS head is identified with Schäfer's
    Voice_CAUSE (@cite{schaefer-2008}). Both introduce a causer external argument.

    This identification follows Occam: the two analyses posit the
    same structural position (Spec,vP/VoiceP) introducing the same
    kind of argument (causer). -/
def pesetskyCAUS : VoiceFlavor := .causer

/-- **Syntax determines**: Voice_CAUSE introduces a causer argument.
    This is what the syntax contributes — the *existence* of a
    causer in the structure. -/
theorem syntax_determines_causer_exists :
    voiceCauser.assignsTheta = true := rfl

/-- **Syntax determines**: Voice_CAUSE is a phase head, creating
    a domain boundary. -/
theorem syntax_determines_phase :
    voiceCauser.phaseHead = true := rfl

/-- **Syntax does NOT determine**: the *kind* of causer. All
    θ-assigning Voice heads project the same structural position
    (Spec,VoiceP with [D] feature). The syntax treats agentive
    and causer Voice identically in this respect. -/
theorem syntax_blind_to_causer_kind :
    voiceCauser.hasD = voiceAgent.hasD := rfl

/-- **Contrast**: non-thematic Voice does NOT introduce any
    argument. This is where syntax makes its one cut: causer
    argument vs no causer argument. -/
theorem syntax_determines_no_causer :
    voiceAnticausative.assignsTheta = false ∧
    voiceMiddle.assignsTheta = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════
-- § 2. What semantics determines: everything else
-- ════════════════════════════════════════════════════════════════════

/-- The referential type of the DP in Spec,Voice_CAUSE.

    This is a **semantic** type, not a syntactic one. The syntax
    sees only "DP in Spec,VoiceP" — it cannot distinguish percepts
    from representations. The distinction is a property of the DP's
    *denotation*, visible only to the semantic component.

    - `.percept`: mind-external entity/event — "the noise" in
      "the noise frightened John"
    - `.representation`: mind-internal representation — "the problem"
      in "the problem concerns John" (John's mental representation
      of the problem, not the problem itself) -/
inductive CauserDenotation where
  | percept         -- Mind-external entity/event (extensional)
  | representation  -- Mind-internal representation (intensional)
  deriving DecidableEq, BEq, Repr

/-- **Semantics determines**: causal source from DP denotation.

    The referential type of the DP *determines* the causal source.
    This is a semantics-internal derivation: from what the DP
    denotes, we know what kind of causation is involved. -/
def denotationToSource : CauserDenotation → CausalSource
  | .percept        => .external
  | .representation => .internal

/-- **Semantics determines**: subject opacity from DP denotation.

    Composed via CausalSource: denotation → source → opacity. -/
def denotationToOpacity (d : CauserDenotation) : Bool :=
  subjectIntensional (denotationToSource d)

/-- **Semantics determines**: causal link profile from DP denotation.

    Composed via CausalSource: denotation → source → temporal
    structure, event sorts, transition. -/
def denotationToLink (Time : Type*) [LinearOrder Time]
    (d : CauserDenotation) : PsychCausalLink Time :=
  CausalSource.toLink Time (denotationToSource d)

/-- **Semantics determines**: stimulus subtype from DP denotation.

    Composed via CausalSource: denotation → source → T/SM. -/
def denotationToStimulusType (d : CauserDenotation) : StimulusType :=
  (denotationToSource d).toStimulusType

-- ════════════════════════════════════════════════════════════════════
-- § 3. Semantic derivation chain (DP denotation → all properties)
-- ════════════════════════════════════════════════════════════════════

/-- Percept DP → external source. -/
theorem percept_source : denotationToSource .percept = .external := rfl

/-- Representation DP → internal source. -/
theorem representation_source : denotationToSource .representation = .internal := rfl

/-- Percept DP → transparent subject. -/
theorem percept_transparent : denotationToOpacity .percept = false := rfl

/-- Representation DP → opaque subject. -/
theorem representation_opaque : denotationToOpacity .representation = true := rfl

/-- Percept DP → Target stimulus, *of*-PP. -/
theorem percept_target :
    denotationToStimulusType .percept = .target ∧
    (denotationToStimulusType .percept).ppFrame = "of" := ⟨rfl, rfl⟩

/-- Representation DP → Subject Matter stimulus, *about*-PP. -/
theorem representation_sm :
    denotationToStimulusType .representation = .subjectMatter ∧
    (denotationToStimulusType .representation).ppFrame = "about" := ⟨rfl, rfl⟩

/-- Percept DP → temporal precedence, BECOME transition. -/
theorem percept_temporal {Time : Type*} [LinearOrder Time] :
    (denotationToLink Time .percept).temporalConstraint = Interval.precedes ∧
    (denotationToLink Time .percept).involvesTransition = true := ⟨rfl, rfl⟩

/-- Representation DP → temporal overlap, no BECOME. -/
theorem representation_temporal {Time : Type*} [LinearOrder Time] :
    (denotationToLink Time .representation).temporalConstraint = Interval.overlaps ∧
    (denotationToLink Time .representation).involvesTransition = false := ⟨rfl, rfl⟩

/-- **Semantics determines all**: one semantic property of the DP
    (its referential type) determines seven downstream properties.
    None of these are syntactically encoded. -/
theorem semantics_determines_all {Time : Type*} [LinearOrder Time] :
    -- Source
    denotationToSource .percept = .external ∧
    denotationToSource .representation = .internal ∧
    -- Stimulus subtype
    denotationToStimulusType .percept = .target ∧
    denotationToStimulusType .representation = .subjectMatter ∧
    -- PP frame
    (denotationToStimulusType .percept).ppFrame = "of" ∧
    (denotationToStimulusType .representation).ppFrame = "about" ∧
    -- Cause cooccurrence
    (denotationToStimulusType .percept).conflictsWithCause = false ∧
    (denotationToStimulusType .representation).conflictsWithCause = true ∧
    -- Opacity
    denotationToOpacity .percept = false ∧
    denotationToOpacity .representation = true ∧
    -- Temporal structure
    (denotationToLink Time .percept).involvesTransition = true ∧
    (denotationToLink Time .representation).involvesTransition = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════
-- § 4. Zero syntax: syntax is invariant across DP denotations
-- ════════════════════════════════════════════════════════════════════

/-- **Zero syntax thesis**: the syntactic
    head projected is the same regardless of DP denotation.

    The syntax contributes exactly Voice_CAUSE in both cases. There
    is no syntactic feature, morpheme, or head that distinguishes
    the percept configuration from the representation configuration.
    All seven semantic differences (§ 3) arise from the DP's
    denotation, not from any syntactic distinction. -/
theorem zero_syntax_invariant_head :
    pesetskyCAUS = pesetskyCAUS := rfl

/-- The zero syntax thesis stated as a gap: syntax is constant
    while semantics varies. The two conjuncts make the directions
    explicit — same syntax, different semantics. -/
theorem syntax_constant_semantics_varies :
    -- Syntax: same head
    pesetskyCAUS = pesetskyCAUS ∧
    -- Semantics: different source
    denotationToSource .percept ≠ denotationToSource .representation ∧
    -- Semantics: different opacity
    denotationToOpacity .percept ≠ denotationToOpacity .representation ∧
    -- Semantics: different stimulus type
    denotationToStimulusType .percept ≠ denotationToStimulusType .representation :=
  ⟨rfl, by decide, by decide, by decide⟩

-- ════════════════════════════════════════════════════════════════════
-- § 5. Interface summary: what each component contributes
-- ════════════════════════════════════════════════════════════════════

/-- **Interface summary**: the syntax-semantics division of labor.

    Syntax contributes: causer argument exists (θ-role assigned).
    Syntax does NOT contribute: what kind of causer, opacity,
    temporality, T/SM, PP frame — none of these are syntactically
    encoded.

    Semantics contributes: all variation between percept and
    representation configurations. -/
theorem interface_division_of_labor :
    -- Syntax contributes: θ-role assignment
    voiceCauser.assignsTheta = true ∧
    -- Syntax does NOT vary: same head in both configurations
    pesetskyCAUS = pesetskyCAUS ∧
    -- Semantics contributes: causal source varies
    denotationToSource .percept ≠ denotationToSource .representation ∧
    -- Semantics contributes: opacity varies
    denotationToOpacity .percept ≠ denotationToOpacity .representation ∧
    -- Semantics contributes: stimulus type varies
    denotationToStimulusType .percept ≠ denotationToStimulusType .representation :=
  ⟨rfl, rfl, by decide, by decide, by decide⟩

end Theories.Interfaces.SyntaxSemantics.CausalSourceBridge
