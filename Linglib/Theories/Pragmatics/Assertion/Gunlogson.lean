import Linglib.Core.Discourse.Commitment
import Linglib.Core.Interfaces.AssertionTheory
import Linglib.Core.Discourse.DiscourseRole

/-!
# Gunlogson (2001): Source-Marked Commitments

@cite{gunlogson-2001}

Models the distinction between falling and rising declaratives via
source-marked discourse commitments. The key innovation: commitments
carry a tag indicating whether they are self-generated (from the
speaker's own evidence) or other-generated (attributed to the addressee).

## Falling vs Rising Declaratives

| Intonation | Example | Source | Speaker committed? |
|------------|---------|--------|--------------------|
| Falling ↓ | "It's raining." | self-generated | Yes |
| Rising ↑ | "It's raining?" | other-generated | No |

A falling declarative commits the speaker to the content (self-generated).
A rising declarative attributes the content to the addressee (other-generated)
without speaker commitment. This explains why rising declaratives can be
used to check or confirm information.

## Challengeability

Source determines who can challenge:
- Self-generated commitments can be challenged by the addressee
  ("Why do you think that?")
- Other-generated commitments can be challenged by the speaker
  ("Is that really what you think?")

## References

- Gunlogson, C. (2001). *True to Form: Rising and Falling Declaratives
  as Questions in English*. PhD dissertation, UC Santa Cruz.
- Gunlogson, C. (2003). *True to Form*. Routledge.
-/

namespace Theories.Pragmatics.Assertion.Gunlogson

open Core.Discourse.Commitment
open Core.CommonGround (ContextSet CG)
open Core.Proposition (BProp)
open Core.Discourse (DiscourseRole)

-- ════════════════════════════════════════════════════
-- § 1. Gunlogson State
-- ════════════════════════════════════════════════════

/-- Gunlogson's discourse state: source-tagged commitment slates
    for speaker and addressee.

    Unlike Stalnaker (single CG) or Farkas & Bruce (dcS + dcL + cg),
    Gunlogson tracks the SOURCE of each commitment, not just which
    participant holds it. -/
structure GunlogsonState (W : Type*) where
  /-- Speaker's source-tagged commitments -/
  speakerSlate : TaggedSlate W
  /-- Addressee's source-tagged commitments -/
  addresseeSlate : TaggedSlate W

namespace GunlogsonState

variable {W : Type*}

/-- Initial state: no commitments for either participant. -/
def empty : GunlogsonState W :=
  ⟨TaggedSlate.empty, TaggedSlate.empty⟩

/-- Falling declarative: speaker commits self to p.

    The speaker adds p to their own slate with source = `.selfGenerated`.
    This is the standard declarative assertion: "It's raining." -/
def fallingDeclarative (s : GunlogsonState W) (p : BProp W) : GunlogsonState W :=
  { s with speakerSlate := s.speakerSlate.add p .selfGenerated }

/-- Rising declarative: speaker attributes p to addressee.

    The speaker adds p to the addressee's slate with source = `.otherGenerated`.
    No commitment is added to the speaker's own slate.
    This is the rising declarative: "It's raining?" -/
def risingDeclarative (s : GunlogsonState W) (p : BProp W) : GunlogsonState W :=
  { s with addresseeSlate := s.addresseeSlate.add p .otherGenerated }

/-- Assert: defaults to falling declarative (standard assertion). -/
def assert (s : GunlogsonState W) (p : BProp W) : GunlogsonState W :=
  s.fallingDeclarative p

/-- Context set: intersection of both participants' commitment contexts.
    Only propositions that both participants are committed to (regardless
    of source) contribute to the shared context. -/
def contextSet (s : GunlogsonState W) : ContextSet W :=
  λ w => s.speakerSlate.toContextSet w ∧ s.addresseeSlate.toContextSet w

/-- Stability: stable when neither participant has unresolved
    other-generated commitments. -/
def isStable (s : GunlogsonState W) : Bool :=
  s.speakerSlate.otherGenerated.isEmpty &&
  s.addresseeSlate.otherGenerated.isEmpty

/-- Can the given role challenge a commitment?

    Source determines challengeability:
    - Self-generated → challengeable by the OTHER participant
    - Other-generated → challengeable by the SAME participant -/
def canChallenge (src : CommitmentSource) (role : DiscourseRole) : Bool :=
  match src, role with
  | .selfGenerated, .addressee => true   -- addressee challenges speaker's self-commitment
  | .otherGenerated, .speaker  => true   -- speaker challenges attributed commitment
  | _, _ => false

end GunlogsonState

-- ════════════════════════════════════════════════════
-- § 2. Interface Instance
-- ════════════════════════════════════════════════════

/-- Marker type for Gunlogson's theory. -/
inductive GunlogsonTag | mk

instance : Interfaces.AssertionTheory GunlogsonTag where
  State := GunlogsonState
  initial := GunlogsonState.empty
  assert := GunlogsonState.assert
  contextSet := GunlogsonState.contextSet
  isStable := GunlogsonState.isStable
  separatesCommitmentFromBelief := true
  supportsRetraction := true
  modelsSourceMarking := true

-- ════════════════════════════════════════════════════
-- § 3. Verification
-- ════════════════════════════════════════════════════

/-- Falling declaratives add self-generated commitments to the speaker. -/
theorem falling_is_self_generated {W : Type*}
    (s : GunlogsonState W) (p : BProp W) :
    (s.fallingDeclarative p).speakerSlate.commitments.head?.map (·.source) =
    some CommitmentSource.selfGenerated := rfl

/-- Rising declaratives add other-generated commitments to the addressee. -/
theorem rising_is_other_generated {W : Type*}
    (s : GunlogsonState W) (p : BProp W) :
    (s.risingDeclarative p).addresseeSlate.commitments.head?.map (·.source) =
    some CommitmentSource.otherGenerated := rfl

/-- Rising declaratives do NOT commit the speaker.

    The speaker's slate is unchanged by a rising declarative — only the
    addressee's slate gets an other-generated commitment. -/
theorem rising_no_speaker_commitment {W : Type*}
    (s : GunlogsonState W) (p : BProp W) :
    (s.risingDeclarative p).speakerSlate = s.speakerSlate := rfl

/-- Falling and rising declaratives differ in source. -/
theorem falling_vs_rising_source {W : Type*}
    (s : GunlogsonState W) (p : BProp W) :
    -- Falling: self-generated on speaker's slate
    (s.fallingDeclarative p).speakerSlate.commitments.head?.map (·.source) =
      some .selfGenerated ∧
    -- Rising: other-generated on addressee's slate
    (s.risingDeclarative p).addresseeSlate.commitments.head?.map (·.source) =
      some .otherGenerated :=
  ⟨rfl, rfl⟩

/-- Gunlogson is the only theory that models source marking. -/
theorem models_source_marking :
    Interfaces.AssertionTheory.modelsSourceMarking (T := GunlogsonTag) = true := rfl

end Theories.Pragmatics.Assertion.Gunlogson
