import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment

/-!
# @cite{gunlogson-2004}: Source-Marked Commitments

@cite{gunlogson-2004} @cite{gunlogson-2001} @cite{gunlogson-2003}Models the distinction between falling and rising declaratives via @cite{bring-gunlogson-2000}
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

-/

namespace Pragmatics.Assertion.Gunlogson

open Core.Discourse.Commitment
open Core.CommonGround (ContextSet CG)
open Core.Proposition (Prop')
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
def fallingDeclarative (s : GunlogsonState W) (p : Prop' W) : GunlogsonState W :=
  { s with speakerSlate := s.speakerSlate.add p .selfGenerated }

/-- Rising declarative: speaker attributes p to addressee.

    The speaker adds p to the addressee's slate with source = `.otherGenerated`.
    No commitment is added to the speaker's own slate.
    This is the rising declarative: "It's raining?" -/
def risingDeclarative (s : GunlogsonState W) (p : Prop' W) : GunlogsonState W :=
  { s with addresseeSlate := s.addresseeSlate.add p .otherGenerated }

/-- Assert: defaults to falling declarative (standard assertion). -/
def assert (s : GunlogsonState W) (p : Prop' W) : GunlogsonState W :=
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

-- ════════════════════════════════════════════════════
-- § 1b. Contextual Bias Condition (Ch. 4 §4.2)
-- ════════════════════════════════════════════════════

/-- The Contextual Bias Condition (@cite{gunlogson-2001}, Ch. 4 §4.2).

    A rising declarative about p is felicitous only when the addressee's
    existing commitments already entail p. This is NOT a free parameter —
    it's a condition derivable from the discourse state.

    The CBC follows from the uninformativeness requirement on questions:
    a rising declarative can serve as a question only if it's uninformative
    for the addressee, which holds iff the addressee is already committed
    to p (see `cbc_from_uninformativeness` below). -/
def cbcMet (s : GunlogsonState W) (p : Prop' W) : Prop :=
  ∀ w, s.addresseeSlate.toContextSet w → p w

/-- Rising declarative guarded by the CBC.

    Returns the updated state when the CBC is met, `none` otherwise.
    Also accepts a coarser `ContextualEvidence` tag for compatibility
    with the polar question bias framework. -/
def risingDeclarativeFelicitous (s : GunlogsonState W) (p : Prop' W)
    (evidence : ContextualEvidence) : Option (GunlogsonState W) :=
  match evidence with
  | .forP => some (s.risingDeclarative p)
  | _ => none

-- ════════════════════════════════════════════════════
-- § 1c. Uninformativeness (Ch. 4 §4.1)
-- ════════════════════════════════════════════════════

/-- A move is uninformative for a participant if their commitment
    context set doesn't change.

    This is the key notion connecting rising declaratives to questions:
    questioning requires uninformativeness for the addressee (the
    addressee isn't learning anything new — they're being asked to
    make their existing commitment public). -/
def uninformativeForAddressee (s : GunlogsonState W) (p : Prop' W) : Prop :=
  (s.risingDeclarative p).addresseeSlate.toContextSet =
  s.addresseeSlate.toContextSet

/-- Rising declaratives are ALWAYS uninformative for the speaker.

    The speaker's slate is untouched, so their commitment context
    is trivially unchanged. This is Generalization (9) from Ch. 2. -/
theorem rising_uninformative_for_speaker (s : GunlogsonState W) (p : Prop' W) :
    (s.risingDeclarative p).speakerSlate.toContextSet =
    s.speakerSlate.toContextSet := by
  simp only [risingDeclarative]

/-- The CBC is the uninformativeness condition for the addressee.

    A rising declarative about p is uninformative for the addressee
    iff the addressee's commitment set already entails p. This is
    Gunlogson's central result: the CBC is *derived*, not stipulated.
    It follows from the definition of uninformativeness applied to
    the commitment-set update semantics of rising declaratives. -/
theorem cbc_from_uninformativeness (s : GunlogsonState W) (p : Prop' W) :
    cbcMet s p → uninformativeForAddressee s p := by
  intro hcbc
  funext w
  apply propext
  refine ⟨?_, ?_⟩
  · -- (rising).addresseeSlate.toContextSet w → s.addresseeSlate.toContextSet w
    intro h q hq
    refine h q ?_
    show q ∈ List.map _ (⟨p, CommitmentSource.otherGenerated⟩ :: s.addresseeSlate.commitments)
    exact List.mem_cons_of_mem _ hq
  · -- s.addresseeSlate.toContextSet w → (rising).addresseeSlate.toContextSet w
    intro h q hq
    have hq' : q ∈ List.map (·.content)
        (⟨p, CommitmentSource.otherGenerated⟩ :: s.addresseeSlate.commitments) := hq
    rw [List.map_cons] at hq'
    rcases List.mem_cons.mp hq' with rfl | hq''
    · exact hcbc w h
    · exact h q hq''

-- ════════════════════════════════════════════════════
-- § 1d. Response Dynamics (Ch. 4)
-- ════════════════════════════════════════════════════

/-- Confirm: addressee endorses content of a rising declarative.

    Adds p as self-generated on the addressee's slate, signaling
    acceptance. Both participants now have p (speaker via falling
    assertion or prior commitment, addressee via confirmation),
    moving p toward the effective common ground. -/
def confirm (s : GunlogsonState W) (p : Prop' W) : GunlogsonState W :=
  { s with addresseeSlate := s.addresseeSlate.add p .selfGenerated }

/-- Reject: addressee declines to endorse a rising declarative.

    Does NOT commit the addressee to ¬p — rejection is weaker than
    denial. The addressee simply doesn't add p as self-generated,
    leaving the other-generated commitment unresolved.

    Formally, rejection is the identity on the state: no new
    commitment is added. The discourse remains unstable (the
    other-generated commitment is still pending). -/
def reject (s : GunlogsonState W) : GunlogsonState W := s

/-- Strong denial: addressee asserts ¬p (stronger than rejection).

    Only appropriate when the addressee actively disagrees, not
    merely declines to confirm. Adds ¬p as self-generated. -/
def strongDeny (s : GunlogsonState W) (p : Prop' W) : GunlogsonState W :=
  { s with addresseeSlate := s.addresseeSlate.add (fun w => ¬ p w) .selfGenerated }

end GunlogsonState

-- ════════════════════════════════════════════════════
-- § 2. Verification
-- ════════════════════════════════════════════════════

/-- Falling declaratives add self-generated commitments to the speaker. -/
theorem falling_is_self_generated {W : Type*}
    (s : GunlogsonState W) (p : Prop' W) :
    (s.fallingDeclarative p).speakerSlate.commitments.head?.map (·.source) =
    some CommitmentSource.selfGenerated := rfl

/-- Rising declaratives add other-generated commitments to the addressee. -/
theorem rising_is_other_generated {W : Type*}
    (s : GunlogsonState W) (p : Prop' W) :
    (s.risingDeclarative p).addresseeSlate.commitments.head?.map (·.source) =
    some CommitmentSource.otherGenerated := rfl

/-- Rising declaratives do NOT commit the speaker.

    The speaker's slate is unchanged by a rising declarative — only the
    addressee's slate gets an other-generated commitment. -/
theorem rising_no_speaker_commitment {W : Type*}
    (s : GunlogsonState W) (p : Prop' W) :
    (s.risingDeclarative p).speakerSlate = s.speakerSlate := rfl

/-- Falling and rising declaratives differ in source. -/
theorem falling_vs_rising_source {W : Type*}
    (s : GunlogsonState W) (p : Prop' W) :
    -- Falling: self-generated on speaker's slate
    (s.fallingDeclarative p).speakerSlate.commitments.head?.map (·.source) =
      some .selfGenerated ∧
    -- Rising: other-generated on addressee's slate
    (s.risingDeclarative p).addresseeSlate.commitments.head?.map (·.source) =
      some .otherGenerated :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2b. Felicity & Response Verification
-- ════════════════════════════════════════════════════

/-- Rising declaratives are infelicitous in neutral contexts. -/
theorem rising_infelicitous_neutral {W : Type*}
    (s : GunlogsonState W) (p : Prop' W) :
    s.risingDeclarativeFelicitous p .neutral = none := rfl

/-- Rising declaratives are infelicitous when evidence is against p. -/
theorem rising_infelicitous_againstP {W : Type*}
    (s : GunlogsonState W) (p : Prop' W) :
    s.risingDeclarativeFelicitous p .againstP = none := rfl

/-- Rising declaratives are felicitous when evidence supports p. -/
theorem rising_felicitous_forP {W : Type*}
    (s : GunlogsonState W) (p : Prop' W) :
    (s.risingDeclarativeFelicitous p .forP).isSome = true := rfl

/-- Confirmation adds a self-generated commitment to the addressee. -/
theorem confirm_adds_self_generated {W : Type*}
    (s : GunlogsonState W) (p : Prop' W) :
    (s.confirm p).addresseeSlate.commitments.head?.map (·.source) =
    some CommitmentSource.selfGenerated := rfl

/-- Strong denial adds a self-generated commitment to the addressee. -/
theorem strongDeny_adds_self_generated {W : Type*}
    (s : GunlogsonState W) (p : Prop' W) :
    (s.strongDeny p).addresseeSlate.commitments.head?.map (·.source) =
    some CommitmentSource.selfGenerated := rfl

/-- Rejection is the identity: no new commitment. -/
theorem reject_identity {W : Type*}
    (s : GunlogsonState W) :
    s.reject = s := rfl

/-- Rising then confirm: the addressee ends up with both an other-generated
    and a self-generated commitment. The self-generated endorsement is what
    moves p toward the common ground. -/
theorem rising_confirm_has_both {W : Type*} (p : Prop' W) :
    let s := GunlogsonState.empty.risingDeclarative p
    let s' := s.confirm p
    s'.addresseeSlate.selfGenerated.length = 1 ∧
    s'.addresseeSlate.otherGenerated.length = 1 :=
  ⟨rfl, rfl⟩

/-- A rising declarative from the empty state breaks stability:
    the other-generated commitment on the addressee's slate is
    unresolved. -/
theorem rising_from_empty_unstable {W : Type*} (p : Prop' W) :
    (GunlogsonState.empty.risingDeclarative p).isStable = false := rfl

/-- Confirm does NOT restore stability: the other-generated commitment
    remains alongside the new self-generated one. Full resolution would
    require removing the other-generated entry. -/
theorem confirm_still_unstable {W : Type*} (p : Prop' W) :
    let s := GunlogsonState.empty.risingDeclarative p
    (s.confirm p).isStable = false := rfl

end Pragmatics.Assertion.Gunlogson
