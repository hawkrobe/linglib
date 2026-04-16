import Linglib.Core.Semantics.CommonGround

/-!
# Discourse Commitments
@cite{krifka-2015} @cite{brandom-1994} @cite{gunlogson-2001} @cite{bring-gunlogson-2000}

The public trace of speech acts: commitment slates, source-tagged commitments,
and contextual evidence bias. Pairs with `Core/Discourse/IllocutionaryForce.lean`
(F in F(p)) and `Core/Discourse/Intentionality.lean` (S in S(r)).

Where Intentional states are private, commitments are public — the
publicly-tracked obligations created by performing speech acts. Asserting p
creates a mind-to-world commitment; promising p creates a world-to-mind one.

## Organization

- **§ 1. Commitment Slates** (@cite{krifka-2015}, @cite{brandom-1994})
- **§ 2. Source-Marked Commitments** (@cite{gunlogson-2001})
- **§ 3. Contextual Evidence** (@cite{bring-gunlogson-2000})
- **§ 4. HasContextSet Instance**
-/

namespace Core.Discourse

open Core.Proposition (BProp)

namespace Commitment

-- ════════════════════════════════════════════════════════════════
-- § 1. Commitment Slates (@cite{krifka-2015} @cite{brandom-1994})
-- ════════════════════════════════════════════════════════════════

/-- An agent's public discourse commitments: a list of propositions
    the agent has publicly committed to.

    Following @cite{krifka-2015}: the commitment slate tracks what an agent
    is publicly committed to, which may diverge from what they privately
    believe (as in lying, hedging, or performing).

    In @cite{searle-1983}'s terms: commitment is the *public* direction-of-fit
    obligation created by performing a speech act. Asserting p creates a
    mind-to-world commitment (the speaker is responsible if p is false);
    promising p creates a world-to-mind commitment (the speaker is
    responsible if p is unfulfilled). -/
structure CommitmentSlate (W : Type*) where
  /-- The propositions the agent is publicly committed to -/
  commitments : List (BProp W)

namespace CommitmentSlate

variable {W : Type*}

/-- The empty commitment slate: no public commitments. -/
def empty : CommitmentSlate W := ⟨[]⟩

/-- Add a commitment to the slate. -/
def add (s : CommitmentSlate W) (p : BProp W) : CommitmentSlate W :=
  ⟨p :: s.commitments⟩

/-- Retract a commitment (remove first occurrence).

    Not all theories support retraction. Stalnaker's CG model has no
    retraction mechanism; Krifka and Brandom do. -/
def retract (s : CommitmentSlate W) (p : BProp W) [BEq (BProp W)] : CommitmentSlate W :=
  ⟨s.commitments.erase p⟩

/-- Convert commitments to a context set: the worlds compatible with
    all committed propositions. -/
def toContextSet (s : CommitmentSlate W) : BProp W :=
  λ w => s.commitments.all (λ p => p w)

/-- Check if the slate entails a proposition (holds at all compatible worlds). -/
def entails (s : CommitmentSlate W) (p : BProp W) (worlds : List W) : Bool :=
  worlds.all λ w => !s.commitments.all (λ q => q w) || p w

/-- Empty slate is trivial: all worlds are compatible. -/
theorem empty_trivial (w : W) : (empty : CommitmentSlate W).toContextSet w = true := by
  simp only [empty, toContextSet, List.all_nil]

/-- Adding a commitment restricts the context set. -/
theorem add_restricts (s : CommitmentSlate W) (p : BProp W) (w : W) :
    (s.add p).toContextSet w → s.toContextSet w := by
  simp only [add, toContextSet, List.all_cons, Bool.and_eq_true]
  exact And.right

/-- Adding a commitment entails the added proposition. -/
theorem add_entails (s : CommitmentSlate W) (p : BProp W) (w : W) :
    (s.add p).toContextSet w → p w = true := by
  simp only [add, toContextSet, List.all_cons, Bool.and_eq_true]
  exact And.left

end CommitmentSlate

-- ════════════════════════════════════════════════════════════════
-- § 2. Source-Marked Commitments (@cite{gunlogson-2001})
-- ════════════════════════════════════════════════════════════════

/-- The source of a discourse commitment.

    @cite{gunlogson-2001}: commitments are marked by their epistemic source.
    The source determines challengeability: self-generated commitments
    can be challenged by the addressee; other-generated commitments
    can be challenged by the speaker. -/
inductive CommitmentSource where
  /-- Commitment generated from agent's own evidence/beliefs -/
  | selfGenerated
  /-- Commitment attributed to another participant -/
  | otherGenerated
  deriving DecidableEq, Repr, Inhabited

/-- A commitment tagged with its source. -/
structure TaggedCommitment (W : Type*) where
  /-- The propositional content -/
  content : BProp W
  /-- How the commitment was generated -/
  source : CommitmentSource

/-- A source-tagged commitment slate. -/
structure TaggedSlate (W : Type*) where
  /-- The tagged commitments -/
  commitments : List (TaggedCommitment W)

namespace TaggedSlate

variable {W : Type*}

/-- The empty tagged slate. -/
def empty : TaggedSlate W := ⟨[]⟩

/-- Add a tagged commitment. -/
def add (s : TaggedSlate W) (p : BProp W) (src : CommitmentSource) : TaggedSlate W :=
  ⟨⟨p, src⟩ :: s.commitments⟩

/-- Get all self-generated commitments. -/
def selfGenerated (s : TaggedSlate W) : List (BProp W) :=
  s.commitments.filter (·.source == .selfGenerated) |>.map (·.content)

/-- Get all other-generated commitments. -/
def otherGenerated (s : TaggedSlate W) : List (BProp W) :=
  s.commitments.filter (·.source == .otherGenerated) |>.map (·.content)

/-- Convert to a plain (untagged) commitment slate. -/
def toSlate (s : TaggedSlate W) : CommitmentSlate W :=
  ⟨s.commitments.map (·.content)⟩

/-- Convert to context set (ignoring source tags). -/
def toContextSet (s : TaggedSlate W) : BProp W :=
  s.toSlate.toContextSet

end TaggedSlate

-- ════════════════════════════════════════════════════════════════
-- § 3. Contextual Evidence (@cite{bring-gunlogson-2000})
-- ════════════════════════════════════════════════════════════════

/-- Contextual evidence bias.

    Expectation about p induced by evidence available in the current
    discourse situation (@cite{bring-gunlogson-2000}). Used as:
    - A felicity condition on rising declaratives
    - A bias dimension for polar questions -/
inductive ContextualEvidence where
  /-- Current context provides evidence for p. -/
  | forP
  /-- No contextual evidence either way. -/
  | neutral
  /-- Current context provides evidence against p. -/
  | againstP
  deriving DecidableEq, Repr

end Commitment

-- ════════════════════════════════════════════════════════════════
-- § 4. HasContextSet Instance
-- ════════════════════════════════════════════════════════════════

open Core.CommonGround in
/-- A commitment slate projects to a context set: the worlds compatible
    with all committed propositions. -/
instance {W : Type*} : HasContextSet (Commitment.CommitmentSlate W) W where
  toContextSet s := λ w => s.toContextSet w

end Core.Discourse
