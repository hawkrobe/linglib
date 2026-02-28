import Linglib.Core.Semantics.Proposition
import Linglib.Core.Semantics.CommonGround

/-!
# Discourse Commitments

Shared types for modeling public commitments in discourse, used by
multiple theories of assertion (Krifka, Brandom, Gunlogson).

A `CommitmentSlate` is an agent's public discourse commitments — the
propositions they have publicly committed to (which may differ from
their private beliefs). This separation is crucial for:

- **Krifka (2015)**: commitment ≠ belief; lying = commitment without belief
- **Brandom (1994)**: commitments are normative statuses tracked by scorekeepers
- **Gunlogson (2001)**: source-marking distinguishes self-generated from
  other-generated commitments

## References

- Krifka, M. (2015). Bias in Commitment Space Semantics. *L&P* 38.
- Brandom, R. (1994). *Making It Explicit*. Harvard UP.
- Gunlogson, C. (2001). *True to Form*. PhD dissertation, UC Santa Cruz.
-/

namespace Core.Discourse.Commitment

open Core.Proposition (BProp)
open Core.CommonGround (ContextSet CG)

-- ════════════════════════════════════════════════════
-- § 1. Commitment Slates
-- ════════════════════════════════════════════════════

/-- An agent's public discourse commitments: a list of propositions
    the agent has publicly committed to.

    Following Krifka (2015): the commitment slate tracks what an agent
    is publicly committed to, which may diverge from what they privately
    believe (as in lying, hedging, or performing). -/
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
def toContextSet (s : CommitmentSlate W) : ContextSet W :=
  λ w => s.commitments.all (λ p => p w)

/-- Check if the slate entails a proposition (holds at all compatible worlds). -/
def entails (s : CommitmentSlate W) (p : BProp W) (worlds : List W) : Bool :=
  worlds.all λ w => !s.commitments.all (λ q => q w) || p w

/-- Empty slate is trivial: all worlds are compatible. -/
theorem empty_trivial : (empty : CommitmentSlate W).toContextSet = ContextSet.trivial := by
  funext w
  simp only [empty, toContextSet, ContextSet.trivial, List.all_nil]

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

-- ════════════════════════════════════════════════════
-- § 2. Source-Marked Commitments (Gunlogson 2001)
-- ════════════════════════════════════════════════════

/-- The source of a discourse commitment.

    Gunlogson (2001): commitments are marked by their epistemic source.
    - `.selfGenerated`: the agent generated the commitment from their own evidence
    - `.otherGenerated`: the commitment originates from another participant

    The source determines challengeability: self-generated commitments
    can be challenged by the addressee; other-generated commitments
    can be challenged by the speaker. -/
inductive CommitmentSource where
  /-- Commitment generated from agent's own evidence/beliefs -/
  | selfGenerated
  /-- Commitment attributed to another participant -/
  | otherGenerated
  deriving DecidableEq, Repr, BEq, Inhabited

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
def toContextSet (s : TaggedSlate W) : ContextSet W :=
  s.toSlate.toContextSet

end TaggedSlate

-- ════════════════════════════════════════════════════
-- § 3. Contextual Evidence (Büring & Gunlogson 2000)
-- ════════════════════════════════════════════════════

/-- Contextual evidence bias (Büring & Gunlogson 2000).

    Expectation about p induced by evidence available in the current
    discourse situation. Used as:
    - A felicity condition on rising declaratives (Gunlogson 2001)
    - A bias dimension for polar questions (Romero 2024)

    This type is shared between assertion theory and question bias
    theory because the same notion of contextual evidence governs
    both: evidence for p licenses rising declaratives about p and
    positive polar questions about p. -/
inductive ContextualEvidence where
  /-- Current context provides evidence for p. -/
  | forP
  /-- No contextual evidence either way. -/
  | neutral
  /-- Current context provides evidence against p. -/
  | againstP
  deriving DecidableEq, BEq, Repr

end Core.Discourse.Commitment
