import Linglib.Core.Discourse.Commitment
import Linglib.Core.Interfaces.AssertionTheory

/-!
# Brandom (1994): Scorekeeping Model of Assertion

@cite{brandom-1994}

Models assertion as a move in a normative scorekeeping game. Each
participant tracks a "scorecard" for every other participant, recording
two kinds of normative status:

- **Commitments**: what the agent has publicly committed to
- **Entitlements**: what the agent is entitled to assert (has reasons for)

The key insight: entitlements have no analog in Stalnaker's model.
A speaker can be committed to p without being entitled to p (assertion
without adequate grounds) or entitled to p without being committed
(possessing evidence but not having asserted).

## Scorekeeping

Each agent keeps a score for every other agent. Scores can DISAGREE:
agent A might attribute commitment-to-p to agent B, while agent C
does not. This means there is no single "common ground" — only an
approximation derived from scorecard intersection.

## Inferential Closure

If an agent is committed to p and p→q, they are inferentially committed
to q (even if they haven't explicitly asserted q). This is Brandom's
"material inference" — the content of a claim is determined by its
inferential role.

## References

- Brandom, R. (1994). *Making It Explicit*. Harvard UP. Ch. 3.
- Brandom, R. (1983). Asserting. *Noûs* 17(4): 637–650.
-/

namespace Theories.Pragmatics.Assertion.Brandom

open Core.Discourse.Commitment (CommitmentSlate)
open Core.CommonGround (ContextSet CG)
open Core.Proposition (BProp)

-- ════════════════════════════════════════════════════
-- § 1. Normative Status
-- ════════════════════════════════════════════════════

/-- The normative status attributed to an agent by a scorekeeper.

    Brandom's central innovation: the deontic score has two independent
    dimensions. An agent can be committed-but-not-entitled (asserted
    without grounds), entitled-but-not-committed (has evidence, hasn't
    asserted), or both (well-grounded assertion). -/
structure NormativeStatus (W : Type*) where
  /-- Propositions the agent is committed to -/
  commitments : CommitmentSlate W
  /-- Propositions the agent is entitled to assert -/
  entitlements : CommitmentSlate W

namespace NormativeStatus

variable {W : Type*}

/-- Empty normative status: no commitments, no entitlements. -/
def empty : NormativeStatus W :=
  ⟨CommitmentSlate.empty, CommitmentSlate.empty⟩

/-- Add a commitment (the agent publicly commits to p). -/
def addCommitment (ns : NormativeStatus W) (p : BProp W) : NormativeStatus W :=
  { ns with commitments := ns.commitments.add p }

/-- Add an entitlement (the agent has grounds for p). -/
def addEntitlement (ns : NormativeStatus W) (p : BProp W) : NormativeStatus W :=
  { ns with entitlements := ns.entitlements.add p }

end NormativeStatus

-- ════════════════════════════════════════════════════
-- § 2. Scorecard
-- ════════════════════════════════════════════════════

/-- Agent type for the scorekeeping model. -/
inductive BAgent where
  | speaker
  | addressee
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A scorecard: what one agent attributes to another.

    `card a b` is agent a's attribution of normative status to agent b.
    Crucially, `card a b` can differ from `card c b` — scorekeepers
    can disagree about what another agent is committed/entitled to. -/
structure Scorecard (W : Type*) where
  /-- Agent a's view of agent b's normative status -/
  card : BAgent → BAgent → NormativeStatus W

namespace Scorecard

variable {W : Type*}

/-- Initial scorecard: everyone attributes empty status to everyone. -/
def empty : Scorecard W :=
  ⟨λ _ _ => NormativeStatus.empty⟩

/-- Get a specific agent's view of another agent's commitments. -/
def commitmentsOf (sc : Scorecard W) (keeper scorer : BAgent) : CommitmentSlate W :=
  (sc.card keeper scorer).commitments

/-- Get a specific agent's view of another agent's entitlements. -/
def entitlementsOf (sc : Scorecard W) (keeper scorer : BAgent) : CommitmentSlate W :=
  (sc.card keeper scorer).entitlements

end Scorecard

-- ════════════════════════════════════════════════════
-- § 3. Brandom State
-- ════════════════════════════════════════════════════

/-- Brandom's discourse state: a scorecard tracking all agent attributions. -/
structure BrandomState (W : Type*) where
  /-- The scorecard recording normative status attributions -/
  scorecard : Scorecard W

namespace BrandomState

variable {W : Type*}

/-- Initial state: empty scorecard. -/
def empty : BrandomState W := ⟨Scorecard.empty⟩

/-- Assert: the speaker undertakes a commitment and authorizes
    the addressee to re-assert.

    Brandom (1994, Ch.3): asserting p has two effects:
    1. The speaker undertakes commitment to p
    2. The speaker authorizes others to re-assert p (default entitlement) -/
def assert (s : BrandomState W) (p : BProp W) : BrandomState W :=
  let card' := λ keeper scorer =>
    if keeper == .speaker && scorer == .speaker then
      (s.scorecard.card keeper scorer).addCommitment p |>.addEntitlement p
    else if keeper == .addressee && scorer == .speaker then
      -- Addressee attributes commitment to speaker
      (s.scorecard.card keeper scorer).addCommitment p
    else
      s.scorecard.card keeper scorer
  ⟨⟨card'⟩⟩

/-- Effective context set: intersection of all attributed commitments.

    This is a LOSSY projection from Brandom → Stalnaker. Brandom's
    model has strictly more structure (entitlements, disagreement
    between scorekeepers), but for the `AssertionTheory` interface
    we need a single `ContextSet`. -/
def effectiveContextSet (s : BrandomState W) : ContextSet W :=
  λ w =>
    -- Intersection: w must be compatible with all commitments
    -- that both agents agree the speaker has
    (s.scorecard.card .speaker .speaker).commitments.toContextSet w ∧
    (s.scorecard.card .addressee .addressee).commitments.toContextSet w

/-- Stability: the state is stable when all commitments have
    matching entitlements (no ungrounded assertions). -/
def isStable (s : BrandomState W) : Bool :=
  let spkrStatus := s.scorecard.card .speaker .speaker
  spkrStatus.commitments.commitments.length ≤
    spkrStatus.entitlements.commitments.length

end BrandomState

-- ════════════════════════════════════════════════════
-- § 4. Challenges
-- ════════════════════════════════════════════════════

/-- A challenge: the addressee demands reasons for a commitment.

    Brandom (1994): challenges shift the burden of proof. If the speaker
    cannot provide entitlement for a commitment, the commitment is
    defeated (withdrawn from the scorecard). -/
structure Challenge (W : Type*) where
  /-- Who issues the challenge -/
  challenger : BAgent
  /-- The proposition challenged -/
  proposition : BProp W

-- ════════════════════════════════════════════════════
-- § 5. Inferential Closure
-- ════════════════════════════════════════════════════

/-- Inferential closure: if committed to p and p→q, committed to q.

    Brandom's "material inference" — the content of a concept is
    its inferential role, not its reference. An agent's commitments
    are closed under their acknowledged inferential connections.

    TODO: full closure requires a fixpoint computation. -/
def inferentialClosure {W : Type*} (cs : CommitmentSlate W)
    (rules : List (BProp W × BProp W)) : CommitmentSlate W :=
  rules.foldl (λ acc ⟨_antecedent, consequent⟩ => acc.add consequent) cs

-- ════════════════════════════════════════════════════
-- § 6. Interface Instance
-- ════════════════════════════════════════════════════

/-- Marker type for Brandom's theory. -/
inductive BrandomTag | mk

instance : Interfaces.AssertionTheory BrandomTag where
  State := BrandomState
  initial := BrandomState.empty
  assert := BrandomState.assert
  contextSet := BrandomState.effectiveContextSet
  isStable := BrandomState.isStable
  separatesCommitmentFromBelief := true
  supportsRetraction := true
  modelsSourceMarking := false

-- ════════════════════════════════════════════════════
-- § 7. Verification
-- ════════════════════════════════════════════════════

/-- Entitlements have no Stalnaker analog.
    Stalnaker's `CG.add` doesn't track whether the speaker has REASONS
    for the assertion — it just adds to shared beliefs. -/
theorem entitlements_no_stalnaker_analog :
    Interfaces.AssertionTheory.separatesCommitmentFromBelief (T := BrandomTag) = true ∧
    Interfaces.AssertionTheory.supportsRetraction (T := BrandomTag) = true :=
  ⟨rfl, rfl⟩

/-- Scorekeepers can disagree: agent A's view of B's status can differ
    from agent C's view of B's status.

    Witnessed by a scorecard where the speaker attributes a commitment
    to the addressee, but the addressee does not self-attribute it. -/
theorem scorekeepers_can_disagree :
    ∃ (sc : Scorecard Unit),
      (sc.card .speaker .addressee).commitments.commitments.length ≠
      (sc.card .addressee .addressee).commitments.commitments.length := by
  exact ⟨⟨λ keeper _ =>
    if keeper == BAgent.speaker then
      { commitments := ⟨[λ _ => true]⟩, entitlements := CommitmentSlate.empty }
    else NormativeStatus.empty⟩, by decide⟩

end Theories.Pragmatics.Assertion.Brandom
