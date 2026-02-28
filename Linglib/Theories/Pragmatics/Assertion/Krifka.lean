import Linglib.Core.Discourse.Commitment
import Linglib.Core.Interfaces.AssertionTheory
import Linglib.Core.Discourse.DiscourseRole

/-!
# Krifka (2015): Commitment Space Semantics

@cite{krifka-2015}

Models assertion via layered assertive clauses (TP < JP < ComP < ActP)
and per-agent commitment spaces. The key innovation over Stalnaker:
commitment and belief are separate, enabling the theory to handle
lying, hedging, and graded commitment.

## Clause Layers

Krifka proposes that assertive clauses have four syntactic layers,
each contributing a distinct semantic dimension:

| Layer | Contribution | Example Modifier |
|-------|-------------|-----------------|
| TP | Propositional content | tense, aspect |
| JP (Judge Phrase) | Epistemic status | "I think", "maybe" |
| ComP (Commitment Phrase) | Commitment strength | "I swear", "perhaps" |
| ActP (Act Phrase) | Speech act type | declarative, imperative |

JP and ComP are independent: "I think I swear p" vs "I swear I think p"
both involve TP content p, but with different epistemic/commitment profiles.

## Commitment Spaces

The common ground emerges from the intersection of all participants'
commitment states, following Krifka's `+ c p` operator:

    CG = ⋂{cs(a) | a ∈ participants}

## References

- Krifka, M. (2015). Bias in Commitment Space Semantics: Declarative
  questions, negated questions, and question tags. *L&P* 38: 115–143.
-/

namespace Theories.Pragmatics.Assertion.Krifka

open Core.Discourse.Commitment (CommitmentSlate)
open Core.CommonGround (ContextSet CG)
open Core.Proposition (BProp)
open Core.Discourse (IllocutionaryMood)

-- ════════════════════════════════════════════════════
-- § 1. Clause Layers
-- ════════════════════════════════════════════════════

/-- The four syntactic layers of an assertive clause.

    Ordered from innermost (TP, propositional content) to outermost
    (ActP, speech act force). Each layer contributes a distinct semantic
    dimension that can be independently modified. -/
inductive ClauseLayer where
  /-- Tense Phrase: propositional content -/
  | TP
  /-- Judge Phrase: epistemic status (certainty/uncertainty) -/
  | JP
  /-- Commitment Phrase: commitment strength -/
  | ComP
  /-- Act Phrase: speech act type -/
  | ActP
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Rank ordering of clause layers (innermost = 0). -/
def ClauseLayer.rank : ClauseLayer → Nat
  | .TP => 0
  | .JP => 1
  | .ComP => 2
  | .ActP => 3

/-- TP is the innermost layer. -/
theorem tp_innermost : ∀ l : ClauseLayer, ClauseLayer.TP.rank ≤ l.rank := by
  intro l; cases l <;> simp [ClauseLayer.rank]

-- ════════════════════════════════════════════════════
-- § 2. Commitment Strength
-- ════════════════════════════════════════════════════

/-- Graded commitment strength, controlled by ComP modifiers.

    - `weak`: hedged ("I think p", "maybe p")
    - `standard`: default declarative assertion
    - `strong`: oath formulae ("I swear p", "I promise p") -/
inductive CommitmentStrength where
  | weak
  | standard
  | strong
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Numerical ordering of commitment strengths. -/
def CommitmentStrength.rank : CommitmentStrength → Nat
  | .weak => 0
  | .standard => 1
  | .strong => 2

/-- Standard is the default. -/
theorem standard_is_default : CommitmentStrength.standard.rank = 1 := rfl

/-- Strong > standard > weak. -/
theorem strength_ordering :
    CommitmentStrength.weak.rank < CommitmentStrength.standard.rank ∧
    CommitmentStrength.standard.rank < CommitmentStrength.strong.rank :=
  ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 3. Layered Assertions
-- ════════════════════════════════════════════════════

/-- A fully layered assertion, decomposed into the four clause layers.

    Each layer is independent: the epistemic status (JP) can vary without
    affecting the commitment strength (ComP), and vice versa. The actType
    uses `IllocutionaryMood` from `Core/Discourse/DiscourseRole.lean`. -/
structure LayeredAssertion (W : Type*) where
  /-- TP: the propositional content -/
  content : BProp W
  /-- JP: the speaker's epistemic status toward the content -/
  epistemicStatus : CommitmentStrength := .standard
  /-- ComP: the strength of the speaker's public commitment -/
  commitmentStrength : CommitmentStrength := .standard
  /-- ActP: the type of speech act performed -/
  actType : IllocutionaryMood := .declarative

-- ════════════════════════════════════════════════════
-- § 4. Krifka State: Per-Agent Commitment Spaces
-- ════════════════════════════════════════════════════

/-- Agent type for two-participant discourse. -/
inductive KAgent where
  | speaker
  | addressee
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Krifka's discourse state: per-agent commitment slates + shared CG.

    The CG is derived as the intersection of all participants' commitments
    when they agree, but we track it explicitly for the interface. -/
structure KrifkaState (W : Type*) where
  /-- Speaker's commitment slate -/
  speakerCS : CommitmentSlate W
  /-- Addressee's commitment slate -/
  addresseeCS : CommitmentSlate W
  /-- The derived common ground (intersection of commitments) -/
  cg : CG W

namespace KrifkaState

variable {W : Type*}

/-- Initial state: no commitments, empty CG. -/
def empty : KrifkaState W :=
  ⟨CommitmentSlate.empty, CommitmentSlate.empty, CG.empty⟩

/-- Krifka's commitment operator: `+ c p`.
    The speaker commits to p by adding it to their commitment slate. -/
def commitOp (s : KrifkaState W) (p : BProp W) : KrifkaState W :=
  { s with speakerCS := s.speakerCS.add p }

/-- Accept: when the addressee also commits, p enters the CG. -/
def accept (s : KrifkaState W) (p : BProp W) : KrifkaState W :=
  { s with
    addresseeCS := s.addresseeCS.add p
    cg := s.cg.add p }

/-- Assert = commit + push to CG for acceptance.
    For the interface, we model assertion as commitment only (the
    acceptance step is separate). -/
def assert (s : KrifkaState W) (p : BProp W) : KrifkaState W :=
  s.commitOp p

/-- Retract: remove a commitment from the speaker's slate. -/
def retract (s : KrifkaState W) (p : BProp W) [BEq (BProp W)] : KrifkaState W :=
  { s with speakerCS := s.speakerCS.retract p }

/-- Context set: from the common ground. -/
def contextSet (s : KrifkaState W) : ContextSet W :=
  s.cg.contextSet

/-- Stability: the state is stable when both participants' commitments
    are subsets of the CG (no unresolved commitments). -/
def isStable (s : KrifkaState W) : Bool :=
  s.speakerCS.commitments.length ≤ s.cg.propositions.length &&
  s.addresseeCS.commitments.length ≤ s.cg.propositions.length

end KrifkaState

-- ════════════════════════════════════════════════════
-- § 5. Interface Instance
-- ════════════════════════════════════════════════════

/-- Marker type for Krifka's theory. -/
inductive KrifkaTag | mk

instance : Interfaces.AssertionTheory KrifkaTag where
  State := KrifkaState
  initial := KrifkaState.empty
  assert := KrifkaState.assert
  contextSet := KrifkaState.contextSet
  isStable := KrifkaState.isStable
  separatesCommitmentFromBelief := true
  supportsRetraction := true
  modelsSourceMarking := false

-- ════════════════════════════════════════════════════
-- § 6. Layer Independence
-- ════════════════════════════════════════════════════

/-- ComP preserves TP content: changing commitment strength does not
    change the propositional content. -/
theorem comp_preserves_content {W : Type*}
    (la : LayeredAssertion W) (str : CommitmentStrength) :
    { la with commitmentStrength := str }.content = la.content := rfl

/-- JP and ComP are independent: changing one does not affect the other. -/
theorem jp_comp_independent {W : Type*}
    (la : LayeredAssertion W) (ep : CommitmentStrength) (cs : CommitmentStrength) :
    ({ la with epistemicStatus := ep, commitmentStrength := cs }).content = la.content ∧
    ({ la with epistemicStatus := ep }).commitmentStrength = la.commitmentStrength ∧
    ({ la with commitmentStrength := cs }).epistemicStatus = la.epistemicStatus :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 7. Bridge to IllocutionaryMood
-- ════════════════════════════════════════════════════

/-- Krifka's ActP layer directly uses `IllocutionaryMood`, grounding
    the clause-type distinction in the speech act classification. -/
theorem actp_declarative_default {W : Type*} (p : BProp W) :
    ({ content := p : LayeredAssertion W }).actType = .declarative := rfl

/-- Krifka separates commitment from belief. -/
theorem separates_commitment :
    Interfaces.AssertionTheory.separatesCommitmentFromBelief (T := KrifkaTag) = true := rfl

/-- Krifka supports retraction. -/
theorem supports_retraction :
    Interfaces.AssertionTheory.supportsRetraction (T := KrifkaTag) = true := rfl

end Theories.Pragmatics.Assertion.Krifka
