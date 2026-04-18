import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment

/-!
# Krifka: Commitment Space Semantics and Layered Assertive Clauses

@cite{krifka-2015} @cite{krifka-2020}

Combines two strands of Krifka's work:

1. **Commitment spaces**: the discourse state is a tree —
   the root (√C) is the current CG, and continuations are proposed
   future states from questions. Assertion narrows every state (`C + S⊢φ`);
   questions preserve the root and add branches (`C + ?φ`).
   Per-agent commitment slates track individual public commitments,
   enabling the commitment/belief separation (lying, hedging).

2. **Layered assertive clauses**: four syntactic layers
   each contributing a distinct semantic dimension:

| Layer | Contribution | Example Modifier |
|-------|-------------|-----------------|
| TP | Propositional content | tense, aspect |
| JP (Judge Phrase) | Epistemic judgment | "I think", evidentials |
| ComP (Commitment Phrase) | Commitment strength | "I swear", "perhaps" |
| ActP (Act Phrase) | Speech act type | declarative, imperative |

JP and ComP are independent: "I think I swear p" vs "I swear I think p"
both involve TP content p, but with different epistemic/commitment profiles.

## Commitment Space Tree

The discourse state is a `CommitmentSpace` tree (§4):

    CommitmentSpace = { root : List Prop, continuations : List (List Prop) }

- **Assert** `C + S⊢φ`: adds φ to root AND all continuations
- **Question** `C + ?φ`: preserves root, adds continuation (root ∩ φ),
  narrows existing continuations by φ
- **Accept**: promotes first continuation to root
- **Reject**: prunes first continuation

-/

namespace Pragmatics.Assertion.Krifka

open Core.Discourse.Commitment (CommitmentSlate)
open Core.CommonGround (ContextSet)
open Core.Proposition (BProp)
open Core.Mood (IllocutionaryMood)

-- ════════════════════════════════════════════════════
-- § 1. Clause Layers
-- ════════════════════════════════════════════════════

/-- The four syntactic layers of an assertive clause.

    Ordered from innermost (TP, propositional content) to outermost
    (ActP, speech act force). Each layer contributes a distinct semantic
    dimension that can be independently modified.

    TODO: @cite{krifka-2015} §4 also posits PolP (Polarity Phrase) between
    ComP and TP, hosting verum (⊢) / falsum (⊣). High negation at ComP
    (¬⊢φ = non-commitment to φ) vs TP negation (⊢¬φ = commitment to ¬φ)
    explains the bias asymmetry of negative questions: "Isn't it raining?"
    is biased toward rain because negation scopes over ⊢, not over φ. -/
inductive ClauseLayer where
  /-- Tense Phrase: propositional content -/
  | TP
  /-- Judge Phrase: epistemic status (certainty/uncertainty) -/
  | JP
  /-- Commitment Phrase: commitment strength -/
  | ComP
  /-- Act Phrase: speech act type -/
  | ActP
  deriving DecidableEq, Repr, Inhabited

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
  deriving DecidableEq, Repr, Inhabited

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
    uses `IllocutionaryMood` from `Core/Discourse/IllocutionaryForce.lean`. -/
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
-- § 4. Commitment Space: Tree Structure (@cite{krifka-2015}, §2)
-- ════════════════════════════════════════════════════

/-- Agent type for two-participant discourse. -/
inductive KAgent where
  | speaker
  | addressee
  deriving DecidableEq, Repr, Inhabited

/-- Bridge `KAgent` to the framework-agnostic `DiscourseRole`.
    Both encode the same two-participant distinction. -/
def KAgent.toDiscourseRole : KAgent → Core.Discourse.DiscourseRole
  | .speaker   => .speaker
  | .addressee => .addressee

/-- A commitment space (@cite{krifka-2015}, Definition 3, p.329).

    A set of commitment states organized as root + continuations:

    - **root** (√C): the current commitment state — what is actually
      in the common ground. All worlds compatible with the root
      propositions are "live".
    - **continuations**: proposed future states, each extending the root.
      Added by questions, resolved by acceptance or rejection.

    Krifka's key operations:

    - Assert `C + S⊢φ` = {s ∩ ⟦φ⟧ : s ∈ C}: narrow every state by φ
    - Question `C + ?φ` = {√C} ∪ (C + S₂⊢φ): preserve root, propose φ
    - Accept: take a continuation as the new root
    - Reject: prune a continuation

    The tree structure captures the assertion/question asymmetry:
    assertions modify the root (the CG changes), while questions only
    add continuations (the CG is preserved until acceptance). -/
structure CommitmentSpace (W : Type*) where
  /-- Root commitment state √C: propositions currently in the CG -/
  root : List (BProp W)
  /-- Proposed future states. Questions add these; acceptance promotes
      one to root. Each continuation is a list of propositions that
      extends (narrows) the root. -/
  continuations : List (List (BProp W))

namespace CommitmentSpace

variable {W : Type*}

/-- The empty commitment space: no commitments, no continuations. -/
def empty : CommitmentSpace W := ⟨[], []⟩

/-- Assert φ: narrow every state by φ (@cite{krifka-2015}, (9), p.329).

    `C + S⊢φ = {s ∩ ⟦φ⟧ : s ∈ C}`

    Adds φ to the root AND all continuations. Any accepted
    continuation will also entail φ. -/
def assert (cs : CommitmentSpace W) (φ : BProp W) : CommitmentSpace W :=
  { root := φ :: cs.root
    continuations := cs.continuations.map (φ :: ·) }

/-- Question: preserve root, propose φ (@cite{krifka-2015}, (14), p.332).

    `C + ?φ = {√C} ∪ (C + S₂⊢φ)`

    The root stays unchanged (CG preserved). A new continuation is
    added (root narrowed by φ), and existing continuations are also
    narrowed by φ. The addressee can accept (promote continuation to
    root) or reject (prune it). -/
def question (cs : CommitmentSpace W) (φ : BProp W) : CommitmentSpace W :=
  { root := cs.root
    continuations := (φ :: cs.root) :: cs.continuations.map (φ :: ·) }

/-- The space is settled: no open continuations.
    A settled space has no unresolved proposals. -/
def isSettled : CommitmentSpace W → Bool
  | ⟨_, []⟩ => true
  | ⟨_, _ :: _⟩ => false

/-- Accept the first continuation: it becomes the new root.
    The CG is updated to the accepted proposal's content. -/
def acceptFirst : CommitmentSpace W → CommitmentSpace W
  | ⟨_, c :: rest⟩ => ⟨c, rest⟩
  | cs => cs

/-- Reject the first continuation: prune it.
    The CG is unchanged; the proposal is discarded. -/
def rejectFirst : CommitmentSpace W → CommitmentSpace W
  | ⟨r, _ :: rest⟩ => ⟨r, rest⟩
  | cs => cs

/-- Context set from root: worlds compatible with all root propositions. -/
def toContextSet (cs : CommitmentSpace W) : ContextSet W :=
  λ w => cs.root.all (· w)

/-- Empty space is settled. -/
theorem empty_settled : (empty : CommitmentSpace W).isSettled = true := rfl

/-- Assertion preserves settledness. -/
theorem assert_preserves_settled (cs : CommitmentSpace W) (φ : BProp W)
    (h : cs.isSettled = true) :
    (cs.assert φ).isSettled = true := by
  cases cs with | mk r conts =>
  cases conts with
  | nil => rfl
  | cons _ _ => simp [isSettled] at h

/-- Question makes a settled space unsettled (adds a continuation). -/
theorem question_unsettles (cs : CommitmentSpace W) (φ : BProp W)
    (h : cs.isSettled = true) :
    (cs.question φ).isSettled = false := by
  cases cs with | mk r conts =>
  cases conts with
  | nil => rfl
  | cons _ _ => simp [isSettled] at h

/-- Accepting a simple question's sole continuation re-settles. -/
theorem accept_resettles_simple (cs : CommitmentSpace W) (φ : BProp W)
    (h : cs.isSettled = true) :
    (cs.question φ).acceptFirst.isSettled = true := by
  cases cs with | mk r conts =>
  cases conts with
  | nil => rfl
  | cons _ _ => simp [isSettled] at h

/-- Root after assertion contains the asserted proposition. -/
theorem assert_in_root (cs : CommitmentSpace W) (φ : BProp W) :
    φ ∈ (cs.assert φ).root := by simp [assert]

/-- Question preserves root commitments. -/
theorem question_preserves_root (cs : CommitmentSpace W) (φ : BProp W) :
    (cs.question φ).root = cs.root := rfl

end CommitmentSpace

/-- Krifka's discourse state: per-agent commitment slates + shared
    commitment space (tree).

    The commitment space tracks the shared discourse structure:
    what's in the CG (root) and what's been proposed (continuations).
    Per-agent slates track individual public commitments, enabling
    the commitment/belief separation central to Krifka's theory. -/
structure KrifkaState (W : Type*) where
  /-- Speaker's individual commitment slate -/
  speakerCS : CommitmentSlate W
  /-- Addressee's individual commitment slate -/
  addresseeCS : CommitmentSlate W
  /-- Shared commitment space (tree): CG + proposed updates -/
  space : CommitmentSpace W

namespace KrifkaState

variable {W : Type*}

/-- Initial state: no commitments, empty settled space. -/
def empty : KrifkaState W :=
  ⟨CommitmentSlate.empty, CommitmentSlate.empty, CommitmentSpace.empty⟩

/-- Krifka's commitment operator `+ S₁⊢p` (@cite{krifka-2015}, (9)):
    speaker commits to p, narrowing the entire space. -/
def commitOp (s : KrifkaState W) (p : BProp W) : KrifkaState W :=
  { s with
    speakerCS := s.speakerCS.add p
    space := s.space.assert p }

/-- Accept: addressee also commits to p (after speaker's assertion). -/
def accept (s : KrifkaState W) (p : BProp W) : KrifkaState W :=
  { s with addresseeCS := s.addresseeCS.add p }

/-- Assert = commit (@cite{krifka-2015}: assertion IS commitment).
    The space is narrowed immediately; the CG reflects the assertion. -/
def assert (s : KrifkaState W) (p : BProp W) : KrifkaState W :=
  s.commitOp p

/-- Question: speaker proposes φ as a continuation (@cite{krifka-2015}, (14)).
    The CG (root) is unchanged; a new continuation is added. -/
def question (s : KrifkaState W) (p : BProp W) : KrifkaState W :=
  { s with space := s.space.question p }

/-- Accept the first continuation: it becomes the new CG. -/
def acceptContinuation (s : KrifkaState W) : KrifkaState W :=
  { s with space := s.space.acceptFirst }

/-- Reject the first continuation: prune it. -/
def rejectContinuation (s : KrifkaState W) : KrifkaState W :=
  { s with space := s.space.rejectFirst }

/-- Retract: remove a commitment from the speaker's slate. -/
def retract (s : KrifkaState W) (p : BProp W) [BEq (BProp W)] : KrifkaState W :=
  { s with speakerCS := s.speakerCS.retract p }

/-- Context set: from the commitment space root (= CG). -/
def contextSet (s : KrifkaState W) : ContextSet W :=
  s.space.toContextSet

/-- Stability: the space is settled (no open proposals). -/
def isStable (s : KrifkaState W) : Bool :=
  s.space.isSettled

end KrifkaState

-- ════════════════════════════════════════════════════
-- § 5. Layer Independence
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
-- § 6. Bridge to IllocutionaryMood
-- ════════════════════════════════════════════════════

/-- Krifka's ActP layer directly uses `IllocutionaryMood`, grounding
    the clause-type distinction in the speech act classification. -/
theorem actp_declarative_default {W : Type*} (p : BProp W) :
    ({ content := p : LayeredAssertion W }).actType = .declarative := rfl

-- ════════════════════════════════════════════════════
-- § 7. Informative vs Performative Updates (@cite{krifka-2020}, §2)
-- ════════════════════════════════════════════════════

/-- Update type for assertions.

    Krifka distinguishes two fundamentally different ways an assertion
    can change the common ground:

    - **informative** (`·φ`): eliminates worlds incompatible with φ.
      `c + ·φ = {i | i ∈ c ∧ φ(i)}`
      Example: "The meeting is at 5" — reduces uncertainty.

    - **performative** (`•φ`): changes world indices so φ becomes true.
      `c + •φ = {i' | ∃ i ∈ c, i ⇒_φ i'}`
      Example: "I hereby name this ship the Queen Elizabeth" — makes
      φ true by the act of uttering it.

    This distinction is orthogonal to commitment strength (ComP) and
    epistemic status (JP). -/
inductive UpdateType where
  | informative   -- ·φ : eliminates worlds where φ is false
  | performative  -- •φ : changes worlds so φ becomes true
  deriving DecidableEq, Repr, Inhabited

/-- Informative update: restrict context set to worlds satisfying φ.
    @cite{krifka-2020}, (7): `c + ·φ = {i | i ∈ c ∧ φ(i)}` -/
def informativeUpdate {W : Type*} (cs : List W) (φ : BProp W) : List W :=
  cs.filter φ

/-- A fully specified assertion with update type. -/
structure TypedAssertion (W : Type*) extends LayeredAssertion W where
  /-- Whether the update is informative or performative -/
  updateType : UpdateType := .informative

/-- Default assertions are informative (the common case). -/
theorem default_assertion_informative {W : Type*} (p : BProp W) :
    ({ content := p : TypedAssertion W }).updateType = .informative := rfl

/-- Commitment Closure (@cite{krifka-2020}, (25)): assertion immediately
    narrows the commitment space. The root (CG) after asserting φ
    is the original root with φ prepended.

    In the tree model, this is definitional: `assert` adds φ to
    all nodes including the root. -/
theorem commitment_closure {W : Type*} (s : KrifkaState W) (p : BProp W) :
    (s.assert p).space.root = p :: s.space.root := rfl

/-- Questions don't change the CG: the root is preserved. -/
theorem question_preserves_cg {W : Type*} (s : KrifkaState W) (p : BProp W) :
    (s.question p).space.root = s.space.root := rfl

/-- Question then accept ≈ assert (on the root): accepting a question's
    sole continuation yields the same CG as a direct assertion.

    This connects the two modes of updating: direct assertion (speaker
    imposes) and question-then-accept (speaker proposes, addressee
    accepts). The roots match because both produce φ :: root₀. -/
theorem question_accept_eq_assert_root {W : Type*}
    (s : KrifkaState W) (p : BProp W) (h : s.space.isSettled = true) :
    (s.question p).acceptContinuation.space.root =
    (s.assert p).space.root := by
  cases s with | mk sCS aCS space =>
  cases space with | mk r conts =>
  cases conts with
  | nil => rfl
  | cons _ _ => simp [CommitmentSpace.isSettled] at h

-- ════════════════════════════════════════════════════
-- § 8. Actor vs Committer (@cite{krifka-2015}, §6)
-- ════════════════════════════════════════════════════

/-- The two discourse roles in a speech act.

    Every speech act has an **actor** (who performs the act) and a
    **committer** (who undertakes the commitment). These can diverge:

    - Assertion: actor = speaker, committer = speaker
    - Monopolar question: actor = speaker, committer = addressee
      (the speaker proposes that the addressee commit)

    This is the "one promising aspect" Krifka highlights in his
    conclusion: the framework naturally separates who acts from
    who commits, explaining why questions can be biased (the speaker
    chooses WHAT to propose) without being assertive (the addressee
    decides WHETHER to commit). -/
structure ActorCommitter where
  actor     : KAgent
  committer : KAgent
  deriving DecidableEq, Repr

/-- In assertions, speaker is both actor and committer. -/
def assertionRoles : ActorCommitter :=
  ⟨.speaker, .speaker⟩

/-- In monopolar questions, speaker acts but addressee commits.
    @cite{krifka-2015}, (16): `C +_{S₁} [? [⊢ p]]` proposes that S₂ commit to p. -/
def questionRoles : ActorCommitter :=
  ⟨.speaker, .addressee⟩

/-- Assertions and questions differ in who commits. -/
theorem actor_committer_diverge :
    assertionRoles.actor = questionRoles.actor ∧
    assertionRoles.committer ≠ questionRoles.committer := by decide

-- ════════════════════════════════════════════════════
-- § 9. Speech Act Composition (@cite{krifka-2015}, §3–5)
-- ════════════════════════════════════════════════════

/-- A speech act in Krifka's framework: ActP content with its
    discourse function (assertion vs question).

    @cite{krifka-2015} clause structure: ActP > ComP > TP (three layers).
    The 2020 paper refines this to ActP > ComP > JP > TP. -/
structure SpeechAct (W : Type*) where
  /-- Propositional content (TP layer) -/
  content : BProp W
  /-- Speech act type: assertion (.) or question (?) -/
  actType : IllocutionaryMood := .declarative
  /-- Actor/committer assignment -/
  roles : ActorCommitter := assertionRoles

/-- Monopolar question: proposes a single
    continuation where the addressee commits to φ.

    `C +_{S₁} [? [⊢ φ]]` = {√C} ∪ (C + S₂⊢φ)

    The root is preserved ({√C}) alongside the proposed continuation
    (C + S₂⊢φ). The addressee can accept (take the continuation) or
    reject (stay at root). This is what makes it a QUESTION rather than
    an assertion — the commitment is proposed, not imposed.

    Monopolar questions are inherently biased toward the proposed
    continuation. -/
def monopolarQuestion {W : Type*} (φ : BProp W) : SpeechAct W :=
  { content := φ, actType := .interrogative, roles := questionRoles }

/-- Complex speech act: conjunction or disjunction of atomic acts.

    @cite{krifka-2015}, §5: question tags involve composition of speech acts.
    The difference between matching and reverse tags is conjunction vs
    disjunction:
    - **conj**: both acts performed sequentially (matching tag)
    - **disj**: addressee chooses one continuation (reverse tag) -/
inductive ComplexSpeechAct (W : Type*) where
  /-- A single speech act. -/
  | atom : SpeechAct W → ComplexSpeechAct W
  /-- Conjunction: perform both acts sequentially.
      "It's raining, isn't it?" = ASSERT(rain) ∧ ASK(rain). -/
  | conj : SpeechAct W → SpeechAct W → ComplexSpeechAct W
  /-- Disjunction: offer alternative continuations.
      "It's raining, or isn't it?" = ASSERT(rain) ∨ ASK(¬rain). -/
  | disj : SpeechAct W → SpeechAct W → ComplexSpeechAct W

/-- Extract the component speech acts from a complex speech act. -/
def ComplexSpeechAct.components {W : Type*} : ComplexSpeechAct W → List (SpeechAct W)
  | .atom a => [a]
  | .conj a b => [a, b]
  | .disj a b => [a, b]

/-- A matching question tag: conjunction of assertion + monopolar question
    with same content.

    "It's raining, isn't it?" = speaker asserts rain AND asks addressee
    to confirm. The speaker has already committed, so the question is
    biased toward the asserted content. -/
def matchingTag {W : Type*} (φ : BProp W) : ComplexSpeechAct W :=
  .conj
    { content := φ, actType := .declarative, roles := assertionRoles }
    (monopolarQuestion φ)

/-- A reverse question tag: disjunction of assertion + monopolar question
    with opposite content.

    "It's raining, or isn't it?" = speaker offers two continuations.
    The addressee picks one. -/
def reverseTag {W : Type*} (φ negφ : BProp W) : ComplexSpeechAct W :=
  .disj
    { content := φ, actType := .declarative, roles := assertionRoles }
    (monopolarQuestion negφ)

/-- In a matching tag, the assertion and question share content. -/
theorem matching_tag_shared_content {W : Type*} (φ : BProp W) :
    (matchingTag φ).components.map SpeechAct.content = [φ, φ] := rfl

/-- In a matching tag, the speaker is actor in both acts. -/
theorem matching_tag_same_actor {W : Type*} (φ : BProp W) :
    (matchingTag φ).components.map (·.roles.actor) = [.speaker, .speaker] := rfl

/-- In a matching tag, the committers differ: speaker for assertion,
    addressee for question. -/
theorem matching_tag_committers_diverge {W : Type*} (φ : BProp W) :
    (matchingTag φ).components.map (·.roles.committer) = [.speaker, .addressee] := rfl

/-- Matching tags are conjunctions, reverse tags are disjunctions. -/
theorem tag_type_distinction {W : Type*} (φ negφ : BProp W) :
    (∃ a b, matchingTag φ = .conj a b) ∧
    (∃ a b, reverseTag φ negφ = .disj a b) :=
  ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

-- ════════════════════════════════════════════════════
-- § 10. HasContextSet Instances
-- ════════════════════════════════════════════════════

open Core.CommonGround in
/-- A commitment space projects to a context set via its root. -/
instance {W : Type*} : HasContextSet (CommitmentSpace W) W where
  toContextSet := CommitmentSpace.toContextSet

open Core.CommonGround in
/-- A Krifka state projects to a context set via the commitment space root. -/
instance {W : Type*} : HasContextSet (KrifkaState W) W where
  toContextSet := KrifkaState.contextSet

open Core.CommonGround in
/-- KrifkaState context set agrees with CommitmentSpace context set. -/
theorem krifkaState_contextSet_eq_space {W : Type*} (s : KrifkaState W) :
    HasContextSet.toContextSet s = HasContextSet.toContextSet s.space := rfl

end Pragmatics.Assertion.Krifka
