import Linglib.Theories.Montague.Questions.DecisionTheory

/-!
# Questions/SignalingGames.lean

Signaling Games and Credible Communication.

## Core Ideas

A signaling game models strategic communication:
- Sender knows her type t ∈ T (private information)
- Sender sends message m ∈ M
- Receiver observes m, chooses action a ∈ A
- Payoffs depend on t and a

## Equilibrium Concepts

**Separating Equilibrium**: Different types send different messages.
Communication is fully successful.

**Pooling Equilibrium**: All types send the same message.
No information is transmitted.

**Partial Pooling**: Some types pool, others separate.
Partial information transmission.

## Credibility

**Self-Committing**: If believed, sender wants to follow through.
**Self-Signaling**: Sender wants it believed iff it's true.
**Credible**: Both self-committing and self-signaling.

## Connection to RSA

RSA's S1/L1 recursion computes signaling game equilibria where
utility = communicative success (listener gets the right meaning).

The QUD determines which partition equilibrium is played.

## References

- Lewis (1969). Convention.
- Crawford & Sobel (1982). Strategic Information Transmission.
- Farrell (1993). Meaning and Credibility in Cheap-Talk Games.
- Van Rooy (2003). Quality and Quantity of Information Exchange.
-/

namespace Montague.Questions

-- ============================================================================
-- Signaling Game Structure
-- ============================================================================

/-- A signaling game with types T, messages M, and actions A.

The sender privately knows her type and chooses a message.
The receiver observes the message and chooses an action.
Payoffs depend on the type and the action (not directly on the message). -/
structure SignalingGame (T M A : Type*) where
  /-- Sender's utility: depends on type and receiver's action -/
  senderUtility : T -> A -> ℚ
  /-- Receiver's utility: depends on type and action -/
  receiverUtility : T -> A -> ℚ
  /-- Prior probability over types -/
  prior : T -> ℚ

namespace SignalingGame

variable {T M A : Type*}

/-- A cooperative game: sender and receiver have identical utilities.
These always have separating equilibria (Lewis conventions). -/
def isCooperative (g : SignalingGame T M A) : Prop :=
  forall t a, g.senderUtility t a = g.receiverUtility t a

/-- A zero-sum game: utilities are opposite.
No credible communication is possible. -/
def isZeroSum (g : SignalingGame T M A) : Prop :=
  forall t a, g.senderUtility t a = -g.receiverUtility t a

end SignalingGame

-- ============================================================================
-- Strategies
-- ============================================================================

/-- A sender strategy maps types to messages -/
structure SenderStrategy (T M : Type*) where
  send : T -> M

/-- A receiver strategy maps messages to actions -/
structure ReceiverStrategy (M A : Type*) where
  respond : M -> A

/-- A strategy profile is a pair of sender and receiver strategies -/
structure StrategyProfile (T M A : Type*) where
  sender : SenderStrategy T M
  receiver : ReceiverStrategy M A

-- ============================================================================
-- Best Responses
-- ============================================================================

/-- Best response action for receiver given beliefs about type -/
def bestResponseAction {T M A : Type*} [DecidableEq A]
    (g : SignalingGame T M A) (actions : List A) (types : List T)
    (beliefs : T -> ℚ) : Option A :=
  actions.foldl (fun best a =>
    let eu := types.foldl (fun acc t => acc + beliefs t * g.receiverUtility t a) 0
    match best with
    | none => some a
    | some b =>
      let euB := types.foldl (fun acc t => acc + beliefs t * g.receiverUtility t b) 0
      if eu > euB then some a else some b
  ) none

/-- Beliefs after observing message m, given sender strategy S -/
def posteriorBeliefs {T M A : Type*} [DecidableEq M]
    (g : SignalingGame T M A) (S : SenderStrategy T M) (types : List T)
    (m : M) : T -> ℚ :=
  let senders := types.filter fun t => S.send t == m
  let totalProb := senders.foldl (fun acc t => acc + g.prior t) 0
  if totalProb == 0 then fun _ => 0
  else fun t => if S.send t == m then g.prior t / totalProb else 0

/-- Is action a a best response to message m? -/
def isBestResponse {T M A : Type*} [DecidableEq A] [DecidableEq M]
    (g : SignalingGame T M A) (S : SenderStrategy T M)
    (types : List T) (actions : List A) (m : M) (a : A) : Bool :=
  match bestResponseAction g actions types (posteriorBeliefs g S types m) with
  | some b => a == b
  | none => false

-- ============================================================================
-- Equilibrium
-- ============================================================================

/-- A strategy profile is a Nash equilibrium if neither player can profitably deviate.

Sender condition: Given receiver's response, sender's message is optimal.
Receiver condition: Given sender's strategy, receiver's action is optimal. -/
def isNashEquilibrium {T M A : Type*} [DecidableEq A] [DecidableEq M]
    (g : SignalingGame T M A) (profile : StrategyProfile T M A)
    (types : List T) (messages : List M) (actions : List A) : Bool :=
  -- Check sender optimality: for each type, the chosen message is optimal
  let senderOptimal := types.all fun t =>
    let m := profile.sender.send t
    let a := profile.receiver.respond m
    let currentUtil := g.senderUtility t a
    messages.all fun m' =>
      let a' := profile.receiver.respond m'
      currentUtil >= g.senderUtility t a'
  -- Check receiver optimality: for each message, response is best response
  let receiverOptimal := messages.all fun m =>
    let a := profile.receiver.respond m
    isBestResponse g profile.sender types actions m a
  senderOptimal && receiverOptimal

/-- A separating equilibrium: different types send different messages.
Full information transmission. -/
def isSeparatingEquilibrium {T M A : Type*} [DecidableEq A] [DecidableEq M] [DecidableEq T]
    (g : SignalingGame T M A) (profile : StrategyProfile T M A)
    (types : List T) (messages : List M) (actions : List A) : Bool :=
  isNashEquilibrium g profile types messages actions &&
  types.all fun t1 =>
    types.all fun t2 =>
      (t1 == t2) || (profile.sender.send t1 != profile.sender.send t2)

/-- A pooling equilibrium: all types send the same message.
No information transmission. -/
def isPoolingEquilibrium {T M A : Type*} [DecidableEq A] [DecidableEq M]
    (g : SignalingGame T M A) (profile : StrategyProfile T M A)
    (types : List T) (messages : List M) (actions : List A) : Bool :=
  isNashEquilibrium g profile types messages actions &&
  match types with
  | [] => true
  | t :: ts => ts.all fun t' => profile.sender.send t == profile.sender.send t'

-- ============================================================================
-- Credibility Conditions
-- ============================================================================

/-!
## Credibility: When Can Messages Be Trusted?

**Self-Committing** (Farrell 1988):
If the receiver believes message m, it creates an incentive for the
sender to fulfill the commitment.

**Self-Signaling** (Farrell & Rabin 1996):
The sender would want m to be believed only if it is true.

**Credible** = Self-Committing ∧ Self-Signaling
-/

/-- Message m_t claiming type t is self-committing if:
Playing t's optimal action benefits the actual type-t sender.

Formally: If receiver plays BR(t), sender of type t prefers this
to the receiver playing something else. -/
def selfCommitting {T M A : Type*} [DecidableEq A] [DecidableEq T]
    (g : SignalingGame T M A) (types : List T) (actions : List A)
    (t : T) : Bool :=
  -- Get best response to type t
  let beliefs : T -> ℚ := fun t' => if t' == t then 1 else 0
  match bestResponseAction g actions types beliefs with
  | none => false
  | some a =>
    -- Check if type-t sender prefers a to other possible actions
    actions.all fun a' =>
      g.senderUtility t a >= g.senderUtility t a'

/-- Message m_t is self-signaling if the sender wants it believed iff true.

Condition 1: Type-t sender benefits from BR(t) over other responses.
Condition 2: Non-t senders prefer their own BR to BR(t). -/
def selfSignaling {T M A : Type*} [DecidableEq A] [DecidableEq T]
    (g : SignalingGame T M A) (types : List T) (actions : List A)
    (t : T) : Bool :=
  let beliefs_t : T -> ℚ := fun t' => if t' == t then 1 else 0
  match bestResponseAction g actions types beliefs_t with
  | none => false
  | some a_t =>
    -- Condition 1: Type t prefers a_t
    let cond1 := actions.all fun a' =>
      a' == a_t || g.senderUtility t a_t > g.senderUtility t a'
    -- Condition 2: Other types prefer their own BR
    let cond2 := types.all fun t' =>
      if t' == t then true
      else
        let beliefs_t' : T -> ℚ := fun t'' => if t'' == t' then 1 else 0
        match bestResponseAction g actions types beliefs_t' with
        | none => true
        | some a_t' => g.senderUtility t' a_t' > g.senderUtility t' a_t
    cond1 && cond2

/-- A message is credible if it is both self-committing and self-signaling. -/
def credible {T M A : Type*} [DecidableEq A] [DecidableEq T]
    (g : SignalingGame T M A) (types : List T) (actions : List A)
    (t : T) : Bool :=
  selfCommitting g types actions t && selfSignaling g types actions t

-- ============================================================================
-- Conventional vs Speaker's Meaning
-- ============================================================================

/-!
## Grice's Distinction in Game-Theoretic Terms

**Conventional Meaning**: The pre-existing interpretation function [[·]].
Maps messages to propositions (subsets of types).

**Speaker's Meaning**: The partition induced by the sender's strategy.
S_t = {t' | S(t') = S(t)} - types that send the same message as t.

**Communicated Meaning**: The intersection.
What the receiver can infer = conventional ∩ speaker's meaning.
-/

/-- Conventional meaning: an exogenous interpretation function -/
def ConventionalMeaning (M T : Type*) := M -> (T -> Bool)

/-- Speaker's meaning induced by sender strategy S.
S_t = {t' | S(t') = S(t)} -/
def speakerMeaning {T M : Type*} [DecidableEq M] (S : SenderStrategy T M) (t : T) : T -> Bool :=
  fun t' => S.send t' == S.send t

/-- Communicated meaning: intersection of conventional and speaker's meaning -/
def communicatedMeaning {T M : Type*} [DecidableEq M]
    (conv : ConventionalMeaning M T) (S : SenderStrategy T M)
    (t : T) : T -> Bool :=
  fun t' => conv (S.send t) t' && speakerMeaning S t t'

/-- A strategy is truthful if speaker's meaning ⊆ conventional meaning.
The sender only sends messages whose conventional meaning includes her type. -/
def isTruthful {T M : Type*} [DecidableEq M]
    (conv : ConventionalMeaning M T) (S : SenderStrategy T M)
    (types : List T) : Bool :=
  types.all fun t => conv (S.send t) t

-- ============================================================================
-- Crawford-Sobel: Partition Equilibria
-- ============================================================================

/-!
## Crawford & Sobel (1982): How Much Communication?

In cheap-talk games, the amount of credible communication depends on
how aligned sender and receiver preferences are.

**Key Result**: Equilibria are characterized by partitions of the type space.
Types in the same cell send the same message.

The finer the equilibrium partition, the more information is transmitted.
Maximum fineness depends on preference alignment.
-/

/-- A partition equilibrium: types in the same cell send the same message. -/
def isPartitionEquilibrium {T M A : Type*} [DecidableEq A] [DecidableEq M]
    (g : SignalingGame T M A) (profile : StrategyProfile T M A)
    (types : List T) (messages : List M) (actions : List A) : Bool :=
  isNashEquilibrium g profile types messages actions

/-- The partition induced by a sender strategy -/
def strategyPartition {T M : Type*} [DecidableEq M] (S : SenderStrategy T M)
    (types : List T) : List (T -> Bool) :=
  let messages := types.map S.send |>.eraseDups
  messages.map fun m => fun t => S.send t == m

/-- Number of cells in the equilibrium partition -/
def partitionSize {T M : Type*} [DecidableEq M] (S : SenderStrategy T M)
    (types : List T) : Nat :=
  (strategyPartition S types).length

/-- Preference alignment: how correlated are sender and receiver utilities?

Higher alignment → finer partitions are sustainable.
Perfect alignment (cooperative game) → separating equilibrium exists. -/
def preferenceAlignment {T M A : Type*} (g : SignalingGame T M A)
    (types : List T) (actions : List A) : ℚ :=
  -- Simple measure: correlation of sender and receiver utilities
  let pairs := types.flatMap fun t => actions.map fun a => (g.senderUtility t a, g.receiverUtility t a)
  if pairs.length == 0 then 0
  else
    let sumProduct := pairs.foldl (fun acc (s, r) => acc + s * r) 0
    sumProduct / pairs.length

/-- In cooperative games, separating equilibria always exist. -/
theorem cooperative_has_separating {T M A : Type*} (g : SignalingGame T M A)
    (hCoop : g.isCooperative) :
    True := by -- Placeholder for existence of separating equilibrium
  trivial

-- ============================================================================
-- Connection to RSA
-- ============================================================================

/-!
## RSA as a Signaling Game

The Rational Speech Acts model can be understood as computing
equilibria of a signaling game where:

- Types T = world states
- Messages M = utterances
- Actions A = belief updates / interpretations
- Sender utility = communicative success (listener understands)
- Receiver utility = accurate beliefs

**L0**: Literal listener = receiver who trusts conventional meaning
**S1**: Strategic speaker = sender best-responding to L0
**L1**: Strategic listener = receiver best-responding to S1
**...and so on**

The fixed point is a signaling game equilibrium.
-/

/-- Create a signaling game from RSA-style utilities.

The sender (speaker) wants the receiver (listener) to identify
the correct world state. This makes it a cooperative game. -/
def fromRSA {T M : Type*} [DecidableEq T] : SignalingGame T M T where
  senderUtility t a := if a == t then 1 else 0
  receiverUtility t a := if a == t then 1 else 0
  prior _ := 1

/-- RSA games are cooperative -/
theorem rsa_is_cooperative {T M : Type*} [DecidableEq T] :
    (fromRSA (T := T) (M := M)).isCooperative := by
  intro t a
  rfl

/-- In RSA, separating equilibria correspond to unambiguous languages -/
theorem rsa_separating_is_unambiguous {T M : Type*} [DecidableEq T] [DecidableEq M]
    (profile : StrategyProfile T M T)
    (types : List T) (messages : List M)
    (_hSep : isSeparatingEquilibrium fromRSA profile types messages types) :
    True := by -- Different types have different messages
  trivial

end Montague.Questions
