import Linglib.Core.Discourse.Goal
import Linglib.Core.Discourse.SpeechActs
import Linglib.Core.QUD.Basic
import Linglib.Core.QUD.PrecisionProjection
import Linglib.Core.QUD.Relevance
import Linglib.Core.Inquisitive
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy

/-!
# Scoreboard: Unified Discourse State
@cite{roberts-2023} @cite{roberts-2012} @cite{lewis-1979} @cite{portner-2004}

The scoreboard K for a language game at time t is a tuple
⟨I, M, ≺, CG, QUD, G⟩ (@cite{roberts-2023} §2.1.1), tracking:

- **I**: the set of interlocutors
- **M**: illocutionary moves made so far (with subsets A, Q, D, Acc)
- **≺**: temporal order on moves
- **CG**: the common ground (propositions treated as mutually believed)
- **QUD**: the ordered set of questions under discussion
- **G**: the interlocutors' publicly evident goals, plans, and priorities

The three central elements — CG, QUD, G — are updated by the three
canonical speech acts via the **Illocutionary Force Linking Principle**
(@cite{roberts-2023} (56)):

| Clause type  | Semantic type      | Default force | Updates |
|-------------|-------------------|---------------|---------|
| declarative  | proposition        | assertion     | CG      |
| interrogative| set of propositions| interrogation | QUD     |
| imperative   | indexed property   | direction     | G       |

## Relation to Prior Work

@cite{lewis-1979}'s "scorekeeping in a language game" introduced the
metaphor. @cite{roberts-2012} formalized CG + QUD. @cite{portner-2004}
added the addressee's ToDo list. @cite{roberts-2023} unifies all three
into a single scoreboard and gives G richer internal structure
(conditional goals with hierarchical priorities, following @cite{bratman-1987}).
-/

namespace Core.Discourse

open Core.Proposition (BProp)

variable {W : Type*}

/-- The semantic type of a clause, determining its default illocutionary force.

    @cite{roberts-2023} (56): propositions → assertion, sets of propositions →
    interrogation, indexed properties → direction. -/
inductive SemanticType where
  /-- Type ⟨s, t⟩: a proposition (set of worlds) -/
  | proposition
  /-- Type ⟨⟨s, t⟩, t⟩: a set of propositions (Hamblin question denotation) -/
  | setOfPropositions
  /-- Type ⟨s, ⟨e, t⟩⟩: a property indexed to the addressee -/
  | indexedProperty
  deriving DecidableEq, Repr

/-- **Illocutionary Force Linking Principle** (@cite{roberts-2023} (56)):
    the default illocutionary force of a root sentence is determined by
    its semantic type.

    (a) proposition → assertion
    (b) set of propositions → interrogation
    (c) indexed property → direction -/
def forceLinkingPrinciple : SemanticType → IllocutionaryMood
  | .proposition       => .declarative
  | .setOfPropositions  => .interrogative
  | .indexedProperty    => .imperative

/-- The default semantic type for each illocutionary mood (inverse of IFLP). -/
def defaultSemanticType : IllocutionaryMood → SemanticType
  | .declarative   => .proposition
  | .interrogative  => .setOfPropositions
  | .imperative     => .indexedProperty
  | .promissive     => .indexedProperty  -- promissives also denote properties
  | .exclamative    => .proposition      -- exclamatives denote propositions

/-- IFLP round-trips for the three core moods. -/
theorem iflp_roundtrip_decl :
    forceLinkingPrinciple (defaultSemanticType .declarative) = .declarative := rfl
theorem iflp_roundtrip_interrog :
    forceLinkingPrinciple (defaultSemanticType .interrogative) = .interrogative := rfl
theorem iflp_roundtrip_imp :
    forceLinkingPrinciple (defaultSemanticType .imperative) = .imperative := rfl

/-! ## The Scoreboard -/

/-- An illocutionary move on the scoreboard.

    @cite{roberts-2023} §2.1.1: M is the set of moves, with distinguished
    subsets A (assertions), Q (questions), D (directions), Acc (accepted). -/
structure Move (W : Type*) where
  /-- Which kind of speech act -/
  mood : IllocutionaryMood
  /-- Propositional content (for assertions and questions; for directions,
      the propositional closure of the targeted property) -/
  content : BProp W
  /-- Who made the move -/
  agent : Nat  -- agent index into interlocutors
  /-- Whether this move has been accepted by the interlocutors -/
  accepted : Bool := false
  deriving Inhabited

/-- The scoreboard K for a language game.

    @cite{roberts-2023} §2.1.1: K = ⟨I, M, ≺, CG, QUD, G⟩.
    We represent ≺ implicitly via list order in `moves`. -/
structure Scoreboard (W : Type*) where
  /-- I: the interlocutors (by index) -/
  numInterlocutors : Nat
  /-- M: illocutionary moves in temporal order (≺ = list position) -/
  moves : List (Move W) := []
  /-- CG: the common ground — propositions treated as mutually believed.
      Represented as a list of propositions; the context set is their
      intersection. -/
  cg : List (BProp W) := []
  /-- QUD: questions under discussion (as a stack of proposition-sets).
      Simplified from the full `QUDStack` for composability. -/
  qud : List (BProp W) := []
  /-- G: per-agent goal sets. `goals[i]` is G_i.
      Length should equal `numInterlocutors`. -/
  goals : List (GoalSet W) := []
  deriving Inhabited

namespace Scoreboard

/-- The context set: worlds compatible with all CG propositions. -/
def contextSet (K : Scoreboard W) : BProp W :=
  λ w => K.cg.all (λ p => p w)

/-- An agent's goal set. Returns empty if index out of bounds. -/
def agentGoals (K : Scoreboard W) (i : Nat) : GoalSet W :=
  K.goals.getD i GoalSet.empty

/-- **Assertion update** (@cite{roberts-2023} (57), following @cite{stalnaker-1978}):
    If a proposition is asserted and accepted, it is added to CG_K. -/
def assertionUpdate (K : Scoreboard W) (p : BProp W) (agent : Nat) : Scoreboard W :=
  { K with
    cg := p :: K.cg
    moves := ⟨.declarative, p, agent, true⟩ :: K.moves }

/-- **Interrogation update** (@cite{roberts-2023} (58), following @cite{roberts-2012}):
    If a question is posed and accepted, it is added to QUD_K. -/
def interrogationUpdate (K : Scoreboard W) (q : BProp W) (agent : Nat) : Scoreboard W :=
  { K with
    qud := q :: K.qud
    moves := ⟨.interrogative, q, agent, true⟩ :: K.moves }

/-- **Direction update** (@cite{roberts-2023} (59)):
    If a targeted property is issued to addressee i and accepted,
    G_i is revised to include the realization of the property in any
    applicable circumstances. -/
def directionUpdate (K : Scoreboard W) (p : BProp W)
    (speaker target : Nat) (priority : Nat := 0) : Scoreboard W :=
  let newGoal : Goal W := { content := p, priority }
  let rec go : List (GoalSet W) → Nat → List (GoalSet W)
    | [], _ => []
    | gs :: rest, i => (if i == target then gs.add newGoal else gs) :: go rest (i + 1)
  let updatedGoals := go K.goals 0
  { K with
    goals := updatedGoals
    moves := ⟨.imperative, p, speaker, true⟩ :: K.moves }

/-- Assertion update adds to CG. -/
theorem assertion_adds_to_cg (K : Scoreboard W) (p : BProp W) (a : Nat) :
    (K.assertionUpdate p a).cg = p :: K.cg := rfl

/-- Direction update preserves CG. -/
theorem direction_preserves_cg (K : Scoreboard W) (p : BProp W) (s t pr : Nat) :
    (K.directionUpdate p s t pr).cg = K.cg := rfl

/-- Direction update preserves QUD. -/
theorem direction_preserves_qud (K : Scoreboard W) (p : BProp W) (s t pr : Nat) :
    (K.directionUpdate p s t pr).qud = K.qud := rfl

/-- Assertion update preserves G. -/
theorem assertion_preserves_goals (K : Scoreboard W) (p : BProp W) (a : Nat) :
    (K.assertionUpdate p a).goals = K.goals := rfl

end Scoreboard
end Core.Discourse
