import Linglib.Core.Discourse.Goal
import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment
import Linglib.Core.QUD.Basic
import Linglib.Core.QUD.PrecisionProjection
import Linglib.Core.QUD.Relevance
import Linglib.Core.Inquisitive
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Core.Mood.POSW

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

open Core.Mood (IllocutionaryMood)

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

@[simp] theorem forceLinkingPrinciple_proposition :
    forceLinkingPrinciple .proposition = .declarative := rfl

@[simp] theorem forceLinkingPrinciple_setOfPropositions :
    forceLinkingPrinciple .setOfPropositions = .interrogative := rfl

@[simp] theorem forceLinkingPrinciple_indexedProperty :
    forceLinkingPrinciple .indexedProperty = .imperative := rfl

/-- The default semantic type for each illocutionary mood (inverse of IFLP). -/
def defaultSemanticType : IllocutionaryMood → SemanticType
  | .declarative   => .proposition
  | .interrogative  => .setOfPropositions
  | .imperative     => .indexedProperty
  | .promissive     => .indexedProperty  -- promissives also denote properties
  | .exclamative    => .proposition      -- exclamatives denote propositions

@[simp] theorem defaultSemanticType_declarative :
    defaultSemanticType .declarative = .proposition := rfl

@[simp] theorem defaultSemanticType_interrogative :
    defaultSemanticType .interrogative = .setOfPropositions := rfl

@[simp] theorem defaultSemanticType_imperative :
    defaultSemanticType .imperative = .indexedProperty := rfl

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
  content : W → Prop
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
  cg : List (W → Prop) := []
  /-- QUD: questions under discussion (as a stack of proposition-sets).
      Simplified from the full `QUDStack` for composability. -/
  qud : List (W → Prop) := []
  /-- G: per-agent goal sets. `goals[i]` is G_i.
      Length should equal `numInterlocutors`. -/
  goals : List (GoalSet W) := []
  deriving Inhabited

namespace Scoreboard

/-- The context set: worlds compatible with all CG propositions. -/
def contextSet (K : Scoreboard W) : W → Prop :=
  λ w => ∀ p ∈ K.cg, p w

/-- An agent's goal set. Returns empty if index out of bounds. -/
def agentGoals (K : Scoreboard W) (i : Nat) : GoalSet W :=
  K.goals.getD i GoalSet.empty

/-- **Assertion update** (@cite{roberts-2023} (57), following @cite{stalnaker-1978}):
    If a proposition is asserted and accepted, it is added to CG_K. -/
def assertionUpdate (K : Scoreboard W) (p : W → Prop) (agent : Nat) : Scoreboard W :=
  { K with
    cg := p :: K.cg
    moves := ⟨.declarative, p, agent, true⟩ :: K.moves }

/-- **Interrogation update** (@cite{roberts-2023} (58), following @cite{roberts-2012}):
    If a question is posed and accepted, it is added to QUD_K. -/
def interrogationUpdate (K : Scoreboard W) (q : W → Prop) (agent : Nat) : Scoreboard W :=
  { K with
    qud := q :: K.qud
    moves := ⟨.interrogative, q, agent, true⟩ :: K.moves }

/-- **Direction update** (@cite{roberts-2023} (59)):
    If a targeted property is issued to addressee i and accepted,
    G_i is revised to include the realization of the property in any
    applicable circumstances. -/
def directionUpdate (K : Scoreboard W) (p : W → Prop)
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
@[simp] theorem assertion_adds_to_cg (K : Scoreboard W) (p : W → Prop) (a : Nat) :
    (K.assertionUpdate p a).cg = p :: K.cg := rfl

/-- Assertion update preserves QUD. -/
@[simp] theorem assertion_preserves_qud (K : Scoreboard W) (p : W → Prop) (a : Nat) :
    (K.assertionUpdate p a).qud = K.qud := rfl

/-- Assertion update preserves G. -/
@[simp] theorem assertion_preserves_goals (K : Scoreboard W) (p : W → Prop) (a : Nat) :
    (K.assertionUpdate p a).goals = K.goals := rfl

/-- Interrogation update adds to QUD. -/
@[simp] theorem interrogation_adds_to_qud (K : Scoreboard W) (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).qud = q :: K.qud := rfl

/-- Interrogation update preserves CG. -/
@[simp] theorem interrogation_preserves_cg (K : Scoreboard W) (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).cg = K.cg := rfl

/-- Interrogation update preserves G. -/
@[simp] theorem interrogation_preserves_goals (K : Scoreboard W) (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).goals = K.goals := rfl

/-- Direction update preserves CG. -/
@[simp] theorem direction_preserves_cg (K : Scoreboard W) (p : W → Prop) (s t pr : Nat) :
    (K.directionUpdate p s t pr).cg = K.cg := rfl

/-- Direction update preserves QUD. -/
@[simp] theorem direction_preserves_qud (K : Scoreboard W) (p : W → Prop) (s t pr : Nat) :
    (K.directionUpdate p s t pr).qud = K.qud := rfl

/-! ## POSW Substrate Bridge

The scoreboard's CG component projects into a `Core.Mood.POSW` substrate
(@cite{portner-2018}, eq. 1) whose `cs` is the scoreboard context set
and whose `lt` is trivial (we don't yet derive a preference ordering
from `G`; that wiring belongs with directive update via `POSW.star`).

This lets us *derive* the Stalnakerian assertion principle
(@cite{stalnaker-1978}) from `POSW.boxCs_plus_self` rather than
re-stipulating it: `assertionUpdate` corresponds, on the `cs` side,
to `POSW.plus`. -/

/-- Project the scoreboard's CG into a POSW substrate. The `cs`
    component is the scoreboard's `contextSet`; `lt` is the trivial
    relation (every world is at least as good as every other), pending
    a preference projection from `G` for directive wiring. -/
def toPOSW (K : Scoreboard W) : Core.Mood.POSW W where
  cs := K.contextSet
  lt := fun _ _ => True
  lt_refl  := fun _ _ => trivial
  lt_trans := fun _ _ _ _ _ _ _ _ => trivial

@[simp] theorem toPOSW_cs (K : Scoreboard W) :
    K.toPOSW.cs = K.contextSet := rfl

@[simp] theorem toPOSW_lt (K : Scoreboard W) (w v : W) :
    K.toPOSW.lt w v ↔ True := Iff.rfl

/-- **Assertion-as-`+`-update bridge** (@cite{stalnaker-1978},
    @cite{portner-2018} eq. 2a). Asserting `p` against scoreboard `K`
    refines the projected POSW exactly the way `POSW.plus` does:
    the new context set is the conjunction of the old context set with
    `p`. The bridge is definitional — `assertionUpdate` is `+`-update
    on the `cs` side. -/
theorem toPOSW_assertion_eq_plus (K : Scoreboard W) (p : W → Prop) (a : Nat) (w : W) :
    (K.assertionUpdate p a).toPOSW.cs w ↔ (K.toPOSW.plus p).cs w := by
  simp [toPOSW, contextSet, assertionUpdate, Core.Mood.POSW.plus]
  exact And.comm

/-- **Stalnakerian assertion principle** (@cite{stalnaker-1978}):
    after asserting `p`, `p` is informationally necessary on the
    projected POSW. *Derived* from `POSW.boxCs_plus_self` via the
    `toPOSW_assertion_eq_plus` bridge — not re-stipulated. -/
theorem boxCs_after_assertion (K : Scoreboard W) (p : W → Prop) (a : Nat) :
    (K.assertionUpdate p a).toPOSW.boxCs p := by
  intro w hw
  have hplus : (K.toPOSW.plus p).cs w := (toPOSW_assertion_eq_plus K p a w).mp hw
  exact Core.Mood.POSW.boxCs_plus_self K.toPOSW p w hplus

end Scoreboard
end Core.Discourse
