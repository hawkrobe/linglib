import Mathlib.Data.List.Sort
import Linglib.Discourse.SpeechAct
import Linglib.Discourse.Commitment.Basic
import Linglib.Discourse.Move
import Linglib.Semantics.Questions.Partition.QUD
import Linglib.Semantics.Questions.PrecisionProjection
import Linglib.Semantics.Mood.POSW
import Linglib.Semantics.Mood.POSWQ

/-!
# Scoreboard: Unified Discourse State
[roberts-2023] [roberts-2012] [lewis-1979] [portner-2004]

The scoreboard K for a language game at time t is a tuple
⟨I, M, ≺, CommonGround, QUD, G⟩ ([roberts-2023]), tracking:

- **I**: the set of interlocutors
- **M**: illocutionary moves made so far (with subsets A, Q, D, Acc)
- **≺**: temporal order on moves
- **CommonGround**: the common ground (propositions treated as mutually believed)
- **QUD**: the ordered set of questions under discussion
- **G**: the interlocutors' publicly evident goals, plans, and priorities

The three central elements — CommonGround, QUD, G — are updated by assertion,
interrogation, and direction respectively, via the Illocutionary
Force Linking Principle ([roberts-2023]).

-/

namespace Discourse

open Semantics.Mood (IllocutionaryMood)

variable {W : Type*}

/-! ### Goals (the G component) -/

/-- A single goal: a proposition the agent is committed to realizing,
    conditional on certain circumstances obtaining ([roberts-2023]). -/
structure Goal (W : Type*) where
  /-- The content: what the agent aims to bring about. -/
  content : W → Prop
  /-- Circumstances under which this goal is active.
      `λ _ => True` for unconditional goals. -/
  condition : W → Prop := λ _ => True
  /-- Priority level: 0 = highest priority. -/
  priority : Nat := 0
  deriving Inhabited

/-- An agent's goal set: publicly evident goals, plans, and priorities. -/
structure GoalSet (W : Type*) where
  goals : List (Goal W) := []
  deriving Inhabited

namespace GoalSet

/-- The empty goal set. -/
def empty : GoalSet W := ⟨[]⟩

@[simp] theorem empty_goals : (empty : GoalSet W).goals = [] := rfl

/-- Add a goal to the set. -/
def add (gs : GoalSet W) (g : Goal W) : GoalSet W :=
  ⟨g :: gs.goals⟩

@[simp] theorem add_goals (gs : GoalSet W) (g : Goal W) :
    (gs.add g).goals = g :: gs.goals := rfl

/-- Project to a flat list of contents ([portner-2004] ToDo list interface). -/
def toPropertyList (gs : GoalSet W) : List (W → Prop) :=
  gs.goals.map Goal.content

@[simp] theorem toPropertyList_empty :
    (empty : GoalSet W).toPropertyList = [] := rfl

@[simp] theorem toPropertyList_add (gs : GoalSet W) (g : Goal W) :
    (gs.add g).toPropertyList = g.content :: gs.toPropertyList := rfl

end GoalSet

/-- The semantic type of a clause, determining its default illocutionary force.

    [roberts-2023]: propositions → assertion, sets of propositions →
    interrogation, indexed properties → direction. -/
inductive SemanticType where
  /-- Type ⟨s, t⟩: a proposition (set of worlds) -/
  | proposition
  /-- Type ⟨⟨s, t⟩, t⟩: a set of propositions (Hamblin question denotation) -/
  | setOfPropositions
  /-- Type ⟨s, ⟨e, t⟩⟩: a property indexed to the addressee -/
  | indexedProperty
  deriving DecidableEq, Repr

/-- Illocutionary Force Linking Principle: the default illocutionary
    force of a root sentence is determined by its semantic type. -/
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

/-- The scoreboard K = ⟨I, M, ≺, CommonGround, QUD, G⟩. The temporal order ≺
    is implicit in list position of `moves`. `qud` is specialised to
    polar-question content (`W → Prop`); the richer `Discourse.QUDStack`
    over `Semantics.Questions.Basic.Question W` is consumed by other
    files. Bridging the two is an open API-coherence item. -/
structure Scoreboard (W : Type*) where
  numInterlocutors : Nat
  moves : List (Move W) := []
  cg : List (W → Prop) := []
  qud : List (W → Prop) := []
  goals : List (GoalSet W) := []
  deriving Inhabited

namespace Scoreboard

/-- The context set: worlds compatible with all CommonGround propositions. -/
def contextSet (K : Scoreboard W) : W → Prop :=
  λ w => ∀ p ∈ K.cg, p w

/-- An agent's goal set. Returns empty if index out of bounds. -/
def agentGoals (K : Scoreboard W) (i : Nat) : GoalSet W :=
  K.goals.getD i GoalSet.empty

/-- Assertion update: accepted assertion of `p` adds `p` to CommonGround. -/
def assertionUpdate (K : Scoreboard W) (p : W → Prop) (agent : Nat) : Scoreboard W :=
  { K with
    cg := p :: K.cg
    moves := ⟨.declarative, p, agent, True⟩ :: K.moves }

/-- Interrogation update: accepted question `q` adds `q` to QUD. -/
def interrogationUpdate (K : Scoreboard W) (q : W → Prop) (agent : Nat) : Scoreboard W :=
  { K with
    qud := q :: K.qud
    moves := ⟨.interrogative, q, agent, True⟩ :: K.moves }

/-- Add goal `g` to the agent at `target` index in `xs` (walking from `i`).
    Identity when `target` is out of range. -/
def addGoalAt : List (GoalSet W) → Nat → Nat → Goal W → List (GoalSet W)
  | [], _, _, _ => []
  | gs :: rest, target, i, g =>
      (if i == target then gs.add g else gs) :: addGoalAt rest target (i + 1) g

/-- If the walk is past `target`, `addGoalAt` is the identity. -/
lemma addGoalAt_out_of_range (xs : List (GoalSet W)) (target i : Nat) (g : Goal W)
    (h : target < i) : addGoalAt xs target i g = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons gs rest ih =>
    have hne : ¬ (i = target) := Nat.ne_of_gt h
    simp only [addGoalAt, beq_iff_eq, if_neg hne, List.cons.injEq, true_and]
    exact ih (i + 1) (by omega)

/-- Direction update: targeted property issued to addressee `target` and
    accepted; revises G_target to include the property's realization. -/
def directionUpdate (K : Scoreboard W) (p : W → Prop)
    (speaker target : Nat) (priority : Nat := 0) : Scoreboard W :=
  let newGoal : Goal W := { content := p, priority }
  { K with
    goals := addGoalAt K.goals target 0 newGoal
    moves := ⟨.imperative, p, speaker, True⟩ :: K.moves }

/-- Assertion update adds to CommonGround. -/
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

/-- Interrogation update preserves CommonGround. -/
@[simp] theorem interrogation_preserves_cg (K : Scoreboard W) (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).cg = K.cg := rfl

/-- Interrogation update preserves G. -/
@[simp] theorem interrogation_preserves_goals (K : Scoreboard W) (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).goals = K.goals := rfl

/-- Direction update preserves CommonGround. -/
@[simp] theorem direction_preserves_cg (K : Scoreboard W) (p : W → Prop) (s t pr : Nat) :
    (K.directionUpdate p s t pr).cg = K.cg := rfl

/-- Direction update preserves QUD. -/
@[simp] theorem direction_preserves_qud (K : Scoreboard W) (p : W → Prop) (s t pr : Nat) :
    (K.directionUpdate p s t pr).qud = K.qud := rfl

/-! ### POSW substrate bridge

The scoreboard's CommonGround and G components project jointly into a
`Semantics.Mood.POSW`: CommonGround via `contextSet`, G via the goal-induced
preference ordering. Assertion ↔ `plus`, direction ↔ `star`. -/

/-- Flat list of goal contents across all agents. -/
def goalContents (K : Scoreboard W) : List (W → Prop) :=
  K.goals.flatMap GoalSet.toPropertyList

/-- Assertion update preserves goal contents (since it doesn't touch G). -/
@[simp] theorem assertion_preserves_goalContents (K : Scoreboard W)
    (p : W → Prop) (a : Nat) :
    (K.assertionUpdate p a).goalContents = K.goalContents := rfl

/-- After a `directionUpdate`, the new directive's content joins the
    flat goal-content list. Requires `target` in bounds. -/
lemma mem_addGoalAt_flatMap (xs : List (GoalSet W)) (target i : Nat) (g : Goal W)
    (hin : i ≤ target) (hbd : target < i + xs.length) (q : W → Prop) :
    q ∈ (addGoalAt xs target i g).flatMap GoalSet.toPropertyList ↔
    q = g.content ∨ q ∈ xs.flatMap GoalSet.toPropertyList := by
  induction xs generalizing i with
  | nil => simp at hbd; omega
  | cons gs rest ih =>
    by_cases hT : i = target
    · -- i = target: the new goal is inserted in this slot
      subst hT
      have hrest : addGoalAt rest i (i + 1) g = rest :=
        addGoalAt_out_of_range rest i (i + 1) g (by omega)
      simp only [addGoalAt, beq_self_eq_true, if_true, hrest,
        List.flatMap_cons, List.mem_append, GoalSet.toPropertyList,
        GoalSet.add_goals, List.map_cons, List.mem_cons]
      tauto
    · -- i < target: walk past this slot, recurse
      have hi : ¬ (i = target) := hT
      have hin' : i + 1 ≤ target := by omega
      have hbd' : target < (i + 1) + rest.length := by
        have : i + (gs :: rest).length = (i + 1) + rest.length := by simp; omega
        omega
      simp only [addGoalAt, beq_iff_eq, if_neg hi,
        List.flatMap_cons, List.mem_append]
      rw [ih (i + 1) hin' hbd']
      tauto

/-- Membership in the flat goal-content list after `directionUpdate`:
    the new directive's content joins the existing goal contents. -/
lemma mem_directionUpdate_goalContents (K : Scoreboard W) (p : W → Prop)
    (s t pr : Nat) (hin : t < K.goals.length) (q : W → Prop) :
    q ∈ (K.directionUpdate p s t pr).goalContents ↔
    q = p ∨ q ∈ K.goalContents := by
  unfold goalContents directionUpdate
  exact mem_addGoalAt_flatMap K.goals t 0 ⟨p, fun _ => True, pr⟩
    (Nat.zero_le _) (by simpa using hin) q

/-- Project the scoreboard into a POSW: `cs` from CommonGround, `le` from
    goal-induced preference. -/
def toPOSW (K : Scoreboard W) : Semantics.Mood.POSW W where
  cs := K.contextSet
  le := fun w v => ∀ p ∈ K.goalContents, p v → p w
  le_refl  := fun _ _ _ _ hp => hp
  le_trans := fun _ _ _ _ _ _ hwu huv p hp hpv => hwu p hp (huv p hp hpv)

@[simp] theorem toPOSW_cs (K : Scoreboard W) :
    K.toPOSW.cs = K.contextSet := rfl

@[simp] theorem toPOSW_le (K : Scoreboard W) (w v : W) :
    K.toPOSW.le w v ↔ ∀ p ∈ K.goalContents, p v → p w := Iff.rfl

/-- Assertion-as-`+`-update bridge: `assertionUpdate` refines the
    projected POSW's `cs` exactly as `POSW.plus` does. -/
theorem toPOSW_assertion_eq_plus (K : Scoreboard W) (p : W → Prop) (a : Nat) (w : W) :
    (K.assertionUpdate p a).toPOSW.cs w ↔ (K.toPOSW.plus p).cs w := by
  simp [toPOSW, contextSet, assertionUpdate, Semantics.Mood.POSW.plus]
  exact And.comm

/-- After asserting `p`, `p` is informationally necessary on the
    projected POSW (Stalnakerian assertion principle). -/
theorem boxCs_after_assertion (K : Scoreboard W) (p : W → Prop) (a : Nat) :
    (K.assertionUpdate p a).toPOSW.boxCs p := by
  intro w hw
  have hplus : (K.toPOSW.plus p).cs w := (toPOSW_assertion_eq_plus K p a w).mp hw
  exact Semantics.Mood.POSW.boxCs_plus_self K.toPOSW p w hplus

/-- Direction-as-`⋆`-update bridge: `directionUpdate` refines the
    projected POSW's `le` exactly as `POSW.star` does
    (modulo target-in-bounds). -/
theorem toPOSW_direction_eq_star (K : Scoreboard W) (p : W → Prop)
    (s t pr : Nat) (hin : t < K.goals.length) (w v : W) :
    (K.directionUpdate p s t pr).toPOSW.le w v ↔ (K.toPOSW.star p).le w v := by
  simp only [toPOSW_le, Semantics.Mood.POSW.star_le]
  constructor
  · intro h
    refine ⟨fun q hq => h q ?_, h p ?_⟩
    · exact (mem_directionUpdate_goalContents K p s t pr hin q).mpr (Or.inr hq)
    · exact (mem_directionUpdate_goalContents K p s t pr hin p).mpr (Or.inl rfl)
  · rintro ⟨h1, h2⟩ q hq
    rcases (mem_directionUpdate_goalContents K p s t pr hin q).mp hq with rfl | hq'
    · exact h2
    · exact h1 q hq'

/-- After `directionUpdate p`, no `p`-violator dominates a `p`-satisfier. -/
theorem direction_demotes_violators (K : Scoreboard W) (p : W → Prop)
    (s t pr : Nat) (hin : t < K.goals.length) (w v : W)
    (hpv : p v) (hpw : ¬ p w) :
    ¬ (K.directionUpdate p s t pr).toPOSW.le w v := by
  intro hlt
  have hstar : (K.toPOSW.star p).le w v :=
    (toPOSW_direction_eq_star K p s t pr hin w v).mp hlt
  exact hpw (hstar.2 hpv)

/-! ### POSWQ inquiry-partition bridge

QUD projects into POSWQ's inquiry partition: meet of polar Setoids
over the QUD stack. Interrogation ↔ `inquire`. -/

/-- Inquiry partition from the QUD stack: meet of polar Setoids
    (`⊤` as identity). Cons-right convention so that consing reduces
    definitionally to `inquire`. -/
def qudInquiry (K : Scoreboard W) : Setoid W :=
  K.qud.foldr (fun q s => s ⊓ Semantics.Mood.POSWQ.polarSetoid q) ⊤

@[simp] theorem qudInquiry_nil (K : Scoreboard W) (h : K.qud = []) :
    K.qudInquiry = (⊤ : Setoid W) := by
  simp [qudInquiry, h]

@[simp] theorem qudInquiry_cons (K : Scoreboard W) (q : W → Prop)
    (rest : List (W → Prop)) (h : K.qud = q :: rest) :
    K.qudInquiry =
      (rest.foldr (fun q s => s ⊓ Semantics.Mood.POSWQ.polarSetoid q) ⊤) ⊓
        Semantics.Mood.POSWQ.polarSetoid q := by
  simp [qudInquiry, h]

/-- Interrogation update preserves goal contents (doesn't touch G). -/
@[simp] theorem interrogation_preserves_goalContents (K : Scoreboard W)
    (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).goalContents = K.goalContents := rfl

/-- Project the scoreboard into a POSWQ: underlying POSW + QUD inquiry. -/
def toPOSWQ (K : Scoreboard W) : Semantics.Mood.POSWQ W :=
  { K.toPOSW with inquiry := K.qudInquiry }

@[simp] theorem toPOSWQ_toPOSW (K : Scoreboard W) :
    K.toPOSWQ.toPOSW = K.toPOSW := rfl

@[simp] theorem toPOSWQ_inquiry (K : Scoreboard W) :
    K.toPOSWQ.inquiry = K.qudInquiry := rfl

/-- Interrogation-as-`?`-update bridge: `interrogationUpdate` refines
    the projected POSWQ's `inquiry` exactly as `POSWQ.inquire` does. -/
theorem toPOSWQ_interrogation_eq_inquire (K : Scoreboard W)
    (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).toPOSWQ.inquiry =
      (K.toPOSWQ.inquire (Semantics.Mood.POSWQ.polarSetoid q)).inquiry := rfl

/-- After posing `q`, the polar partition of `q` is settled by
    the new POSWQ (inquiry analogue of `boxCs_after_assertion`). -/
theorem boxAns_polar_after_interrogation (K : Scoreboard W)
    (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).toPOSWQ.boxAns q := by
  intro w v _ _ hwv
  exact hwv.2

end Scoreboard
end Discourse
