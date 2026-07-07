import Linglib.Semantics.Intensional.WorldTimeIndex
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Mood.Defs
import Linglib.Semantics.Mood.Modal
import Linglib.Discourse.SpeechAct
import Linglib.Semantics.Modality.Kratzer.Flavor
import Linglib.Semantics.Modality.Directive
import Linglib.Semantics.Mood.SpeechEvent
import Linglib.Studies.RuytenbeekEtAl2017
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Sort
import Linglib.Discourse.Commitment.Basic
import Linglib.Semantics.Questions.Partition.QUD
import Linglib.Semantics.Questions.PrecisionProjection
import Linglib.Semantics.Mood.State

/-!
# Roberts (2023): Imperatives in Dynamic Pragmatics
[roberts-2023]

Imperatives in dynamic pragmatics. *Semantics & Pragmatics* 16, Article 7: 1–55.

## Core Contribution

A semantics and dynamic pragmatics for imperative mood that combines the
best features of [kaufmann-2012] and [portner-2004]:

1. **Semantic type**: Imperatives denote *de se* properties indexed to the
   addressee — following [portner-2004].
2. **Modal in semantic content**: The content includes a futurate
   circumstantial modal with Kratzerian modal base *f* and goal-based
   ordering source *g* — following [kaufmann-2012]. But the modal
   is **not deontic**.
3. **Pragmatic deontic flavor**: The perceived deontic force arises
   entirely from the pragmatics of accepting a direction — updating the
   addressee's preference structure (the goals component G of the
   discourse scoreboard) — not from the LF.

## Substrate hookup

This file is a **configuration of existing infrastructure**, not a
standalone formalization of an imperative mood ontology:

- The futurate modal base reuses
  `HistoricalAlternatives.futureHistoryBase`.
- The goal-based ordering and circumstantial modal base are
  `Kratzer.OrderingSource` / `ModalBase`, packaged as
  `TeleologicalFlavor` (no parallel types).
- The architectural commitment "imperative force targets the
  preferential POSW component, not the informational" is
  `Mood.Component`'s `HasTarget Illocutionary`
  instance — Roberts agrees with [portner-2018] on the
  POSW component, disagrees with [kaufmann-2012] only on
  the prejacent's modal flavor.
- The scoreboard updates are `Discourse.Scoreboard`'s
  assertion/interrogation/direction; the *derivation* that
  `directionUpdate` factors as `ExpState.promote` lives in the
  Scoreboard section (`toExpState_direction_eq_promote`).

## Equation citations

All equation numbers verified against the published PDF:
(45) circumstance, (47) SameHistory, (48) FUT, (49) goal-based
ordering source, (50) timely future, (51) futurate circumstantial
modal base, (53) APPLIC, (54)/(67) imperative character ¡,
(57) assertion, (58) interrogation, (59) direction, (65)
conservativity. Example "Have a cookie" is (60) in §2.2 (not §3).
-/

/-!### Discourse Move
[roberts-2023] [lewis-1979]

An illocutionary move: speaker performs `mood F(p)` for some content `p`,
addressed to an interlocutor, possibly accepted.

[roberts-2023] §2.1.1: M is the set of moves on the scoreboard, with
distinguished subsets A (assertions), Q (questions), D (directions),
Acc (accepted).

## Main definitions

* `Move W` — ⟨mood, content, agent, accepted⟩.
-/

namespace Discourse

open Mood (Illocutionary)

/-- An illocutionary move: a speech act performed by an agent. -/
structure Move (W : Type*) where
  /-- Which kind of speech act. -/
  mood : Illocutionary
  /-- Propositional content (for assertions and questions; for directions,
      the propositional closure of the targeted property). -/
  content : W → Prop
  /-- Who made the move (agent index into interlocutors). -/
  agent : Nat
  /-- Whether this move has been accepted by the interlocutors. -/
  accepted : Prop := False
  deriving Inhabited

end Discourse


/-!### Scoreboard: Unified Discourse State
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

open Mood (Illocutionary)

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
def forceLinkingPrinciple : SemanticType → Illocutionary
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
def defaultSemanticType : Illocutionary → SemanticType
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
the POSW substrate (`Semantics.Dynamic.Default.ExpState` under its
`Semantics/Mood/Modal.lean` modal reading): CommonGround via
`contextSet`, G via the goal-induced preference ordering. Assertion ↔
`assert`, direction ↔ `promote`. -/

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

/-- Project the scoreboard into a POSW-style expectation state: `info`
    from CommonGround, `order` from goal-induced preference. -/
def toExpState (K : Scoreboard W) : Semantics.Dynamic.Default.ExpState W where
  info := K.contextSet
  order := Preorder.ofLE (fun w v => ∀ p ∈ K.goalContents, p v → p w)
    (fun _ _ _ hp => hp)
    (fun _ _ _ hwu huv p hp hpv => hwu p hp (huv p hp hpv))

@[simp] theorem toExpState_info (K : Scoreboard W) :
    K.toExpState.info = K.contextSet := rfl

@[simp] theorem toExpState_le (K : Scoreboard W) (w v : W) :
    K.toExpState.order.le w v ↔ ∀ p ∈ K.goalContents, p v → p w := Iff.rfl

/-- Assertion-as-`+`-update bridge: `assertionUpdate` refines the
    projected state's `info` exactly as `ExpState.assert` does. -/
theorem toExpState_assertion_eq_assert (K : Scoreboard W) (p : W → Prop) (a : Nat) (w : W) :
    w ∈ (K.assertionUpdate p a).toExpState.info ↔
      w ∈ (K.toExpState.assert p).info := by
  show (∀ q ∈ p :: K.cg, q w) ↔ (∀ q ∈ K.cg, q w) ∧ p w
  rw [List.forall_mem_cons]
  exact And.comm

/-- After asserting `p`, `p` is informationally necessary on the
    projected state (Stalnakerian assertion principle). -/
theorem boxCs_after_assertion (K : Scoreboard W) (p : W → Prop) (a : Nat) :
    (K.assertionUpdate p a).toExpState.boxCs p := by
  intro w hw
  have hassert : w ∈ (K.toExpState.assert p).info :=
    (toExpState_assertion_eq_assert K p a w).mp hw
  exact K.toExpState.boxCs_assert_self p w hassert

/-- Direction-as-`⋆`-update bridge: `directionUpdate` refines the
    projected state's `order` exactly as `ExpState.promote` does
    (modulo target-in-bounds). -/
theorem toExpState_direction_eq_promote (K : Scoreboard W) (p : W → Prop)
    (s t pr : Nat) (hin : t < K.goals.length) (w v : W) :
    (K.directionUpdate p s t pr).toExpState.order.le w v ↔
      (K.toExpState.promote p).order.le w v := by
  simp only [toExpState_le, Semantics.Dynamic.Default.ExpState.promote_order,
    Core.Order.Normality.refine_le, toExpState_le]
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
    ¬ (K.directionUpdate p s t pr).toExpState.order.le w v := by
  intro hlt
  have hstar : (K.toExpState.promote p).order.le w v :=
    (toExpState_direction_eq_promote K p s t pr hin w v).mp hlt
  exact hpw ((Core.Order.Normality.refine_le.mp hstar).2 hpv)

/-! ### State inquiry-partition bridge

QUD projects into State's inquiry partition: meet of polar Setoids
over the QUD stack. Interrogation ↔ `inquire`. -/

/-- Inquiry partition from the QUD stack: meet of polar Setoids
    (`⊤` as identity). Cons-right convention so that consing reduces
    definitionally to `inquire`. -/
def qudInquiry (K : Scoreboard W) : Setoid W :=
  K.qud.foldr (fun q s => s ⊓ Mood.State.polarSetoid q) ⊤

@[simp] theorem qudInquiry_nil (K : Scoreboard W) (h : K.qud = []) :
    K.qudInquiry = (⊤ : Setoid W) := by
  simp [qudInquiry, h]

@[simp] theorem qudInquiry_cons (K : Scoreboard W) (q : W → Prop)
    (rest : List (W → Prop)) (h : K.qud = q :: rest) :
    K.qudInquiry =
      (rest.foldr (fun q s => s ⊓ Mood.State.polarSetoid q) ⊤) ⊓
        Mood.State.polarSetoid q := by
  simp [qudInquiry, h]

/-- Interrogation update preserves goal contents (doesn't touch G). -/
@[simp] theorem interrogation_preserves_goalContents (K : Scoreboard W)
    (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).goalContents = K.goalContents := rfl

/-- Project the scoreboard into a State: underlying state + QUD inquiry. -/
def toMoodState (K : Scoreboard W) : Mood.State W :=
  { K.toExpState with inquiry := K.qudInquiry }

@[simp] theorem toMoodState_toExpState (K : Scoreboard W) :
    K.toMoodState.toExpState = K.toExpState := rfl

@[simp] theorem toMoodState_inquiry (K : Scoreboard W) :
    K.toMoodState.inquiry = K.qudInquiry := rfl

/-- Interrogation-as-`?`-update bridge: `interrogationUpdate` refines
    the projected State's `inquiry` exactly as `State.inquire` does. -/
theorem toMoodState_interrogation_eq_inquire (K : Scoreboard W)
    (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).toMoodState.inquiry =
      (K.toMoodState.inquire (Mood.State.polarSetoid q)).inquiry := rfl

/-- After posing `q`, the polar partition of `q` is settled by
    the new State (inquiry analogue of `boxCs_after_assertion`). -/
theorem boxAns_polar_after_interrogation (K : Scoreboard W)
    (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).toMoodState.boxAns q := by
  intro w v _ _ hwv
  exact hwv.2

end Scoreboard
end Discourse


namespace Roberts2023

open Intensional (WorldTimeIndex)
open Discourse (forceLinkingPrinciple defaultSemanticType Scoreboard)
open Mood.Illocutionary (sincerityCondition)
open Mood (State Component Illocutionary HasTarget)
open Semantics.Dynamic.Default (ExpState)
open HistoricalAlternatives
open Semantics.Modality.Kratzer

abbrev World := Fin 4

/-! ## §2.1.2 Basic Ontology

Roberts's "circumstance" ⟨w, t⟩ (eq. 45), SameHistory (47), and FUT
(48) all instantiate the canonical world-time substrate in
`Intensional.WorldTimeIndex` and `HistoricalAlternatives`:

  Roberts                        Linglib substrate
  ────────────────────────────   ────────────────────────────
  ⟨w, t⟩ circumstance            `WorldTimeIndex W T`
  SameHistory(w', w, t)          `HistoricalAlternatives W T` predicate
  FUT(⟨w, t⟩)                    `futureHistoryBase history s`

No new types are introduced for these. -/

/-! ## §2.1.2 The Imperative Character

Roberts's `¡` (eq. 54/67) bundles the addressee, the prejacent, and
the modal parameters. The modal flavor is **teleological** — facts
plus goals — represented directly by `Kratzer.TeleologicalFlavor`.
The "futurate" property of the modal base is enforced separately as
the predicate `IsFuturate` below, which uses `futureHistoryBase`. -/

/-- Roberts's imperative character `¡` ([roberts-2023] (54)/(67)).
    Bundles the addressee, the prejacent property, and the
    teleological-flavor parameters. -/
structure ImperativeCharacter (W : Type*) where
  /-- The addressee (target of the directive). -/
  addressee : Nat
  /-- The prejacent: VP denotation. -/
  prejacent : W → Prop
  /-- Modal parameters: futurate circumstantial modal base + goal-based
      ordering source, packaged as a `TeleologicalFlavor`. -/
  flavor : TeleologicalFlavor W

/-- Necessity reading of the imperative character: the prejacent holds
    at every applicable circumstance (= every best world under the
    teleological flavor). Eq. (54)/(67) flattened to a world index. -/
def ImperativeCharacter.realize {W : Type*}
    (ic : ImperativeCharacter W) (w : W) : Prop :=
  ic.flavor.toKratzerParams.necessity ic.prejacent w

/-! ## §4 Conservativity Presupposition

Eq. (65), after [kaufmann-2012]: an imperative subject NP must
live on the addressee set. Stated as a property of the bundle. -/

/-- Conservativity presupposition: the subject's quantificational
    domain is a subset of the addressee set. -/
def ImperativeCharacter.conservativeOn {W : Type*}
    (_ic : ImperativeCharacter W) (domain addressees : List Nat) : Prop :=
  ∀ e ∈ domain, e ∈ addressees

/-! ## §3 Architectural commitments

Roberts's central architectural claim is that the deontic flavor of
imperatives is **pragmatic** — it lives in the preferential POSW
component (the addressee's goals/plans), not in the LF as a deontic
modal. This is precisely the [portner-2018] `Component`
assignment for `Illocutionary.imperative`, derived (not
restipulated) here. -/

/-- **Roberts's architectural commitment**, derived from
    [portner-2018]'s `HasTarget Illocutionary`
    instance: the imperative targets the preferential POSW
    component (= the addressee's preference structure), not the
    informational component (= CommonGround).

    This is the type-level shadow of "deontic force is pragmatic,
    not LF": deontic-style content lives where the preference
    component does, and the imperative refines that component
    (via `ExpState.promote` / `Scoreboard.directionUpdate`) rather
    than the informational one. -/
theorem imperative_targets_preferential :
    HasTarget.target Illocutionary.imperative = .preferential := rfl

/-- **Pragmatic-deontic routing** ([roberts-2023] §3, headline claim).

    Directing `p` to addressee `t` routes the deontic content through
    the **preferential** component of the projected POSW: every
    prejacent-violator `w` (`¬ p w`) is demoted relative to every
    prejacent-satisfier `v` (`p v`) in the preference order
    (`¬ (· ).toExpState.order.le w v`).

    The dual negative claim — that the **informational** component
    (CommonGround) is untouched — is `Scoreboard.direction_preserves_cg` (a
    `@[simp]` lemma). The two together discharge Roberts's claim
    that deontic content arises pragmatically via the preference
    structure rather than via assertion to common ground.

    The hypothesis `hin : t < K.goals.length` is the substrate
    counterpart of Roberts's conservativity presupposition (eq. (65)):
    the addressee must be a real participant for the directive to
    have its preferential effect. Composes
    `Scoreboard.direction_demotes_violators` (the substrate theorem
    that does the work) with the Component assignment
    `imperative_targets_preferential` (the architectural commitment
    that this preference-side change *is* the deontic content). -/
theorem pragmatic_deontic_routing
    {W : Type*} (K : Scoreboard W) (p : W → Prop) (s t pr : Nat)
    (hin : t < K.goals.length) {w v : W} (hpv : p v) (hpw : ¬ p w) :
    ¬ (K.directionUpdate p s t pr).toExpState.order.le w v :=
  Scoreboard.direction_demotes_violators K p s t pr hin w v hpv hpw

/-! ## §1 Desideratum (h): Futurate Flavor

Restated against `futureHistoryBase` (the canonical Condoravdi/CIR
substrate in `HistoricalAlternatives`) rather than a
local `FUT` enumeration. -/

/-- **(h) Futurate flavor** ([roberts-2023] Table 1, §1, exx.
    33–35). Every circumstance in the future-history base of
    ⟨w, t⟩ has a strictly later time than t. Direct consequence of
    `futureHistoryBase`'s definition. -/
theorem futurate {W T : Type*} [LT T]
    (history : HistoricalAlternatives W T)
    (s s' : WorldTimeIndex W T) (h : s' ∈ futureHistoryBase history s) :
    s.time < s'.time := h.2

/-! ## §2.2 Force Linking — integration tests

These are smoke tests that the `Illocutionary` infrastructure
agrees with Roberts's IFLP and her sincerity-condition triad.
Each `rfl` is a structural check that the `Scoreboard` enum
assignment matches the paper. -/

/-- The IFLP round-trips for all three core moods. -/
theorem iflp_roundtrip :
    forceLinkingPrinciple (defaultSemanticType .declarative) = .declarative ∧
    forceLinkingPrinciple (defaultSemanticType .interrogative) = .interrogative ∧
    forceLinkingPrinciple (defaultSemanticType .imperative) = .imperative :=
  ⟨rfl, rfl, rfl⟩

/-- Sincerity conditions: assertion expresses belief; interrogation
    and direction both express desire. -/
theorem sincerity_triad :
    sincerityCondition .declarative = .belief ∧
    sincerityCondition .interrogative = .desire ∧
    sincerityCondition .imperative = .desire := ⟨rfl, rfl, rfl⟩

/-- Direction-of-fit triad: assertion is mind-to-world, interrogation
    and direction are world-to-mind. -/
theorem direction_of_fit_triad :
    (sincerityCondition .declarative).directionOfFit = .mindToWorld ∧
    (sincerityCondition .interrogative).directionOfFit = .worldToMind ∧
    (sincerityCondition .imperative).directionOfFit = .worldToMind :=
  ⟨rfl, rfl, rfl⟩

/-! ## §5 Comparison with [kaufmann-2012] / [ruytenbeek-etal-2017]

Roberts's central disagreement with [kaufmann-2012]: the
imperative's **prejacent-internal** modal flavor is teleological
(circumstantial + goals), not deontic. [ruytenbeek-etal-2017]
adopt Kaufmann's position: their `SentType.imperative.modalFlavor =
some .deontic` (`RuytenbeekEtAl2017.lean` line 102) and their
`directiveCompatible` test fires only on `.deontic` flavor. This
is a *substantive* disagreement, not a naming dispute: the two
accounts make opposite predictions about whether circumstantial
declaratives ("Il est possible de VP" with goal-relevance) should
pattern with imperatives in directive force. -/

/-- The flavor Roberts assigns to the imperative's prejacent-internal
    modal: teleological/circumstantial. -/
def robertsImperativeFlavor : Semantics.Modality.ModalFlavor :=
  TeleologicalFlavor.flavorTag

/-- **Cross-paper disagreement** — [ruytenbeek-etal-2017] Study 2
    encodes the [kaufmann-2012] position by stipulating
    `SentType.imperative.modalFlavor = some .deontic`. Roberts's
    account predicts `.circumstantial`. The two prejacent-internal
    flavors are distinct. -/
theorem disagrees_with_ruytenbeek_imperative_flavor :
    some robertsImperativeFlavor ≠
    RuytenbeekEtAl2017.SentType.imperative.modalFlavor := by decide

/-- [kaufmann-2012]'s position is exposed in
    `Semantics/Mood/SpeechEvent.lean` as
    `primaryFlavor .imperative = .deontic`. Roberts disagrees.

    This subsumes a previous `roberts_fails_ruytenbeek_mechanism_one`
    theorem (deleted after Ruytenbeek's `directiveCompatible` wrapper
    was inlined): under Roberts, an imperative is directive *despite*
    not having deontic flavor in its prejacent — the directive force
    comes from the `ExpState.promote` update on the addressee's preference
    structure (see `pragmatic_deontic_routing`), not from the
    prejacent's flavor matching the imperative's. -/
theorem disagrees_with_assert :
    robertsImperativeFlavor ≠
    Mood.Illocutionary.primaryFlavor .imperative := by decide

/-- **Mechanism wedge** (post-2026-05-13: empirical wedge collapsed).
    `possibleDecl` ("Il est possible de VP") was previously the lone
    construction where Roberts and Ruytenbeek made *opposite predictions*
    about directive force: Roberts predicted directive (prejacent flavor
    matches imperative under teleological account), while
    `RuytenbeekEtAl2017.lean`'s mechanisms 1 and 2 alone did not fire on
    `possibleDecl`. The 2026-05-13 PDF re-audit found the paper's §4
    General Discussion (p. 61) explicitly groups all four
    ability/possibility constructions — including *Il est possible de
    VP* — as encoding force-dynamic enablement (Talmy 2000, Sweetser
    1990, Johnson 1987), and the corresponding Fig. 6 shows
    `possibleDecl` does receive directive interpretations. Ruytenbeek
    now formalises this as mechanism 3 (`enablementEncoded`), which
    fires on `possibleDecl`.

    The two accounts therefore *agree* on the prediction (`possibleDecl`
    is directive) but route through different mechanisms: Roberts via
    prejacent-flavor matching (teleological), Ruytenbeek via mechanism
    3 (force-dynamic enablement).

    The conjuncts below remain literally true and document the
    mechanism difference: under Ruytenbeek's *original two* mechanisms
    (1 = deontic match, 2 = preparatory-condition questioning) — the
    only ones the chronologically-prior [kaufmann-2012] and
    [clark-1979] sources support — `possibleDecl` would not be
    licensed. The substantive Roberts-vs-Ruytenbeek wedge has migrated
    to the imperative's prejacent flavor (see
    `disagrees_with_ruytenbeek_imperative_flavor` above). -/
theorem empirical_wedge_possible_declarative :
    RuytenbeekEtAl2017.SentType.possibleDecl.modalFlavor =
      some robertsImperativeFlavor ∧
    ¬ RuytenbeekEtAl2017.SentType.possibleDecl.deonticMatch ∧
    ¬ RuytenbeekEtAl2017.SentType.possibleDecl.prepConditionQueried :=
  ⟨rfl, by decide, by decide⟩

/-! ## Worked Examples

These instantiate `ImperativeCharacter` with the local 4-world toy
type `World := Fin 4` defined above. -/

/-- Example: "Move!" ([roberts-2023] (55), worked derivation).
    Trivial case — empty modal base and ordering, prejacent always
    holds. -/
def moveExample : ImperativeCharacter World where
  addressee := 0
  prejacent := λ _ => True
  flavor := ⟨emptyBackground, emptyBackground⟩

theorem move_trivial : ∀ w, moveExample.realize w := by
  intro w
  show necessity _ _ _ _
  rw [necessity_iff_all]
  intro _ _; trivial

/-- Example: "Nobody move!" ([roberts-2023] (42), attributed to
    [veltman-2018]). Negation is **internal** (predicate-term
    negation `¬MOVE`), not external (`¬□`) — propositional negation
    cannot scope over a property. -/
def nobodyMoveExample : ImperativeCharacter World where
  addressee := 0
  prejacent := λ _ => False
  flavor := ⟨emptyBackground, emptyBackground⟩

private theorem empty_best (w : World) :
    w ∈ bestWorlds (W := World) emptyBackground emptyBackground w := by
  have hAcc : w ∈ accessibleWorlds (emptyBackground (W := World)) w := by
    rw [empty_base_universal_access]; exact Set.mem_univ _
  exact ⟨hAcc, fun _ _ q hq _ => by simp [emptyBackground] at hq⟩

theorem nobody_move_total_prohibition :
    ∀ w, ¬ nobodyMoveExample.realize w := by
  intro w h
  have h' : necessity (W := World) emptyBackground emptyBackground (λ _ => False) w := h
  rw [necessity_iff_all] at h'
  exact h' w (empty_best w)

/-! ## §1 (38) Weak imperatives — suggestions and advice

Suggestions like "Hire an attorney" carry weaker modal force than
commands. The mood and semantic type are unchanged; the force
difference lives in the **ordering source**, where the prejacent
itself serves as a secondary ordering criterion (yielding weak
necessity in the sense of [von-fintel-iatridou-2008], which
linglib formalizes in `Semantics/Modality/Directive.lean`). -/

open Semantics.Modality.Directive in
/-- Weak (suggestion/advice) reading of an imperative character: weak
    necessity under the primary teleological ordering plus a
    secondary ordering favoring the prejacent. -/
def ImperativeCharacter.weakRealize {W : Type*}
    (ic : ImperativeCharacter W) (secondaryGoals : OrderingSource W)
    (w : W) : Prop :=
  weakNecessity ic.flavor.circumstances ic.flavor.goals secondaryGoals
    ic.prejacent w

open Semantics.Modality.Directive in
/-- Commands entail suggestions: strong necessity entails weak
    necessity (`Directive.strong_entails_weak`), so a command-strength
    imperative a fortiori realizes the suggestion. -/
theorem strong_imperative_entails_suggestion {W : Type*}
    (ic : ImperativeCharacter W) (secondaryGoals : OrderingSource W) (w : W)
    (h : ic.realize w) :
    ic.weakRealize secondaryGoals w :=
  strong_entails_weak ic.flavor.circumstances ic.flavor.goals secondaryGoals
    ic.prejacent w h

/-- Example: "Have a cookie." ([roberts-2023] §2.2, (60)).
    Invitation, not command — the hostess proposes the goal of
    eating a cookie; the guest may decline. Modeled as weak
    necessity over an empty primary ordering, with a secondary
    ordering favoring cookie-eating worlds. -/
def haveCookieExample : ImperativeCharacter World where
  addressee := 0
  prejacent := λ w => w = (0 : World)
  flavor := ⟨emptyBackground, emptyBackground⟩

theorem cookie_not_command :
    ¬ haveCookieExample.realize (1 : World) := by
  intro h
  have h' : necessity (W := World) emptyBackground emptyBackground
      (λ w => w = (0 : World)) (1 : World) := h
  rw [necessity_iff_all] at h'
  exact absurd (h' (1 : World) (empty_best (1 : World))) (by decide)

open Semantics.Modality.Directive in
theorem cookie_is_suggestion :
    haveCookieExample.weakRealize
      (λ _ => [λ w => w = (0 : World)]) (0 : World) := by
  show necessity _ _ _ _
  rw [necessity_iff_all]
  intro w hw
  by_contra hne
  rcases hw with ⟨_, hBest⟩
  have hw0Acc : (0 : World) ∈ accessibleWorlds (emptyBackground (W := World)) (0 : World) := by
    rw [empty_base_universal_access]; exact Set.mem_univ _
  have hgoal : (λ w' : World => w' = (0 : World)) (0 : World) := rfl
  have hweq : w = (0 : World) := hBest (0 : World) hw0Acc (λ w' : World => w' = (0 : World))
    (by simp [combineOrdering]) hgoal
  exact hne hweq

end Roberts2023
