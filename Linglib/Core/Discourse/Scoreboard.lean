import Linglib.Core.Discourse.Goal
import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment
import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.PrecisionProjection
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Core.Mood.POSW
import Linglib.Core.Mood.POSWQ

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

/-- Replace the `target`-th goal set in `xs` (walking from index `i`)
    by adding `g`. Returns `xs` unchanged if `target` is out of range
    (no implicit list extension). Used by `directionUpdate` and reasoned
    about by `addGoalAt_out_of_range` and `mem_addGoalAt_flatMap`. -/
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

/-- **Direction update** (@cite{roberts-2023} (59)):
    If a targeted property is issued to addressee i and accepted,
    G_i is revised to include the realization of the property in any
    applicable circumstances. -/
def directionUpdate (K : Scoreboard W) (p : W → Prop)
    (speaker target : Nat) (priority : Nat := 0) : Scoreboard W :=
  let newGoal : Goal W := { content := p, priority }
  { K with
    goals := addGoalAt K.goals target 0 newGoal
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

The scoreboard's CG and G components project jointly into a
`Core.Mood.POSW` substrate (@cite{portner-2018}, eq. 1):

- The `cs` component is the scoreboard `contextSet` (∩ of CG).
- The `le` component is the **goal-induced preference ordering**:
  `w` is at least as good as `v` iff every active goal content (across
  every agent) that holds at `v` also holds at `w`. Equivalently,
  `w` violates no goal that `v` doesn't already violate.

This makes the two scoreboard updates that target the POSW substrate
correspond, by construction, to the two POSW updates of @cite{portner-2018}:

| scoreboard      | POSW    | informational consequence                  |
|-----------------|---------|--------------------------------------------|
| assertionUpdate | `plus`  | `boxCs_plus_self` (Stalnakerian principle) |
| directionUpdate | `star`  | `le`-refinement: p-violators demoted       |

We *derive* both consequences from `POSW.boxCs_plus_self` and the
`star`-refinement via the bridge theorems below — not re-stipulate them. -/

/-- The flat list of goal contents across all agents. The substrate of
    the goal-induced preference ordering on `toPOSW`. -/
def goalContents (K : Scoreboard W) : List (W → Prop) :=
  K.goals.flatMap GoalSet.toPropertyList

@[simp] theorem goalContents_def (K : Scoreboard W) :
    K.goalContents = K.goals.flatMap GoalSet.toPropertyList := rfl

/-- Assertion update preserves goal contents (since it doesn't touch G). -/
@[simp] theorem assertion_preserves_goalContents (K : Scoreboard W)
    (p : W → Prop) (a : Nat) :
    (K.assertionUpdate p a).goalContents = K.goalContents := rfl

/-- Membership in the flat goal-content list of a `directionUpdate`-modified
    scoreboard: the directive's content is added; everything else is preserved.
    Requires the target to be in bounds. -/
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

/-- Project the scoreboard into a POSW substrate. `cs` is the
    scoreboard's `contextSet`; `le` is the **goal-induced** ordering —
    `w` is at least as good as `v` iff `w` satisfies every goal
    `v` satisfies. The two POSW updates of @cite{portner-2018} target
    these two components (cf. `toPOSW_assertion_eq_plus` and
    `toPOSW_direction_eq_star`). -/
def toPOSW (K : Scoreboard W) : Core.Mood.POSW W where
  cs := K.contextSet
  le := fun w v => ∀ p ∈ K.goalContents, p v → p w
  le_refl  := fun _ _ _ _ hp => hp
  le_trans := fun _ _ _ _ _ _ hwu huv p hp hpv => hwu p hp (huv p hp hpv)

@[simp] theorem toPOSW_cs (K : Scoreboard W) :
    K.toPOSW.cs = K.contextSet := rfl

@[simp] theorem toPOSW_le (K : Scoreboard W) (w v : W) :
    K.toPOSW.le w v ↔ ∀ p ∈ K.goalContents, p v → p w := Iff.rfl

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

/-- **Direction-as-`⋆`-update bridge** (@cite{portner-2018} eq. 2b,
    following @cite{portner-2004}). Issuing the directive `p` to a
    target in bounds refines the projected POSW exactly the way
    `POSW.star` does: the new ordering keeps the old ordering and
    additionally requires that whenever the dominated world satisfies
    `p`, the dominating world does too. The bridge mirrors the
    assertion bridge — `directionUpdate` is `⋆`-update on the `le`
    side, modulo the `t < K.goals.length` precondition (out-of-range
    targets silently drop the directive; that's a stipulated property
    of `directionUpdate`, not of POSW). -/
theorem toPOSW_direction_eq_star (K : Scoreboard W) (p : W → Prop)
    (s t pr : Nat) (hin : t < K.goals.length) (w v : W) :
    (K.directionUpdate p s t pr).toPOSW.le w v ↔ (K.toPOSW.star p).le w v := by
  simp only [toPOSW_le, Core.Mood.POSW.star_le]
  constructor
  · intro h
    refine ⟨fun q hq => h q ?_, h p ?_⟩
    · exact (mem_directionUpdate_goalContents K p s t pr hin q).mpr (Or.inr hq)
    · exact (mem_directionUpdate_goalContents K p s t pr hin p).mpr (Or.inl rfl)
  · rintro ⟨h1, h2⟩ q hq
    rcases (mem_directionUpdate_goalContents K p s t pr hin q).mp hq with rfl | hq'
    · exact h2
    · exact h1 q hq'

/-- **Goal-violator demotion** (corollary of the `⋆`-bridge):
    after directing `p`, no `p`-violator can dominate a `p`-satisfier
    in the goal-induced ordering. The directive update genuinely
    refines the preference relation — the analogue, on the `le` side,
    of `boxCs_after_assertion` on the `cs` side. -/
theorem direction_demotes_violators (K : Scoreboard W) (p : W → Prop)
    (s t pr : Nat) (hin : t < K.goals.length) (w v : W)
    (hpv : p v) (hpw : ¬ p w) :
    ¬ (K.directionUpdate p s t pr).toPOSW.le w v := by
  intro hlt
  have hstar : (K.toPOSW.star p).le w v :=
    (toPOSW_direction_eq_star K p s t pr hin w v).mp hlt
  exact hpw (hstar.2 hpv)

/-! ## POSWQ Substrate Bridge

The scoreboard's QUD component projects into the third POSW component
of @cite{portner-2018} — the **inquiry partition** of `Core.Mood.POSWQ`.
Each yes/no question `q : W → Prop` on the QUD stack induces a binary
partition (`q`-true worlds vs. `q`-false worlds); the joint inquiry
is the meet of these binary partitions in the `Setoid W` lattice.

| scoreboard          | POSWQ               | informational consequence    |
|---------------------|---------------------|------------------------------|
| assertionUpdate     | `plus`              | `boxCs_plus_self`            |
| directionUpdate     | `star`              | `le`-refinement              |
| interrogationUpdate | `inquire` (`?`)     | `boxAns`-strengthening       |

Together these three bridges complete the @cite{portner-2018} 3×3
unification on the discourse-update side. -/

/-- The inquiry partition projected from the QUD stack: the meet of
    the polar Setoids of every question on the stack, with the trivial
    inquiry (`⊤`) as identity. The fold convention places the new
    head's polar Setoid on the *right* of `⊓` so that consing reduces
    definitionally to the `inquire` update on `POSWQ`.
    `polarSetoid` lives in `Core/Mood/POSWQ.lean` (the natural
    primitive site — it is the partition substrate). -/
def qudInquiry (K : Scoreboard W) : Setoid W :=
  K.qud.foldr (fun q s => s ⊓ Core.Mood.POSWQ.polarSetoid q) ⊤

@[simp] theorem qudInquiry_nil (K : Scoreboard W) (h : K.qud = []) :
    K.qudInquiry = (⊤ : Setoid W) := by
  simp [qudInquiry, h]

@[simp] theorem qudInquiry_cons (K : Scoreboard W) (q : W → Prop)
    (rest : List (W → Prop)) (h : K.qud = q :: rest) :
    K.qudInquiry =
      (rest.foldr (fun q s => s ⊓ Core.Mood.POSWQ.polarSetoid q) ⊤) ⊓
        Core.Mood.POSWQ.polarSetoid q := by
  simp [qudInquiry, h]

/-- Interrogation update preserves goal contents (since it doesn't
    touch G). Needed for the POSWQ bridge — `toPOSWQ` projects both
    `le` (from `goalContents`) and `inquiry` (from `qud`), and the
    interrogation update only refines the latter. -/
@[simp] theorem interrogation_preserves_goalContents (K : Scoreboard W)
    (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).goalContents = K.goalContents := rfl

/-- Project the scoreboard into a POSWQ substrate: the underlying POSW
    plus the QUD-induced inquiry partition. The third row of the
    @cite{portner-2018} unification table. -/
def toPOSWQ (K : Scoreboard W) : Core.Mood.POSWQ W :=
  { K.toPOSW with inquiry := K.qudInquiry }

@[simp] theorem toPOSWQ_toPOSW (K : Scoreboard W) :
    K.toPOSWQ.toPOSW = K.toPOSW := rfl

@[simp] theorem toPOSWQ_inquiry (K : Scoreboard W) :
    K.toPOSWQ.inquiry = K.qudInquiry := rfl

/-- **Interrogation-as-`?`-update bridge** (@cite{portner-2018} on
    questions; @cite{groenendijk-stokhof-1984} partitions). Posing a
    question `q` against scoreboard `K` refines the projected POSWQ
    exactly the way `POSWQ.inquire` does on the polar Setoid of `q`:
    the new inquiry partition is the meet of the old inquiry with
    the polar partition of `q`. The bridge is definitional —
    `interrogationUpdate` is `?`-update on the `inquiry` side. -/
theorem toPOSWQ_interrogation_eq_inquire (K : Scoreboard W)
    (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).toPOSWQ.inquiry =
      (K.toPOSWQ.inquire (Core.Mood.POSWQ.polarSetoid q)).inquiry := rfl

/-- **Question-strengthening principle** (the inquiry analogue of
    `boxCs_after_assertion` and `direction_demotes_violators`):
    after posing `q`, every proposition that is settled by `q`
    *and* compatible with the prior inquiry is settled by the new
    POSWQ. Concretely, the polar partition of `q` itself is settled.
    Derived from `POSWQ.boxAns` over the meet — not re-stipulated. -/
theorem boxAns_polar_after_interrogation (K : Scoreboard W)
    (q : W → Prop) (a : Nat) :
    (K.interrogationUpdate q a).toPOSWQ.boxAns q := by
  intro w v _ _ hwv
  -- (K.interrogationUpdate q a).toPOSWQ.inquiry = K.qudInquiry ⊓ polarSetoid q
  -- meet's right component is exactly polarSetoid q, hence q w ↔ q v
  exact hwv.2

end Scoreboard
end Core.Discourse
