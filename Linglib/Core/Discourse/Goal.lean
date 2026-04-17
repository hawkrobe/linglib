import Linglib.Core.Semantics.Proposition

/-!
# Discourse Goals and Plans
@cite{bratman-1987} @cite{portner-2004} @cite{roberts-2023}

The interlocutors' publicly evident goals, plans, and priorities — the **G**
component of @cite{roberts-2023}'s scoreboard K = ⟨I, M, ≺, CG, QUD, G⟩.

@cite{bratman-1987}: intentions are commitments to action, organized
hierarchically into plans. Goals subserve other goals, and an agent's
priorities induce a partial order over them.

@cite{portner-2004}'s ToDo list is a special case: an unstructured set of
properties the addressee is committed to realizing. The present formalization
follows @cite{roberts-2023} in giving G richer internal structure — conditional
goals with priority ordering — while remaining compatible with Portner's
interface (a `GoalSet` projects to a flat property list).

## Key Design Choices

1. Goals are **conditional**: realized only when applicable circumstances
   obtain (@cite{roberts-2023} §2.1.1). We represent the condition as a
   proposition (the modal base propositions that must hold).
2. Goals carry **priority**: a natural number where lower = higher priority.
   @cite{roberts-2023}: "i's priorities are reflected in additional structure
   over G_i."
3. Goal sets are **per-agent**: G = {G_i | i ∈ I}, one set per interlocutor.
-/

namespace Core.Discourse

open Core.Proposition (BProp)

variable {W : Type*}

/-- A single goal: a proposition the agent is committed to realizing,
    conditional on certain circumstances obtaining.

    @cite{roberts-2023} §2.1.1: "for all g ∈ G_i, g is a conditional goal,
    its presence in G_i representing i's intention to achieve the goal
    should certain conditions obtain in the actual world at some future
    time t' > t." -/
structure Goal (W : Type*) where
  /-- The content: what the agent aims to bring about -/
  content : BProp W
  /-- The condition: circumstances under which this goal is active.
      `λ _ => true` for unconditional goals. -/
  condition : BProp W := λ _ => true
  /-- Priority level: 0 = highest priority. @cite{roberts-2023}: goals are
      hierarchically organized to reflect plans and priorities. -/
  priority : Nat := 0
  deriving Inhabited

/-- An agent's goal set: the publicly evident goals, plans, and priorities.

    @cite{roberts-2023} §2.1.1: "G_i is the set of i's evident goals,
    including those which i is publicly committed at t to trying to realize."
    Goals are organized to reflect plans and priorities. -/
structure GoalSet (W : Type*) where
  /-- The goals, ordered by priority (lower index = mentioned earlier,
      not necessarily higher priority — use `Goal.priority` for ranking). -/
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

/-- Add an unconditional goal with given priority. -/
def addSimple (gs : GoalSet W) (content : BProp W) (priority : Nat := 0) : GoalSet W :=
  gs.add { content, priority }

/-- Remove goals whose content matches a predicate (e.g., realized or abandoned). -/
def remove (gs : GoalSet W) (shouldRemove : Goal W → Bool) : GoalSet W :=
  ⟨gs.goals.filter (λ g => !shouldRemove g)⟩

@[simp] theorem remove_goals (gs : GoalSet W) (f : Goal W → Bool) :
    (gs.remove f).goals = gs.goals.filter (fun g => !f g) := rfl

/-- Goals active in circumstance w (condition satisfied). -/
def activeGoals (gs : GoalSet W) (w : W) : List (Goal W) :=
  gs.goals.filter (λ g => g.condition w)

@[simp] theorem activeGoals_empty (w : W) :
    (empty : GoalSet W).activeGoals w = [] := rfl

theorem mem_activeGoals_iff (gs : GoalSet W) (w : W) (g : Goal W) :
    g ∈ gs.activeGoals w ↔ g ∈ gs.goals ∧ g.condition w = true := by
  simp only [activeGoals, List.mem_filter]

/-- Active goal contents at w, sorted by priority (ascending = most important first). -/
def activeContents (gs : GoalSet W) (w : W) : List (BProp W) :=
  (gs.activeGoals w |>.mergeSort (λ g₁ g₂ => g₁.priority ≤ g₂.priority))
    |>.map Goal.content

/-- Project to a flat list of contents (@cite{portner-2004} ToDo list interface). -/
def toPropertyList (gs : GoalSet W) : List (BProp W) :=
  gs.goals.map Goal.content

@[simp] theorem toPropertyList_empty :
    (empty : GoalSet W).toPropertyList = [] := rfl

@[simp] theorem toPropertyList_add (gs : GoalSet W) (g : Goal W) :
    (gs.add g).toPropertyList = g.content :: gs.toPropertyList := rfl

/-- Whether the goal set is empty. -/
def isEmpty (gs : GoalSet W) : Bool :=
  gs.goals.isEmpty

@[simp] theorem empty_isEmpty : (empty : GoalSet W).isEmpty = true := rfl

theorem isEmpty_iff (gs : GoalSet W) : gs.isEmpty = true ↔ gs.goals = [] := by
  simp only [isEmpty, List.isEmpty_iff]

/-- Number of goals. -/
def size (gs : GoalSet W) : Nat :=
  gs.goals.length

@[simp] theorem size_eq (gs : GoalSet W) : gs.size = gs.goals.length := rfl

@[simp] theorem empty_size : (empty : GoalSet W).size = 0 := rfl

@[simp] theorem add_size (gs : GoalSet W) (g : Goal W) :
    (gs.add g).size = gs.size + 1 := rfl

end GoalSet

end Core.Discourse
