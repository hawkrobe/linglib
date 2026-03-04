import Linglib.Theories.Syntax.Minimalism.Core.Basic

/-!
# Derivation Steps and Traces

Ordered derivation tracking for Minimalist syntax: the sequence of
Merge/Move operations that produces a `SyntacticObject` tree.

## Key definitions

- `SyntacticObject.replace` — substitute a subtree, used to leave traces
- `Step` — a single derivation step (External or Internal Merge)
- `Derivation` — an ordered list of steps applied to an initial SO
- `Derivation.final` — the tree produced by applying all steps
- `Derivation.stageAt` — intermediate tree after `n` steps
- `Derivation.movedItems` — which subtrees underwent Internal Merge
-/

namespace Minimalism

/-- Replace all occurrences of `target` in `so` with `replacement`.

    In well-formed derivations with unique `LIToken` IDs, each subtree
    appears exactly once, so this replaces at most one position. -/
def SyntacticObject.replace (so target replacement : SyntacticObject) : SyntacticObject :=
  match so with
  | .leaf _ => if so == target then replacement else so
  | .node l r =>
    if so == target then replacement
    else .node (l.replace target replacement) (r.replace target replacement)

/-- A single derivation step. -/
inductive Step where
  /-- External Merge: new item becomes left daughter. -/
  | emL (item : SyntacticObject)
  /-- External Merge: new item becomes right daughter. -/
  | emR (item : SyntacticObject)
  /-- Internal Merge: move `mover` to left edge, leaving a trace with `traceId`. -/
  | im (mover : SyntacticObject) (traceId : Nat)
  deriving Repr

/-- Apply a derivation step to the current tree.

    - `emL`: new item merges as left daughter (head/specifier above current)
    - `emR`: new item merges as right daughter (complement of current)
    - `im`: mover is extracted (replaced by trace) then re-merged at the left edge -/
def Step.apply (step : Step) (current : SyntacticObject) : SyntacticObject :=
  match step with
  | .emL item => .node item current
  | .emR item => .node current item
  | .im mover traceId =>
    let traced := current.replace mover (mkTrace traceId)
    .node mover traced

/-- An ordered derivation: an initial SO plus a sequence of steps. -/
structure Derivation where
  initial : SyntacticObject
  steps : List Step
  deriving Repr

/-- The final tree produced by applying all derivation steps. -/
def Derivation.final (d : Derivation) : SyntacticObject :=
  d.steps.foldl (λ so step => step.apply so) d.initial

/-- The intermediate tree after the first `n` steps. -/
def Derivation.stageAt (d : Derivation) (n : Nat) : SyntacticObject :=
  (d.steps.take n).foldl (λ so step => step.apply so) d.initial

/-- Number of derivation steps. -/
def Derivation.length (d : Derivation) : Nat := d.steps.length

/-- The subtrees that underwent Internal Merge (movement). -/
def Derivation.movedItems (d : Derivation) : List SyntacticObject :=
  d.steps.filterMap λ
    | .im mover _ => some mover
    | _ => none

-- ============================================================================
-- Verification theorems
-- ============================================================================

/-- Stage 0 is the initial tree (no steps applied). -/
theorem stageAt_zero (d : Derivation) : d.stageAt 0 = d.initial := by
  simp [Derivation.stageAt]

/-- Stage at full length equals the final tree. -/
theorem stageAt_length (d : Derivation) : d.stageAt d.steps.length = d.final := by
  simp [Derivation.stageAt, Derivation.final, List.take_length]

/-- Replacing `so` when it is the root returns the replacement. -/
theorem replace_self (so replacement : SyntacticObject) :
    so.replace so replacement = replacement := by
  cases so with
  | leaf _ => simp [SyntacticObject.replace]
  | node _ _ => simp [SyntacticObject.replace]

end Minimalism
