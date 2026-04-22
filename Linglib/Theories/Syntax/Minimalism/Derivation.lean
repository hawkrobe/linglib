import Linglib.Theories.Syntax.Minimalism.Basic

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
  | .leaf _ => if decide (so = target) then replacement else so
  | .node l r =>
    if decide (so = target) then replacement
    else .node (l.replace target replacement) (r.replace target replacement)

/-- A single derivation step. -/
inductive Step where
  /-- External Merge: new item becomes left daughter. -/
  | emL (item : SyntacticObject)
  /-- External Merge: new item becomes right daughter. -/
  | emR (item : SyntacticObject)
  /-- Internal Merge: move `mover` to left edge, leaving a trace with `traceId`. -/
  | im (mover : SyntacticObject) (traceId : Nat)
  /-- Wholesale Late Merger: countercyclically merge `restrictor` (the NP
      complement of a determiner) into the bare determiner `target` at a
      chain position. The bare D is replaced by `{D, restrictor}`.
      @cite{takahashi-hulsey-2009} @cite{lebeaux-1988} -/
  | wlm (restrictor : SyntacticObject) (target : SyntacticObject)
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
  | .wlm restrictor target =>
    -- Replace bare D with {D, NP-restrictor} at the merger site
    current.replace target (.node target restrictor)

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

/-- The restrictor–target pairs from Wholesale Late Merger steps. -/
def Derivation.wlmOperations (d : Derivation) : List (SyntacticObject × SyntacticObject) :=
  d.steps.filterMap λ
    | .wlm restrictor target => some (restrictor, target)
    | _ => none

/-- Whether a derivation uses Wholesale Late Merger. -/
def Derivation.usesWLM (d : Derivation) : Bool :=
  d.steps.any λ
    | .wlm _ _ => true
    | _ => false

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
  match so with
  | .leaf _ => simp [SyntacticObject.replace]
  | .node _ _ => simp [SyntacticObject.replace]

/-- WLM at the root: if the target is the entire current tree,
    the result is `{target, restrictor}`. -/
theorem wlm_at_root (restrictor target : SyntacticObject) :
    (Step.wlm restrictor target).apply target = .node target restrictor := by
  simp [Step.apply, replace_self]

/-- WLM is non-destructive: the target subtree is preserved (as left
    daughter of the new node). -/
theorem wlm_preserves_target (restrictor target current : SyntacticObject) :
    let result := (Step.wlm restrictor target).apply current
    containsB current target = true →
    containsB result (.node target restrictor) = true := by
  intro result h
  sorry -- structural induction on `current`; follows from `replace` behavior

end Minimalism
