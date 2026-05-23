import Linglib.Syntax.Minimalist.Basic

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

namespace Minimalist

/-- Replace all occurrences of `target` in `so` with `replacement`.

    In well-formed derivations with unique `LIToken` IDs, each subtree
    appears exactly once, so this replaces at most one position.

    Defined via `FreeCommMagma.lift` over a swap-respecting helper on
    the underlying `FreeMagma`. The swap-respect proof exploits the new
    `FreeCommMagma.swap`/`mul_comm` API: equality of the `if` conditions
    follows from `swap`; equality of the recursive `else` branches
    follows from `mul_comm` on the quotient. -/
private def replaceAux (target replacement : SyntacticObject) :
    FreeMagma (LIToken ⊕ Nat) → SyntacticObject
  | a@(.of _) =>
    if (FreeCommMagma.mk a : SyntacticObject) = target then replacement
    else FreeCommMagma.mk a
  | .mul l r =>
    if (FreeCommMagma.mk (l * r) : SyntacticObject) = target then replacement
    else replaceAux target replacement l * replaceAux target replacement r

private theorem replaceAux_respects (target replacement : SyntacticObject)
    (a b : FreeMagma (LIToken ⊕ Nat)) (h : FreeMagma.CommRel a b) :
    replaceAux target replacement a = replaceAux target replacement b := by
  induction h with
  | swap a b =>
    show (if (FreeCommMagma.mk (a * b) : SyntacticObject) = target then replacement
            else replaceAux target replacement a * replaceAux target replacement b)
       = (if (FreeCommMagma.mk (b * a) : SyntacticObject) = target then replacement
            else replaceAux target replacement b * replaceAux target replacement a)
    rw [FreeCommMagma.swap a b]
    split
    · rfl
    · exact mul_comm _ _
  | @mul_left a b h_inner c ih =>
    show (if (FreeCommMagma.mk (a * c) : SyntacticObject) = target then replacement
            else replaceAux target replacement a * replaceAux target replacement c)
       = (if (FreeCommMagma.mk (b * c) : SyntacticObject) = target then replacement
            else replaceAux target replacement b * replaceAux target replacement c)
    rw [FreeCommMagma.sound (.mul_left h_inner _), ih]
  | @mul_right a b c h_inner ih =>
    show (if (FreeCommMagma.mk (a * b) : SyntacticObject) = target then replacement
            else replaceAux target replacement a * replaceAux target replacement b)
       = (if (FreeCommMagma.mk (a * c) : SyntacticObject) = target then replacement
            else replaceAux target replacement a * replaceAux target replacement c)
    rw [FreeCommMagma.sound (.mul_right _ h_inner), ih]

def SyntacticObject.replace (so target replacement : SyntacticObject) : SyntacticObject :=
  FreeCommMagma.lift (replaceAux target replacement)
    (replaceAux_respects target replacement) so

@[simp] theorem SyntacticObject.replace_leaf (tok : LIToken) (target rep : SyntacticObject) :
    (SyntacticObject.leaf tok).replace target rep
      = if (SyntacticObject.leaf tok) = target then rep else SyntacticObject.leaf tok := rfl

@[simp] theorem SyntacticObject.replace_trace (n : Nat) (target rep : SyntacticObject) :
    (SyntacticObject.trace n).replace target rep
      = if (SyntacticObject.trace n) = target then rep else SyntacticObject.trace n := rfl

@[simp] theorem SyntacticObject.replace_mul (l r target rep : SyntacticObject) :
    (l * r).replace target rep
      = if (l * r) = target then rep else l.replace target rep * r.replace target rep := by
  induction l, r using FreeCommMagma.inductionOn₂ with | _ a b => rfl

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
    - `im`: mover is extracted (replaced by trace) then re-merged at the left edge

    Since `*` is commutative on `SyntacticObject` (the carrier is the
    free commutative magma), `emL` and `emR` produce the same SO; the
    distinction matters only for the planar projection at PF (which
    happens via `linearize` / `phonYield`, downstream of derivation). -/
def Step.apply (step : Step) (current : SyntacticObject) : SyntacticObject :=
  match step with
  | .emL item => item * current
  | .emR item => current * item
  | .im mover traceId =>
    let traced := current.replace mover (mkTrace traceId)
    mover * traced

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
  induction so with
  | leaf _ => simp only [SyntacticObject.replace_leaf, if_true]
  | trace _ => simp only [SyntacticObject.replace_trace, if_true]
  | mul l r _ _ => simp only [SyntacticObject.replace_mul, if_true]

end Minimalist
