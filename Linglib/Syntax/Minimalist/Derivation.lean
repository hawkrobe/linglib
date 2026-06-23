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

/-! ## Derivation-grounded externalization (computable PF order)
[marcolli-chomsky-berwick-2025]

A `SyntacticObject` is unordered (`FreeCommMagma`), so the surface left-to-right
order is *not* recoverable from `Derivation.final` alone. But a `Derivation`
*records* the planarization choices: `emL`/`im` place material on the LEFT edge,
`emR` on the right. This is exactly MCB's externalization section `σ_L`
(§1.12), here determined by the derivation ("the language `L`") instead of by a
noncanonical `Quot.out`. The fold below replays the steps on an **ordered**
`FreeMagma` accumulator, giving a fully **computable** PF — no `Quot.out`, so
surface orders are `decide`/`#eval`-checkable.

Merged items and the initial seed are leaves/traces in canonical derivations;
complex merged items return `none` (flagged) in this version. Movers may be
phrasal: `im` locates the *ordered* subtree of the accumulator that projects to
the (unordered) mover and moves it left, mirroring `Step.apply`'s
`replace`. -/

/-- Planar form of a leaf/trace SO (the only items merged in canonical
    derivations). `none` for a complex SO (no recorded internal order). -/
def SyntacticObject.toPlanarLeaf? (so : SyntacticObject) :
    Option (FreeMagma (LIToken ⊕ Nat)) :=
  match so.getLIToken, isTrace so with
  | some tok, _ => some (.of (.inl tok))
  | _, some n => some (.of (.inr n))
  | _, _ => none

/-- Replace every ordered subtree of `t` that projects to `target` with `rep`.
    The planar mirror of `SyntacticObject.replace` (matches by SO-equality of
    the projection `FreeCommMagma.mk`). -/
def planarReplaceSO (target : SyntacticObject) (rep : FreeMagma (LIToken ⊕ Nat)) :
    FreeMagma (LIToken ⊕ Nat) → FreeMagma (LIToken ⊕ Nat)
  | a@(.of _) => if (FreeCommMagma.mk a : SyntacticObject) = target then rep else a
  | a@(.mul l r) =>
      if (FreeCommMagma.mk a : SyntacticObject) = target then rep
      else .mul (planarReplaceSO target rep l) (planarReplaceSO target rep r)

/-- Find the (leftmost) ordered subtree of `t` projecting to `target`. -/
def findOrderedSubtree? (target : SyntacticObject) :
    FreeMagma (LIToken ⊕ Nat) → Option (FreeMagma (LIToken ⊕ Nat))
  | a@(.of _) => if (FreeCommMagma.mk a : SyntacticObject) = target then some a else none
  | a@(.mul l r) =>
      if (FreeCommMagma.mk a : SyntacticObject) = target then some a
      else (findOrderedSubtree? target l).or (findOrderedSubtree? target r)

/-- Internal Merge on the ordered accumulator: raise the ordered subtree
    projecting to `mover` to the LEFT edge, leaving a trace. Mirrors
    `Step.apply (.im mover tid)`. `none` if `mover` isn't found. -/
def moveLeftPlanar (acc : FreeMagma (LIToken ⊕ Nat)) (mover : SyntacticObject)
    (tid : Nat) : Option (FreeMagma (LIToken ⊕ Nat)) :=
  (findOrderedSubtree? mover acc).map fun s =>
    .mul s (planarReplaceSO mover (.of (.inr tid)) acc)

/-- The derivation's ordered planar representative (MCB `σ_L` for this
    derivation), or `none` if a merged item is complex / a mover is missing. -/
def Derivation.externalizeP? (d : Derivation) :
    Option (FreeMagma (LIToken ⊕ Nat)) :=
  (d.initial.toPlanarLeaf?).bind fun init =>
    d.steps.foldl (fun acc? step => acc?.bind fun acc =>
      match step with
      | .emL item => (item.toPlanarLeaf?).map (fun p => .mul p acc)
      | .emR item => (item.toPlanarLeaf?).map (fun p => .mul acc p)
      | .im mover tid => moveLeftPlanar acc mover tid) (some init)

/-- Surface (pronounced) tokens of a derivation, left-to-right. Traces are
    dropped (`linearizePlanar` skips `Sum.inr`). Empty if externalization
    fails. -/
def Derivation.surfaceTokens (d : Derivation) : List LIToken :=
  (d.externalizeP?.map linearizePlanar).getD []

/-- Surface category sequence — the readout used by word-order studies
    (e.g. Cinque's Dem/Num/A/N orders). -/
def Derivation.surfaceCats (d : Derivation) : List Cat :=
  d.surfaceTokens.map (·.item.outerCat)

/-! ### Faithfulness (Π bridge) and verification

**Faithfulness:** whenever `externalizeP?` succeeds, its ordered representative
projects back to the unordered `Derivation.final` — `externalizeP?` is a genuine
planar representative of the narrow-syntax output, not an independent
re-derivation. Stated concretely below by `decide`; the general theorem
`∀ fm, d.externalizeP? = some fm → (FreeCommMagma.mk fm) = d.final` is provable
by induction on `d.steps` via `mk (planarReplaceSO t rep a) = (mk a).replace t
(mk rep)` plus the leaf/trace projection lemmas (deferred).

The checks below also pin the substantive content: phrasal **pied-piping
preserves the moved constituent's internal order**, so deriving Dem-N-A-Num
(raise N around A, then pied-pipe `[N A]` around Num) is distinct from
Dem-A-N-Num (pied-pipe `[A N]` around Num) — the [cinque-2005] o-vs-n contrast.
(`.D` stands in for the demonstrative pending a `Cat.Dem` constructor.) -/

private def vN : SyntacticObject := mkLeaf .N [] 1
private def vA : SyntacticObject := mkLeaf .A [] 2
private def vNum : SyntacticObject := mkLeaf .Num [] 3
private def vD : SyntacticObject := mkLeaf .D [] 4

/-- No movement: `Dem Num A N`. -/
private def derivBase : Derivation :=
  { initial := vN, steps := [.emL vA, .emL vNum, .emL vD] }
/-- Raise N around A, pied-pipe `[N A]` around Num: `Dem N A Num`. -/
private def derivO : Derivation :=
  { initial := vN
    steps := [.emL vA, .im vN 10, .emL vNum, .im (vN * (vA * mkTrace 10)) 11, .emL vD] }
/-- Pied-pipe `[A N]` around Num, no sub-raise: `Dem A N Num`. -/
private def derivN : Derivation :=
  { initial := vN, steps := [.emL vA, .emL vNum, .im (vA * vN) 11, .emL vD] }

example : derivBase.surfaceCats = [.D, .Num, .A, .N] := by decide
example : derivO.surfaceCats = [.D, .N, .A, .Num] := by decide
example : derivN.surfaceCats = [.D, .A, .N, .Num] := by decide
/-- Pied-piping preserves internal order: o and n diverge. -/
example : derivO.surfaceCats ≠ derivN.surfaceCats := by decide
/-- Concrete Π bridge: externalization projects to `final`. -/
example :
    derivO.externalizeP?.map (FreeCommMagma.mk (α := LIToken ⊕ Nat)) = some derivO.final := by
  decide

end Minimalist
