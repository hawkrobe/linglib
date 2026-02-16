/-
# Workspace and Numeration

Formalization of the derivational workspace following Chomsky (1995, 2000)
and Adger (2003) Chapter 3.

## Key Concepts

- **Numeration**: A multiset of lexical items selected for a derivation
- **Workspace**: The current state of the derivation (active syntactic objects)
- **Select**: Operation that moves an LI from numeration to workspace
- **Merge**: Combines elements in the workspace

## The Derivational Model

1. Start with a Numeration N = {LI₁^n₁, LI₂^n₂, ...}
2. Select items from N into the Workspace W
3. Apply Merge to combine items in W
4. Continue until N is exhausted and W contains a single SO

## References

- Chomsky, N. (1995). The Minimalist Program.
- Chomsky, N. (2000). Minimalist Inquiries.
- Adger, D. (2003). Core Syntax, Chapter 3.
- Collins, C. & E. Stabler (2016). A Formalization of Minimalist Syntax.
-/

import Linglib.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Agree

namespace Minimalism

-- Part 1: Numeration

/-- A numeration entry: a lexical item with a count (how many times it can be used)

    The count allows the same LI to appear multiple times in a derivation.
    E.g., "John said John left" uses 'John' twice. -/
structure NumerationEntry where
  item : ExtendedLI
  count : Nat
  countPos : count > 0
  deriving Repr

/-- A numeration is a collection of LIs available for the derivation -/
structure Numeration where
  entries : List NumerationEntry
  deriving Repr

/-- Empty numeration -/
def Numeration.empty : Numeration := ⟨[]⟩

/-- Add an LI to the numeration -/
def Numeration.add (n : Numeration) (li : ExtendedLI) (count : Nat) (h : count > 0) : Numeration :=
  ⟨⟨li, count, h⟩ :: n.entries⟩

/-- Check if numeration is exhausted (all counts = 0) -/
def Numeration.exhausted (n : Numeration) : Bool :=
  n.entries.all (·.count == 0)

/-- Check if numeration contains a given LI -/
def Numeration.contains (n : Numeration) (li : ExtendedLI) : Bool :=
  n.entries.any (λ e => e.item.base == li.base && e.count > 0)

/-- Total items remaining in numeration -/
def Numeration.totalCount (n : Numeration) : Nat :=
  n.entries.foldl (λ acc e => acc + e.count) 0

-- Part 2: Workspace

/-- The workspace contains the active syntactic objects being combined

    At any point in a derivation, the workspace contains:
    - SOs that have been built so far
    - LIs that have been selected but not yet merged -/
structure Workspace where
  objects : List SyntacticObject
  nextId : Nat  -- Counter for generating unique token IDs
  deriving Repr

/-- Empty workspace -/
def Workspace.empty : Workspace := ⟨[], 0⟩

/-- Number of objects in workspace -/
def Workspace.size (w : Workspace) : Nat := w.objects.length

/-- Check if workspace contains a single object (derivation complete condition) -/
def Workspace.isSingleton (w : Workspace) : Bool := w.objects.length == 1

/-- Get the result if workspace is singleton -/
def Workspace.getResult (w : Workspace) : Option SyntacticObject :=
  match w.objects with
  | [so] => some so
  | _ => none

-- Part 3: Select Operation

/-- Result of a select operation -/
structure SelectResult where
  numeration : Numeration
  workspace : Workspace
  selected : SyntacticObject

/-- Select: Move an LI from numeration to workspace

    This operation:
    1. Finds the LI in the numeration
    2. Decrements its count
    3. Creates a token and adds it to the workspace -/
def select (n : Numeration) (w : Workspace) (li : ExtendedLI) : Option SelectResult :=
  -- Find and decrement the entry
  let rec findAndDecrement (entries : List NumerationEntry) (acc : List NumerationEntry) :
      Option (List NumerationEntry) :=
    match entries with
    | [] => none
    | e :: rest =>
      if e.item.base == li.base && e.count > 0 then
        let newEntry := match e.count with
          | 0 => none  -- Should not happen due to e.count > 0 check
          | 1 => none  -- Last use, remove entry
          | n + 2 => some ⟨e.item, n + 1, by omega⟩  -- n + 2 > 1, so n + 1 > 0
        let newEntries := match newEntry with
          | some e' => acc.reverse ++ [e'] ++ rest
          | none => acc.reverse ++ rest
        some newEntries
      else
        findAndDecrement rest (e :: acc)

  match findAndDecrement n.entries [] with
  | none => none
  | some newEntries =>
    let token : LIToken := ⟨li.base, w.nextId⟩
    let so := SyntacticObject.leaf token
    some {
      numeration := ⟨newEntries⟩
      workspace := ⟨so :: w.objects, w.nextId + 1⟩
      selected := so
    }

-- Part 4: Merge Triggers

/-- What triggers Merge? In Minimalism, uninterpretable features drive operations -/
inductive MergeTrigger where
  | selection : Cat → MergeTrigger     -- Selectional feature [uF] on head
  | epp : MergeTrigger                  -- EPP triggers specifier
  | theta : MergeTrigger                -- Theta-role assignment
  deriving Repr, DecidableEq

/-- Check if an LI needs to merge (has unsatisfied selectional features) -/
def needsMerge (li : ExtendedLI) : Bool :=
  !li.base.outerSel.isEmpty

/-- Get the category that an LI selects (if any) -/
def getSelectionalTarget (li : ExtendedLI) : Option Cat :=
  li.base.outerSel.head?

-- Part 5: External Merge Operation

/-- External Merge: combine two separate SOs from the workspace

    This is feature-driven: we merge when there's a selectional relationship -/
structure ExternalMergeOp where
  selector : SyntacticObject
  selected : SyntacticObject
  trigger : MergeTrigger
  deriving Repr

/-- Apply external merge to the workspace -/
def applyExternalMerge (w : Workspace) (op : ExternalMergeOp) : Option Workspace :=
  -- Remove both objects from workspace
  let objects' := w.objects.filter (· != op.selector)
  let objects'' := objects'.filter (· != op.selected)
  -- Check both were present
  if objects'.length != w.objects.length - 1 then none
  else if objects''.length != objects'.length - 1 then none
  else
    -- Create merged object
    let merged := merge op.selector op.selected
    some ⟨merged :: objects'', w.nextId⟩

/-- Check if external merge is valid (selector selects the selected) -/
def validExternalMerge (op : ExternalMergeOp) : Bool :=
  selectsB op.selector op.selected

-- Part 6: Internal Merge Operation

/-- Internal Merge: re-merge an SO already in the structure (movement)

    This handles cases where an element moves to a new position -/
structure InternalMergeOp where
  target : SyntacticObject    -- The structure being extended
  mover : SyntacticObject     -- The element being re-merged (must be in target)
  trigger : MergeTrigger
  deriving Repr

/-- Check if mover is contained in target -/
def moverInTarget (op : InternalMergeOp) : Bool :=
  -- Simple containment check
  let rec checkContains (so : SyntacticObject) : Bool :=
    if so == op.mover then true
    else match so with
      | .leaf _ => false
      | .node a b => checkContains a || checkContains b
  checkContains op.target

/-- Apply internal merge to workspace -/
def applyInternalMerge (w : Workspace) (op : InternalMergeOp) : Option Workspace :=
  -- Target must be in workspace
  if !w.objects.contains op.target then none
  -- Mover must be contained in target
  else if !moverInTarget op then none
  -- Mover must be different from target (proper containment)
  else if op.target == op.mover then none
  else
    let objects' := w.objects.filter (· != op.target)
    -- Use merge directly (internal merge places mover at edge of target)
    let merged := merge op.mover op.target
    some ⟨merged :: objects', w.nextId⟩

-- Part 7: Derivation State

/-- A derivation state captures everything needed to continue a derivation -/
structure DerivationState where
  numeration : Numeration
  workspace : Workspace
  deriving Repr

/-- Initial state from a numeration -/
def DerivationState.init (n : Numeration) : DerivationState :=
  ⟨n, Workspace.empty⟩

/-- Is the derivation complete?

    A derivation is complete when:
    1. The numeration is exhausted (all items used)
    2. The workspace contains exactly one SO -/
def DerivationState.isComplete (s : DerivationState) : Bool :=
  s.numeration.exhausted && s.workspace.isSingleton

/-- Get the derived structure if complete -/
def DerivationState.getResult (s : DerivationState) : Option SyntacticObject :=
  if s.isComplete then s.workspace.getResult
  else none

-- Part 8: Derivation Steps

/-- A single step in a derivation -/
inductive DerivationStep where
  | selectStep : ExtendedLI → DerivationStep
  | externalMergeStep : ExternalMergeOp → DerivationStep
  | internalMergeStep : InternalMergeOp → DerivationStep
  | transferStep : SyntacticObject → DerivationStep  -- Transfer phase complement
  deriving Repr

/-- Apply a derivation step to a state -/
def applyStep (s : DerivationState) (step : DerivationStep) : Option DerivationState :=
  match step with
  | .selectStep li =>
    match select s.numeration s.workspace li with
    | none => none
    | some result => some ⟨result.numeration, result.workspace⟩
  | .externalMergeStep op =>
    match applyExternalMerge s.workspace op with
    | none => none
    | some w' => some ⟨s.numeration, w'⟩
  | .internalMergeStep op =>
    match applyInternalMerge s.workspace op with
    | none => none
    | some w' => some ⟨s.numeration, w'⟩
  | .transferStep _complement =>
    -- Transfer ships the complement to PF/LF interfaces.
    -- The complement is conceptually removed from further narrow-syntactic
    -- operations, but the workspace structure remains intact for now.
    -- Full PF/LF separation would require a richer state model.
    some s

-- Part 9: Full Derivation

/-- A derivation is a sequence of steps from initial state to completion -/
structure FullDerivation where
  initial : Numeration
  steps : List DerivationStep
  final : DerivationState
  -- Validity: steps actually transform initial to final
  valid : final.isComplete

/-- Execute a list of steps from an initial numeration -/
def executeSteps (n : Numeration) (steps : List DerivationStep) : Option DerivationState :=
  steps.foldlM (λ s step => applyStep s step) (DerivationState.init n)

-- Part 10: Example: Building "the cat"

/-- Example: Numeration for "the cat" -/
def theCatNumeration : Numeration :=
  let detThe : ExtendedLI := ⟨.simple .D [.N], []⟩
  let nounCat : ExtendedLI := ⟨.simple .N [], []⟩
  Numeration.empty
    |>.add detThe 1 (by omega)
    |>.add nounCat 1 (by omega)

#eval theCatNumeration.totalCount  -- 2

-- ============================================================================
-- MinimalistGrammar: Grammar Instance Using Formal Types
-- ============================================================================

/-- A Minimalist grammar specifies the lexicon as a list of extended LIs. -/
structure MinimalistGrammar where
  lexicon : List ExtendedLI

/-- Minimalist derivations link a formal derivation to a clause type. -/
structure MinDerivation (g : MinimalistGrammar) where
  deriv : FullDerivation
  clauseType : ClauseType

/-- Minimalism Grammar instance.

    Derivations are formal `FullDerivation`s from Workspace.lean.
    Realization checks that the phonological yield matches. -/
instance : Grammar MinimalistGrammar where
  Derivation := Σ g : MinimalistGrammar, MinDerivation g
  realizes d ws ct :=
    let result := d.2.deriv.final.workspace.getResult
    match result with
    | some so => so.phonYield = ws.map (·.form) ∧ d.2.clauseType = ct
    | none => False
  derives g ws ct :=
    ∃ d : MinDerivation g,
      match d.deriv.final.workspace.getResult with
      | some so => so.phonYield = ws.map (·.form) ∧ d.clauseType = ct
      | none => False

end Minimalism
