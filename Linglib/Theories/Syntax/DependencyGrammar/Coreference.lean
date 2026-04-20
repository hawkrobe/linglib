/-
Dependency grammar coreference (binding) via dependency paths and d-command.
Reflexives require short dependency paths; locality = same subgraph rooted at verb.

References: @cite{hudson-1990}, @cite{gibson-2025}
-/

import Linglib.Core.Dependency.Basic
import Linglib.Theories.Syntax.DependencyGrammar.Core.Nominal
import Linglib.Core.CoreferenceStatus

namespace DepGrammar.Coreference

open DepGrammar Nominal

section DependencyBasedLocality

/-- Simple clause structure: a subgraph rooted at the main verb. -/
structure SimpleClause where
  subject : Word
  verb : Word
  object : Option Word
  /-- Whether the subject denotes a plurality. Defaults to matching
      syntactic number. Override for languages where syntactic and
      semantic number diverge (@cite{rakosi-2019}). -/
  semanticPl : Bool := subject.features.number == some .pl
  deriving Repr

/-- Parse a simple transitive sentence into a clause. -/
def parseSimpleClause (ws : List Word) : Option SimpleClause :=
  match ws with
  | [subj, v, obj] =>
    if isNominalCat subj.cat && v.cat == .VERB && isNominalCat obj.cat then
      some { subject := subj, verb := v, object := some obj }
    else none
  | [subj, v] =>
    if isNominalCat subj.cat && v.cat == .VERB then
      some { subject := subj, verb := v, object := none }
    else none
  | _ => none

/-- Build a dependency tree from a simple clause.

    Indices: 0 = subject, 1 = verb (root), 2 = object (if present).
    Dependencies: subject ←nsubj— verb, object ←obj— verb. -/
def SimpleClause.toDepTree (clause : SimpleClause) : DepTree :=
  let words := match clause.object with
    | none => [clause.subject, clause.verb]
    | some obj => [clause.subject, clause.verb, obj]
  let deps : List Dependency := [⟨1, 0, .nsubj⟩] ++
    match clause.object with
    | none => []
    | some _ => [⟨1, 2, .obj⟩]
  { words := words, deps := deps, rootIdx := 1 }

/-- Same local domain: both subject and object are dependents of the
    same head (the verb), hence in the same dependency subgraph. -/
def sameLocalDomain (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => true
  | some _ =>
    let tree := clause.toDepTree
    (tree.deps.any fun d => d.depIdx == 0 && d.headIdx == tree.rootIdx) &&
    (tree.deps.any fun d => d.depIdx == 2 && d.headIdx == tree.rootIdx)

/-- Path length from subject to object: count edges through the shared
    head (subject → verb → object). -/
def pathLength (clause : SimpleClause) : Nat :=
  match clause.object with
  | none => 0
  | some _ =>
    let tree := clause.toDepTree
    let subjEdge := if tree.deps.any (fun d => d.depIdx == 0) then 1 else 0
    let objEdge := if tree.deps.any (fun d => d.depIdx == 2) then 1 else 0
    subjEdge + objEdge

end DependencyBasedLocality

section DependencyBasedCommand

/-- D-command: word at index `i` d-commands word at index `j` in a
    dependency tree if both are dependents of the same head and `i`
    bears the subject relation (nsubj). -/
def dCommands (tree : DepTree) (i j : Nat) : Bool :=
  tree.deps.any fun di =>
    di.depIdx == i && di.depType == .nsubj &&
    tree.deps.any fun dj =>
      dj.depIdx == j && di.headIdx == dj.headIdx

/-- Subject d-commands object: derived from the dependency tree.
    Both are dependents of the verb, and the subject bears nsubj. -/
def subjectDCommandsObject (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some _ => dCommands clause.toDepTree 0 2

/-- Object does not d-command subject: derived from the tree.
    The object bears obj, not nsubj, so d-command fails. -/
def objectDCommandsSubject (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some _ => dCommands clause.toDepTree 2 0

end DependencyBasedCommand

-- phi-feature agreement: imported from Core.Nominal

section CoreferenceConstraints

/-- Reflexive is licensed if d-commanded by an agreeing antecedent in the local domain. -/
def reflexiveLicensed (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some obj =>
    match classifyNominal obj with
    | some .reflexive =>
      subjectDCommandsObject clause &&
      sameLocalDomain clause &&
      phiAgree clause.subject obj
    | _ => true

/-- Reciprocals must be d-commanded by a semantically plural antecedent.
    The plurality requirement is semantic, not morphosyntactic
    (@cite{rakosi-2019}). -/
def reciprocalLicensed (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some obj =>
    match classifyNominal obj with
    | some .reciprocal =>
      subjectDCommandsObject clause &&
      sameLocalDomain clause &&
      clause.semanticPl
    | _ => true

/-- A pronoun must not be d-commanded by a coreferent antecedent locally. -/
def pronounLocallyFree (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => true
  | some obj =>
    match classifyNominal obj with
    | some .pronoun =>
      !(subjectDCommandsObject clause && sameLocalDomain clause)
    | _ => true

/-- R-expression freedom in dependency grammar -/
def rExpressionFree (clause : SimpleClause) : Bool :=
  match classifyNominal clause.subject with
  | some .pronoun =>
    match clause.object with
    | some obj =>
      match classifyNominal obj with
      | some .rExpression => true  -- Pronoun subject, R-expression object is fine
      | _ => true
    | none => true
  | _ => true

-- ============================================================================
-- Part 6: Combined Coreference Check
-- ============================================================================

/-- Is a sentence grammatical for coreference under dependency binding? -/
def grammaticalForCoreference (ws : List Word) : Bool :=
  match parseSimpleClause ws with
  | none => false
  | some clause =>
    match classifyNominal clause.subject with
    | some .reflexive => false
    | some .reciprocal => false
    | _ =>
      match clause.object with
      | none => true
      | some obj =>
        match classifyNominal obj with
        | some .reflexive => reflexiveLicensed clause
        | some .reciprocal => reciprocalLicensed clause
        | some .pronoun => false
        | _ => true

/-- Check if reflexive is licensed in a sentence -/
def reflexiveLicensedInSentence (ws : List Word) : Bool :=
  match parseSimpleClause ws with
  | none => false
  | some clause => reflexiveLicensed clause

/-- Check if pronoun coreference is blocked -/
def pronounCoreferenceBlocked (ws : List Word) : Bool :=
  match parseSimpleClause ws with
  | none => false
  | some clause => !pronounLocallyFree clause

-- Binding theory tests are verified by native_decide theorems in
-- Hudson1990

-- ============================================================================
-- Part 10: Dependency Grammar Configuration
-- ============================================================================

/-- Dependency grammar coreference configuration -/
structure DepGrammarCoreferenceConfig where
  /-- Whether to use strict path-length locality -/
  strictLocality : Bool := true

/-- Default configuration for coreference -/
def defaultConfig : DepGrammarCoreferenceConfig := {}

-- ============================================================================
-- Part 11: Theoretical Notes
-- ============================================================================

/-
## Dependency Grammar Binding Theory

### D-Command

In dependency grammar, the analogue of c-command is "d-command":
- A word W1 d-commands W2 if W1 is a co-dependent of W2
  (both are dependents of the same head) and W1 is the designated binder
  (typically the subject)

### Dependency Paths

Locality can be measured by dependency path length:
- In "John saw himself", the path John → saw ← himself has length 2
- In "John thinks Mary saw himself", path is longer (crosses clause boundary)

### Comparison with Phrase Structure Approaches

| Concept | Phrase Structure | Dependency |
|---------|-----------------|------------|
| Locality | Dominating nodes | Path length |
| Command | Sister's descendants | Co-dependents |
| Domain | Clause/phase | Subgraph rooted at V |

The predictions are the same for simple cases because:
- Subject c-commands object ↔ Subject d-commands object
- Same clause ↔ Same dependency subgraph
- Both require agreement for coreference
-/

-- ============================================================================
-- Part 12: CoreferenceTheory Interface Implementation
-- ============================================================================

/-- Compute coreference status using d-command (dependency paths) -/
def computeCoreferenceStatus (clause : SimpleClause) (i j : Nat) : Interfaces.CoreferenceStatus :=
  if i == 0 && j == 2 then
    -- Subject-object: subject d-commands object (both depend on verb)
    match clause.object with
    | none => .unspecified
    | some obj =>
      match classifyNominal obj with
      | some .reflexive =>
        if subjectDCommandsObject clause && sameLocalDomain clause && phiAgree clause.subject obj
        then .obligatory
        else .blocked
      | some .reciprocal =>
        if subjectDCommandsObject clause && sameLocalDomain clause &&
           clause.semanticPl
        then .obligatory
        else .blocked
      | some .pronoun =>
        if subjectDCommandsObject clause && sameLocalDomain clause
        then .blocked
        else .possible
      | some .rExpression => .possible
      | none => .unspecified
  else if i == 2 && j == 0 then
    -- Does the object d-command the subject?
    -- Derived: object bears .obj (not .nsubj), so d-command fails
    match classifyNominal clause.subject with
    | some .reflexive =>
      if objectDCommandsSubject clause && sameLocalDomain clause
      then .obligatory
      else .blocked
    | some .reciprocal =>
      if objectDCommandsSubject clause && sameLocalDomain clause
      then .obligatory
      else .blocked
    | some .pronoun =>
      if objectDCommandsSubject clause && sameLocalDomain clause
      then .blocked
      else .possible
    | _ => .possible
  else
    .unspecified

end CoreferenceConstraints

end DepGrammar.Coreference
