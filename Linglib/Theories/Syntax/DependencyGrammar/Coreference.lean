/-
Dependency grammar coreference (binding) via dependency paths and d-command.
Reflexives require short dependency paths; locality = same subgraph rooted at verb.

References: @cite{hudson-1990}, @cite{gibson-2025}
-/

import Linglib.Theories.Syntax.DependencyGrammar.Core.Nominal
import Linglib.Core.Interface

namespace DepGrammar.Coreference

open DepGrammar Nominal

section DependencyBasedLocality

/-- Simple clause structure: a subgraph rooted at the main verb. -/
structure SimpleClause where
  subject : Word
  verb : Word
  object : Option Word
  deriving Repr

/-- Parse a simple transitive sentence into a clause. -/
def parseSimpleClause (ws : List Word) : Option SimpleClause :=
  match ws with
  | [subj, v, obj] =>
    if isNominalCat subj.cat && v.cat == .VERB && isNominalCat obj.cat then
      some ⟨subj, v, some obj⟩
    else none
  | [subj, v] =>
    if isNominalCat subj.cat && v.cat == .VERB then
      some ⟨subj, v, none⟩
    else none
  | _ => none

/-- Subject and object are co-dependents of the same verb, hence in the same local domain. -/
def sameLocalDomain (_clause : SimpleClause) : Bool := true

/-- Path length from subject to object = 2 (Subj --subj--> V <--obj-- Obj). -/
def pathLength (_clause : SimpleClause) : Nat := 2

end DependencyBasedLocality

section DependencyBasedCommand

/-- W1 d-commands W2 if both are dependents of the same head H and W1 is the subject. -/
def subjectDCommandsObject (_clause : SimpleClause) : Bool := true

/-- Object does not d-command subject. -/
def objectDCommandsSubject (_clause : SimpleClause) : Bool := false

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

/-- Reciprocals must be d-commanded by a plural antecedent in the local domain. -/
def reciprocalLicensed (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some obj =>
    match classifyNominal obj with
    | some .reciprocal =>
      subjectDCommandsObject clause &&
      sameLocalDomain clause &&
      clause.subject.features.number == some .pl
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
-- Phenomena.Anaphora.Studies.Hudson1990

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
           clause.subject.features.number == some .pl
        then .obligatory
        else .blocked
      | some .pronoun =>
        if subjectDCommandsObject clause && sameLocalDomain clause
        then .blocked
        else .possible
      | some .rExpression => .possible
      | none => .unspecified
  else if i == 2 && j == 0 then
    -- Object doesn't d-command subject
    match classifyNominal clause.subject with
    | some .reflexive => .blocked
    | some .reciprocal => .blocked
    | some .pronoun => .possible
    | _ => .possible
  else
    .unspecified

end CoreferenceConstraints

end DepGrammar.Coreference
