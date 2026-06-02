import Linglib.Syntax.DependencyGrammar.Basic
import Linglib.Syntax.DependencyGrammar.Nominal
import Linglib.Features.CoreferenceStatus

/-!
# Dependency-grammar coreference (binding)

Reflexives require short dependency paths; locality is defined as the
subgraph rooted at the verb of the matrix clause. The c-command analogue
in dependency grammar is *d-command*: a node `x` d-commands `y` iff `y` is
in the subtree rooted at `x`'s mother. @cite{hudson-1990},
@cite{gibson-2025}.

## Main declarations

* `SimpleClause` — clause-rooted subgraph for binding-domain bookkeeping.
* `dCommands`, `sameLocalDomain` — the d-command relation and its locality
  restriction.
* `reflexiveLicensed`, `reciprocalLicensed`, `pronounLocallyFree` — the
  binding-theory licensing predicates over a simple clause.
* `grammaticalForCoreference` — top-level acceptability check consumed by
  `Studies/Hudson1990.lean`.

## Implementation notes

* Predicate-shape definitions are `Bool`-valued, inheriting the
  substrate-wide convention from `Basic.lean`. A migration to
  `Prop` + `[DecidablePred]` is a project-wide refactor target.
-/

namespace DepGrammar.Coreference

open DepGrammar Nominal

/-! ### Clauses and locality -/

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
    (tree.deps.any λ d => d.depIdx == 0 && d.headIdx == tree.rootIdx) &&
    (tree.deps.any λ d => d.depIdx == 2 && d.headIdx == tree.rootIdx)

/-! ### D-command -/

/-- D-command: word at index `i` d-commands word at index `j` in a
    dependency tree if both are dependents of the same head and `i`
    bears the subject relation (nsubj). -/
def dCommands (tree : DepTree) (i j : Nat) : Bool :=
  tree.deps.any λ di =>
    di.depIdx == i && di.depType == .nsubj &&
    tree.deps.any λ dj =>
      dj.depIdx == j && di.headIdx == dj.headIdx

/-- Subject d-commands object: derived from the dependency tree.
    Both are dependents of the verb, and the subject bears nsubj. -/
def subjectDCommandsObject (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some _ => dCommands clause.toDepTree 0 2

/-! ### Binding-theory licensing -/

/-- Reflexive is licensed if d-commanded by an agreeing antecedent in the
    local domain. -/
def reflexiveLicensed (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some obj =>
    match classifyNominal obj with
    | some .reflexive =>
      subjectDCommandsObject clause &&
      sameLocalDomain clause &&
      decide (Word.Agree clause.subject obj)
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

/-! ### Top-level acceptability -/

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

end DepGrammar.Coreference
