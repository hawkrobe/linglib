import Linglib.Syntax.DependencyGrammar.Basic
import Linglib.Syntax.Binding.Basic

/-!
# Dependency-grammar coreference (binding)

Binding via **d-command** and locality ([hudson-1990], [gibson-2025]).
The c-command analogue in dependency grammar is *d-command*: `x` d-commands `y`
iff both are dependents of the same head and `x` bears the subject relation.
Locality is the dependency subgraph rooted at the matrix verb.

As with the other frameworks, the binding principles are *not* restated here:
this file supplies dependency grammar's command relation as a
`Binding.CommandRelation` instance, and the framework-neutral engine
(`Syntax/Binding/Basic.lean`) derives Principles A/B/C over it. The file is
language-neutral — it imports no Fragment.

## Main definitions

- `toDepTree`, `dCommands`, `subjectDCommandsObject`, `sameLocalDomain` — the
  d-command relation and its locality restriction, over a `Binding.SimpleClause`.
- `instance : CommandRelation` — the dependency-grammar instance of the abstract
  command relation (d-command); the engine supplies Principles A/B/C over it.
-/

namespace DepGrammar.Coreference

open Binding (SimpleClause Pos CommandRelation)

/-! ### D-command from the dependency tree -/

/-- Build a dependency tree from a clause. Indices: 0 = subject, 1 = verb
    (root), 2 = object (if present); subject ←nsubj— verb, object ←obj— verb. -/
def toDepTree (clause : SimpleClause) : DepTree :=
  let words := match clause.object with
    | none => [clause.subject, clause.verb]
    | some obj => [clause.subject, clause.verb, obj]
  let deps : List Dependency := [⟨1, 0, .nsubj⟩] ++
    match clause.object with
    | none => []
    | some _ => [⟨1, 2, .obj⟩]
  { words := words, deps := deps, rootIdx := 1 }

/-- D-command: the word at `i` d-commands the word at `j` if both are dependents
    of the same head and `i` bears the subject relation (nsubj). -/
def dCommands (tree : DepTree) (i j : Nat) : Bool :=
  tree.deps.any fun di =>
    di.depIdx == i && di.depType == .nsubj &&
    tree.deps.any fun dj => dj.depIdx == j && di.headIdx == dj.headIdx

/-- Subject d-commands object: both dependents of the verb, subject bears nsubj. -/
def subjectDCommandsObject (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some _ => dCommands (toDepTree clause) 0 2

/-- Both positions are dependents of the same head (the verb) — one domain. -/
def sameLocalDomain (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => true
  | some _ =>
    let tree := toDepTree clause
    (tree.deps.any fun d => d.depIdx == 0 && d.headIdx == tree.rootIdx) &&
    (tree.deps.any fun d => d.depIdx == 2 && d.headIdx == tree.rootIdx)

/-! ### Dependency grammar as a command relation -/

/-- The dependency-grammar command relation: d-command. Object→subject never
    holds (only the subject bears nsubj). -/
def commands (c : SimpleClause) : Pos → Pos → Prop
  | .subject, .object => subjectDCommandsObject c = true
  | _, _ => False

instance (c : SimpleClause) (i j : Pos) : Decidable (commands c i j) := by
  unfold commands; split <;> infer_instance

/-- Locality: in a simple clause all positions share the one binding domain. -/
def sameDomain (c : SimpleClause) (_ _ : Pos) : Prop := sameLocalDomain c = true

instance (c : SimpleClause) (i j : Pos) : Decidable (sameDomain c i j) :=
  inferInstanceAs (Decidable (sameLocalDomain c = true))

/-- The dependency-grammar instance of the abstract command relation
    ([barker-pullum-1990]): d-command. The engine supplies Principles
    A/B/C; a study applies them with this instance and a language classifier. -/
instance : CommandRelation where
  commands := commands
  sameDomain := sameDomain
  commandsDec := fun c i j => inferInstance
  sameDomainDec := fun c i j => inferInstance

end DepGrammar.Coreference
