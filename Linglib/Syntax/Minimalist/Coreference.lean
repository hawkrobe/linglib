import Linglib.Syntax.Minimalist.Basic
import Linglib.Syntax.Binding.Basic

/-!
# Minimalist Coreference (Binding)

Binding via **c-command** and locality ([chomsky-1981]). The binding
principles themselves are *not* restated here: this file supplies Minimalism's
command relation (c-command, read off the phrase-structure tree) as a
`Syntax.Binding.CommandRelation` instance, and the framework-neutral engine
(`Syntax/Binding/Basic.lean`) derives Principles A/B/C and the coreference
predictions from it. The file is language-neutral — it imports no Fragment; a
study combines this instance with a language's binding-class classifier.

## Main definitions

- `subjectCCommandsObject` / `objectCCommandsSubject` — c-command from tree
  geometry.
- `instance : CommandRelation` — the Minimalist instance of the abstract
  command relation (c-command); the engine supplies Principles A/B/C over it.
-/

namespace Minimalist.Coreference

open Binding (SimpleClause Pos CommandRelation)

/-! ### C-command from tree geometry -/

/-- Convert a word to a Minimalist syntactic object (leaf with UPOS mapped to
    Cat and phonological form attached). -/
private def wordToSO (w : Word) (id : Nat) : SyntacticObject :=
  mkLeafPhon (uposToCat w.cat) [] w.form id

/-- Build a phrase-structure tree from a clause: transitive `{subj, {verb, obj}}`
    (subject specifier, verb–object a head-complement pair), intransitive
    `{subj, verb}`. C-command follows from the geometry. -/
def toSyntacticObject (clause : SimpleClause) : SyntacticObject :=
  let subjSO := wordToSO clause.subject 0
  let verbSO := wordToSO clause.verb 1
  match clause.object with
  | none => merge subjSO verbSO
  | some obj => merge subjSO (merge verbSO (wordToSO obj 2))

private def subjectSO (clause : SimpleClause) : SyntacticObject :=
  wordToSO clause.subject 0

private def objectSO? (clause : SimpleClause) : Option SyntacticObject :=
  clause.object.map fun obj => wordToSO obj 2

/-- Subject c-commands object: in `{subj, {verb, obj}}`, the subject's sister
    `{verb, obj}` contains the object. -/
def subjectCCommandsObject (clause : SimpleClause) : Prop :=
  match objectSO? clause with
  | none => False
  | some objSO => cCommandsIn (toSyntacticObject clause) (subjectSO clause) objSO

instance (clause : SimpleClause) : Decidable (subjectCCommandsObject clause) := by
  unfold subjectCCommandsObject; cases objectSO? clause <;> infer_instance

/-- Object does not c-command subject: in `{subj, {verb, obj}}`, the object's
    sister `verb` does not contain the subject. -/
def objectCCommandsSubject (clause : SimpleClause) : Prop :=
  match objectSO? clause with
  | none => False
  | some objSO => cCommandsIn (toSyntacticObject clause) objSO (subjectSO clause)

instance (clause : SimpleClause) : Decidable (objectCCommandsSubject clause) := by
  unfold objectCCommandsSubject; cases objectSO? clause <;> infer_instance

/-- Both positions are in the local clause tree (the minimal domain). -/
def sameLocalDomain (clause : SimpleClause) : Prop :=
  match objectSO? clause with
  | none => True
  | some objSO =>
    contains (toSyntacticObject clause) (subjectSO clause) ∧
    contains (toSyntacticObject clause) objSO

instance (clause : SimpleClause) : Decidable (sameLocalDomain clause) := by
  unfold sameLocalDomain; cases objectSO? clause <;> infer_instance

/-! ### Minimalism as a command relation -/

/-- The Minimalist command relation: c-command read off the tree. -/
def commands (c : SimpleClause) : Pos → Pos → Prop
  | .subject, .object => subjectCCommandsObject c
  | .object, .subject => objectCCommandsSubject c
  | _, _ => False

instance (c : SimpleClause) (i j : Pos) : Decidable (commands c i j) := by
  unfold commands; split <;> infer_instance

/-- Locality: in a simple clause all positions share the one binding domain. -/
def sameDomain (c : SimpleClause) (_ _ : Pos) : Prop := sameLocalDomain c

instance (c : SimpleClause) (i j : Pos) : Decidable (sameDomain c i j) :=
  inferInstanceAs (Decidable (sameLocalDomain c))

/-- Minimalism is an instance of the abstract command relation
    ([barker-pullum-1990]). The binding principles
    (`Syntax.Binding.grammaticalForCoreference` etc.) come from the engine;
    a study applies them with this instance in scope and a language classifier. -/
instance : CommandRelation where
  commands := commands
  sameDomain := sameDomain
  commandsDec := fun c i j => inferInstance
  sameDomainDec := fun c i j => inferInstance

end Minimalist.Coreference
