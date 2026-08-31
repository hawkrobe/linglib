import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.SyntacticObject.Subterm
import Linglib.Syntax.Binding.Basic
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.FunctionWords
import Linglib.Features.MinimalPairs

open Morphology (Word)

/-!
# Chomsky 1981: binding principles A, B and C

The Government-and-Binding binding theory of [chomsky-1981]
classifies nominal expressions into three types and constrains their
distribution by c-command + a local binding domain:

- **Principle A**: an anaphor must be bound (c-commanded by a coindexed
  antecedent) in its local domain
- **Principle B**: a pronoun must be free (not bound) in its local domain
- **Principle C**: an R-expression must be free everywhere

This file holds the textbook minimal-pair paradigm and verifies the Minimalist binding
implementation — c-command as a `CommandRelation` instance over the phrase-structure tree —
against the pairs. Three of the five datasets are contrasts the sentence-level predicate can
adjudicate and it captures all of them; Principle C is a fact about a construal rather than a
string, so the referential-expression contrast is checked at the construal level, where the
engine blocks a commanded name from corefering; and the reciprocal data's coordinated subjects
lie outside the three-word parser, with the plural-antecedent contrast checked within it.

## Main definitions

* `reflexiveCoreferenceData`, `pronominalDisjointReferenceData`,
  `referentialExpressionFreedomData`, `complementaryDistributionData`,
  `reciprocalCoreferenceData` — the minimal-pair datasets
* the `CommandRelation` instance — Minimalist c-command over the clause's tree

## Main results

* `captures_binding_data` — the engine captures the three sentence-level datasets
* `principleC_blocks_commanded_name` — Principle C at the construal level
* `reciprocal_plural_antecedent` — the reciprocal contrast within the parser's reach

Companion to `Reinhart1976.lean` (which formalizes the c-command
relation that Principles A/B/C presuppose) and to
`SagWasowBender2003.lean` (the HPSG re-axiomatization that subsumes
Principle C under Principle B); `Hudson1990.lean` (DG) and
`Cooper2023/Basic.lean` (TTR) verify their analyses against the same
tables.
-/

namespace Chomsky1981


open Features.MinimalPairs
open Minimalist SyntacticObject
open Binding (SimpleClause Pos CommandRelation)

private abbrev john := English.Nouns.john.toWordSg
private abbrev mary := English.Nouns.mary.toWordSg
private abbrev sam := English.Nouns.sam.toWordSg
private abbrev pat := English.Nouns.pat.toWordSg
private abbrev he := English.Pronouns.he.toWord
private abbrev him := English.Pronouns.him.toWord
private abbrev her := English.Pronouns.her.toWord
private abbrev they := English.Pronouns.they.toWord
private abbrev them := English.Pronouns.them.toWord
private abbrev himself := English.Pronouns.himself.toWord
private abbrev herself := English.Pronouns.herself.toWord
private abbrev themselves := English.Pronouns.themselves.toWord
private abbrev eachOther := English.Pronouns.eachOther.toWord
private abbrev sees := English.Predicates.Verbal.see.toWord3sg
private abbrev see := English.Predicates.Verbal.see.toWordPl
private abbrev saw := English.Predicates.Verbal.see.toWordPast
private abbrev and_ := English.FunctionWords.and_.toWord

/-! ### Coreference / binding (relocated from Minimalist/Coreference.lean)

Binding via **c-command** and locality ([chomsky-1981]). The binding
principles themselves are *not* restated here: this section supplies Minimalism's
command relation (c-command, read off the phrase-structure tree) as a
`Syntax.Binding.CommandRelation` instance, and the framework-neutral engine
(`Syntax/Binding/Basic.lean`) derives Principles A/B/C and the coreference
predictions from it. The instance is language-neutral; the theorems below
combine it with English's binding-class classifier.
-/

/-! #### C-command from tree geometry -/

/-- Convert a word to a Minimalist lexical-item token (UPOS mapped to `Cat`,
    phonological form attached). The smart Merge `SyntacticObject.node` is noncomputable, so
    concrete trees are built planar-first from these tokens and `decide`d over. -/
private def wordTok (w : Word) (id : Nat) : LIToken :=
  ⟨.simple (uposToCat w.cat) [] w.form, id⟩

/-- Build a phrase-structure tree from a clause: transitive `{subj, {verb, obj}}`
    (subject specifier, verb–object a head-complement pair), intransitive
    `{subj, verb}`. C-command follows from the geometry. Built planar-first so
    the containment / c-command decision procedures reduce. -/
def toSyntacticObject (clause : SimpleClause) : SyntacticObject :=
  let subjP := leafP (wordTok clause.subject 0)
  let verbP := leafP (wordTok clause.verb 1)
  match clause.object with
  | none => ofPlanar (nodeP subjP verbP)
  | some obj => ofPlanar (nodeP subjP (nodeP verbP (leafP (wordTok obj 2))))

private def subjectSO (clause : SimpleClause) : SyntacticObject :=
  lexLeaf (wordTok clause.subject 0)

private def objectSO? (clause : SimpleClause) : Option SyntacticObject :=
  clause.object.map fun obj => lexLeaf (wordTok obj 2)

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

/-! #### Minimalism as a command relation -/

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
    the theorems below apply them with this instance in scope and a language
    classifier. -/
instance : CommandRelation where
  commands := commands
  sameDomain := sameDomain
  commandsDec := fun c i j => inferInstance
  sameDomainDec := fun c i j => inferInstance

/-- Reflexives require local c-commanding antecedent. -/
def reflexiveCoreferenceData : PhenomenonData := {
  name := "Reflexive Coreference"
  generalization := "Reflexives require a c-commanding antecedent in the local domain"
  pairs := [
    -- Local antecedent required
    { lhs := [john, sees, himself]
      rhs := [himself, sees, john]
      description := "Reflexive needs c-commanding antecedent"
      citation := "Chomsky (1981); Pollard & Sag (1994)" },

    { lhs := [mary, sees, herself]
      rhs := [herself, sees, mary]
      description := "Reflexive needs c-commanding antecedent" },

    { lhs := [they, see, themselves]
      rhs := [themselves, see, them]
      description := "Plural reflexive needs plural antecedent" },

    -- Agreement required
    { lhs := [john, sees, himself]
      rhs := [john, sees, herself]
      description := "Reflexive must agree with antecedent (gender)" },

    { lhs := [they, see, themselves]
      rhs := [they, see, himself]
      description := "Reflexive must agree with antecedent (number)" }
  ]
}

/-- Pronouns cannot corefer with local c-commanding antecedent. -/
def pronominalDisjointReferenceData : PhenomenonData := {
  name := "Pronominal Disjoint Reference"
  generalization := "Pronouns cannot corefer with a c-commanding nominal in the local domain"
  pairs := [
    -- Coreference blocked locally (the ungrammatical reading is with coreference)
    { lhs := [john, sees, mary]
      rhs := [john, sees, him]  -- intended: John₁ sees him₁
      description := "Pronoun resists coreference with local subject"
      citation := "Chomsky (1981)" },

    { lhs := [mary, sees, john]
      rhs := [mary, sees, her]  -- intended: Mary₁ sees her₁
      description := "Pronoun resists coreference with local subject" }
  ]
}

/-- Full nominals cannot corefer with c-commanding pronoun. -/
def referentialExpressionFreedomData : PhenomenonData := {
  name := "Referential Expression Freedom"
  generalization := "Names and descriptions cannot corefer with a c-commanding pronoun"
  pairs := [
    { lhs := [john, sees, mary]
      rhs := [he, sees, john]  -- intended: He₁ sees John₁
      description := "Name resists coreference with c-commanding pronoun"
      citation := "Chomsky (1981)" }
  ]
}

/-- Reflexives and pronouns in complementary distribution. -/
def complementaryDistributionData : PhenomenonData := {
  name := "Complementary Distribution"
  generalization := "In the local domain, coreference requires reflexive; pronouns are blocked"
  pairs := [
    { lhs := [john, sees, himself]
      rhs := [john, sees, him]  -- intended coreference
      description := "Local coreference: reflexive required, pronoun blocked"
      citation := "Chomsky (1981)" },

    { lhs := [mary, sees, herself]
      rhs := [mary, sees, her]  -- intended coreference
      description := "Local coreference: reflexive required, pronoun blocked" }
  ]
}

/-- Reciprocals require a plural/coordinated antecedent and local binding. -/
def reciprocalCoreferenceData : PhenomenonData := {
  name := "Reciprocal Coreference"
  generalization :=
    "Reciprocals require a c-commanding semantically plural antecedent in the local domain"
  pairs := [
    -- Coordinated antecedent required
    { lhs := [sam, and_, pat, saw, eachOther]
      rhs := [eachOther, saw, sam, and_, pat]
      description := "Reciprocal needs c-commanding antecedent"
      citation := "Dalrymple et al. (1998)" },

    -- Reciprocal vs reflexive complementary distribution
    { lhs := [sam, and_, pat, saw, eachOther]
      rhs := [sam, and_, pat, saw, themselves]  -- awkward as reciprocal reading
      description := "Reciprocal preferred for symmetric reading with coordinated subject" },

    -- Plural antecedent requirement
    { lhs := [they, see, eachOther]
      rhs := [john, sees, eachOther]  -- singular antecedent fails
      description := "Reciprocal requires semantically plural antecedent" }
  ]
}

/-- English binding under Minimalist (c-command): the framework-neutral engine
    (`Binding.grammaticalForCoreference`) applied with Minimalism's
    `CommandRelation` instance (the relocated instance above) and
    English's binding-class classifier. -/
private abbrev grammaticalForCoreference (ws : List Word) : Prop :=
  Binding.grammaticalForCoreference Binding.bindingClassOf ws

/-- Coverage of a `PhenomenonData` set under Minimalist binding theory.

    Stated `Prop`-valued (with a `Decidable` instance) because the
    underlying `grammaticalForCoreference` predicate is `Prop`-valued. -/
def capturesCoreferenceData (phenom : PhenomenonData) : Prop :=
  ∀ p ∈ phenom.pairs,
    grammaticalForCoreference p.lhs ∧ ¬ grammaticalForCoreference p.rhs

instance (phenom : PhenomenonData) : Decidable (capturesCoreferenceData phenom) := by
  unfold capturesCoreferenceData; infer_instance

/-- Minimalist binding theory captures every minimal pair in the three datasets the
sentence-level predicate can adjudicate: the grammatical member of each pair is licensed for
coreference and its partner is not. -/
theorem captures_binding_data :
    ∀ phenom ∈ [reflexiveCoreferenceData, pronominalDisjointReferenceData,
                complementaryDistributionData],
      capturesCoreferenceData phenom := by
  intro phenom h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

/-- Principle C is a fact about a construal, not a string: *he sees John* is grammatical on the
non-coreferential reading, so the sentence-level predicate cannot register
`referentialExpressionFreedomData`'s contrast. At the construal level the engine blocks it — the
commanded name object cannot corefer with the pronoun subject. -/
theorem principleC_blocks_commanded_name :
    Binding.computeCoreferenceStatus Binding.bindingClassOf
      { subject := he, verb := sees, object := some john } .subject .object = .blocked := by
  decide

/-- Reciprocal binding within the three-word parser's reach: a semantically plural antecedent
licenses *each other* and a singular one does not. The reciprocal dataset's coordinated subjects
(*Sam and Pat saw each other*) lie outside that parser, so they are recorded as data but not
adjudicated here. -/
theorem reciprocal_plural_antecedent :
    grammaticalForCoreference [they, see, eachOther] ∧
    ¬ grammaticalForCoreference [john, sees, eachOther] := by
  decide

end Chomsky1981
