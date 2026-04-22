/-
# Minimalist Coreference (Binding)

Coreference constraints via c-command and locality following @cite{chomsky-1981}.

## Main definitions

- `NominalType`, `SimpleClause`
- `reflexiveLicensed`, `pronounLocallyFree`, `grammaticalForCoreference`

-/

import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Theories.Syntax.Minimalism.Basic
import Linglib.Core.CoreferenceStatus

namespace Minimalism.Phenomena.Coreference

/-- Types of nominal expressions for coreference -/
inductive NominalType where
  | reflexive
  | reciprocal
  | pronoun
  | rExpression
  deriving Repr, DecidableEq

/-- Is this a nominal category? -/
def isNominalCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Classify a word as a nominal type.
    Derives classification from `Fragments.English.Pronouns` rather than
    hardcoding string lists. Falls back to UPOS for R-expressions. -/
def classifyNominal (w : Word) : Option NominalType :=
  match Fragments.English.Pronouns.lookup w.form with
  | some entry => match entry.pronounType with
    | .reflexive => some .reflexive
    | .reciprocal => some .reciprocal
    | .personal => some .pronoun
    | _ => some .pronoun  -- wh, relative, demonstrative treated as pronominal
  | none =>
    if isNominalCat w.cat then some .rExpression
    else none

/-- Simple clause structure for coreference checking.
    `semanticPl` tracks whether the subject denotes a plurality,
    independently of syntactic number. In English, these coincide.
    In Hungarian, quantified NPs, singular coordinate DPs, and
    collective nouns are syntactically singular but semantically
    plural (@cite{rakosi-2019}). Defaults to matching syntactic number. -/
structure SimpleClause where
  subject : Word
  verb : Word
  object : Option Word
  /-- Whether the subject denotes a plurality (multiple individuals).
      Defaults to matching the syntactic number feature. Override for
      languages where syntactic and semantic number diverge. -/
  semanticPl : Bool := subject.features.number == some .pl
  deriving Repr

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

/-- Convert a word to a Minimalist syntactic object (leaf with UPOS mapped
    to Cat and phonological form attached). -/
private def wordToSO (w : Word) (id : Nat) : SyntacticObject :=
  mkLeafPhon (uposToCat w.cat) [] w.form id

/-- Build a phrase structure tree from a simple clause.

    Transitive: `{subj, {verb, obj}}` — subject is specifier,
    verb–object is a head-complement pair.
    Intransitive: `{subj, verb}` — subject and verb are co-daughters.

    C-command follows from the tree geometry:
    - Subject c-commands object (subject's sister contains object)
    - Object does NOT c-command subject (object's sister is verb leaf) -/
def SimpleClause.toSyntacticObject (clause : SimpleClause) : SyntacticObject :=
  let subjSO := wordToSO clause.subject 0
  let verbSO := wordToSO clause.verb 1
  match clause.object with
  | none => merge subjSO verbSO
  | some obj =>
    let objSO := wordToSO obj 2
    merge subjSO (merge verbSO objSO)

/-- The subject as a syntactic object for tree-relative c-command checks. -/
private def SimpleClause.subjectSO (clause : SimpleClause) : SyntacticObject :=
  wordToSO clause.subject 0

/-- The object as a syntactic object, if present. -/
private def SimpleClause.objectSO? (clause : SimpleClause) : Option SyntacticObject :=
  clause.object.map fun obj => wordToSO obj 2

/-- Subject c-commands object: derived from the phrase structure tree.
    In `{subj, {verb, obj}}`, the subject's sister is `{verb, obj}`,
    which contains the object. -/
def subjectCCommandsObject (clause : SimpleClause) : Prop :=
  match clause.objectSO? with
  | none => False
  | some objSO => cCommandsIn clause.toSyntacticObject clause.subjectSO objSO

instance (clause : SimpleClause) : Decidable (subjectCCommandsObject clause) := by
  unfold subjectCCommandsObject
  cases clause.objectSO? <;> infer_instance

/-- Object does not c-command subject: derived from the tree.
    In `{subj, {verb, obj}}`, the object's sister is `verb`,
    which does not contain the subject. -/
def objectCCommandsSubject (clause : SimpleClause) : Prop :=
  match clause.objectSO? with
  | none => False
  | some objSO => cCommandsIn clause.toSyntacticObject objSO clause.subjectSO

instance (clause : SimpleClause) : Decidable (objectCCommandsSubject clause) := by
  unfold objectCCommandsSubject
  cases clause.objectSO? <;> infer_instance

/-- Same local domain: both subject and object are subterms of the same
    clause tree (the minimal domain containing a SUBJECT). -/
def sameLocalDomain (clause : SimpleClause) : Prop :=
  let tree := clause.toSyntacticObject
  match clause.objectSO? with
  | none => True
  | some objSO =>
    contains tree clause.subjectSO ∧ contains tree objSO

instance (clause : SimpleClause) : Decidable (sameLocalDomain clause) := by
  unfold sameLocalDomain
  cases clause.objectSO? <;> infer_instance

/-- Binding domain check: in a simple clause, all positions share a domain. -/
def inSameBindingDomain (_clause : SimpleClause) (_pos1 _pos2 : String) : Prop :=
  True

instance (clause : SimpleClause) (pos1 pos2 : String) :
    Decidable (inSameBindingDomain clause pos1 pos2) := by
  unfold inSameBindingDomain; infer_instance

/-- Phi-feature agreement for coreference.
    Checks person, number, and gender agreement between antecedent and
    anaphor. Person and number come from `Word.Features`; gender uses
    `Fragments.English.Pronouns.genderAgrees` since `Word` currently
    lacks a gender field. -/
def phiAgree (w1 w2 : Word) : Prop :=
  (match w1.features.person, w2.features.person with
    | some p1, some p2 => p1 = p2
    | _, _ => True) ∧
  (match w1.features.number, w2.features.number with
    | some n1, some n2 => n1 = n2
    | _, _ => True) ∧
  Fragments.English.Pronouns.genderAgrees w1.form w2.form = true

instance (w1 w2 : Word) : Decidable (phiAgree w1 w2) := by
  unfold phiAgree
  have d1 : Decidable
      (match w1.features.person, w2.features.person with
       | some p1, some p2 => p1 = p2
       | _, _ => True) := by
    split <;> infer_instance
  have d2 : Decidable
      (match w1.features.number, w2.features.number with
       | some n1, some n2 => n1 = n2
       | _, _ => True) := by
    split <;> infer_instance
  exact inferInstance

/-- Principle A: Reflexives must be bound locally -/
def reflexiveLicensed (clause : SimpleClause) : Prop :=
  match clause.object with
  | none => False
  | some obj =>
    match classifyNominal obj with
    | some .reflexive =>
      subjectCCommandsObject clause ∧
      sameLocalDomain clause ∧
      phiAgree clause.subject obj
    | _ => True

instance (clause : SimpleClause) : Decidable (reflexiveLicensed clause) := by
  unfold reflexiveLicensed
  split <;> first | infer_instance | (split <;> infer_instance)

/-- Reciprocals must be locally c-commanded by a semantically plural
    antecedent. Unlike reflexive licensing (which uses narrow-syntactic
    φ-agreement, hence requires morphosyntactic plurality), reciprocal
    licensing is an LF interpretive condition under the Y-model:
    the antecedent must *denote* a plurality, but need not bear plural
    morphology or trigger plural verb agreement.
    @cite{rakosi-2019}: Hungarian *egymás* is licensed by quantified NPs,
    singular coordinate DPs, and collective nouns — all syntactically
    singular but semantically plural. -/
def reciprocalLicensed (clause : SimpleClause) : Prop :=
  match clause.object with
  | none => False
  | some obj =>
    match classifyNominal obj with
    | some .reciprocal =>
      subjectCCommandsObject clause ∧
      sameLocalDomain clause ∧
      clause.semanticPl = true  -- LF condition: semantic plurality suffices
    | _ => True

instance (clause : SimpleClause) : Decidable (reciprocalLicensed clause) := by
  unfold reciprocalLicensed
  split <;> first | infer_instance | (split <;> infer_instance)

/-- Principle B: Pronouns must be free locally -/
def pronounLocallyFree (clause : SimpleClause) : Prop :=
  match clause.object with
  | none => True
  | some obj =>
    match classifyNominal obj with
    | some .pronoun =>
      ¬ (subjectCCommandsObject clause ∧ sameLocalDomain clause)
    | _ => True

instance (clause : SimpleClause) : Decidable (pronounLocallyFree clause) := by
  unfold pronounLocallyFree
  split <;> first | infer_instance | (split <;> infer_instance)

/-- Principle C: R-expressions must be free everywhere.

    An R-expression is free iff no coreferential pronoun c-commands it.
    In a simple clause `{subj, {verb, obj}}`, a pronominal subject
    c-commands the object (via tree-relative `cCommandsIn`), so
    subject–object coreference with an R-expression object is blocked.

    Note: WLM (@cite{takahashi-hulsey-2009}, @cite{gong-2022}) can
    bleed Condition C by merging the NP restrictor at a chain position
    above the binder. This function checks the *surface* tree; the
    WLM escape is modeled via `wlmAvoidsCondC` in `LateMerger.lean`. -/
def rExpressionFree (clause : SimpleClause) : Prop :=
  match classifyNominal clause.subject with
  | some .pronoun =>
    match clause.object with
    | some obj =>
      match classifyNominal obj with
      | some .rExpression =>
        -- Condition C: R-expression object must NOT be c-commanded
        -- by the coreferential pronominal subject
        ¬ subjectCCommandsObject clause
      | _ => True
    | none => True
  | _ => True

instance (clause : SimpleClause) : Decidable (rExpressionFree clause) := by
  unfold rExpressionFree
  split <;> first
    | infer_instance
    | (split <;> first | infer_instance | (split <;> infer_instance))

/-- Grammatical for coreference under Minimalist binding -/
def grammaticalForCoreference (ws : List Word) : Prop :=
  match parseSimpleClause ws with
  | none => False
  | some clause =>
    match classifyNominal clause.subject with
    | some .reflexive => False
    | some .reciprocal => False
    | _ =>
      match clause.object with
      | none => True
      | some obj =>
        match classifyNominal obj with
        | some .reflexive => reflexiveLicensed clause
        | some .reciprocal => reciprocalLicensed clause
        | some .pronoun => False
        | _ => True

instance (ws : List Word) : Decidable (grammaticalForCoreference ws) := by
  unfold grammaticalForCoreference
  split <;> first
    | infer_instance
    | (split <;> first
        | infer_instance
        | (split <;> first | infer_instance | (split <;> infer_instance)))

def reflexiveLicensedInSentence (ws : List Word) : Prop :=
  match parseSimpleClause ws with
  | none => False
  | some clause => reflexiveLicensed clause

instance (ws : List Word) : Decidable (reflexiveLicensedInSentence ws) := by
  unfold reflexiveLicensedInSentence
  cases parseSimpleClause ws <;> infer_instance

def pronounCoreferenceBlocked (ws : List Word) : Prop :=
  match parseSimpleClause ws with
  | none => False
  | some clause => ¬ pronounLocallyFree clause

instance (ws : List Word) : Decidable (pronounCoreferenceBlocked ws) := by
  unfold pronounCoreferenceBlocked
  cases parseSimpleClause ws <;> infer_instance

structure MinimalistCoreferenceGrammar where
  strictLocality : Bool := true

def defaultGrammar : MinimalistCoreferenceGrammar := {}

def computeCoreferenceStatus (clause : SimpleClause) (i j : Nat) : Interfaces.CoreferenceStatus :=
  if i = 0 ∧ j = 2 then
    match clause.object with
    | none => .unspecified
    | some obj =>
      match classifyNominal obj with
      | some .reflexive =>
        if subjectCCommandsObject clause ∧ sameLocalDomain clause ∧ phiAgree clause.subject obj
        then .obligatory
        else .blocked
      | some .reciprocal =>
        if subjectCCommandsObject clause ∧ sameLocalDomain clause ∧
           clause.semanticPl = true  -- LF: semantic plurality
        then .obligatory
        else .blocked
      | some .pronoun =>
        if subjectCCommandsObject clause ∧ sameLocalDomain clause
        then .blocked
        else .possible
      | some .rExpression =>
        -- Condition C: pronoun subject c-commanding R-expression object
        -- blocks coreference (the R-expression is not free)
        if subjectCCommandsObject clause
        then .blocked
        else .possible
      | none => .unspecified
  else if i = 2 ∧ j = 0 then
    -- Object→subject: does the object c-command the subject?
    -- Derived from tree: in {subj, {verb, obj}}, object does NOT c-command subject
    match classifyNominal clause.subject with
    | some .reflexive =>
      if objectCCommandsSubject clause ∧ sameLocalDomain clause
      then .obligatory
      else .blocked
    | some .reciprocal =>
      if objectCCommandsSubject clause ∧ sameLocalDomain clause
      then .obligatory
      else .blocked
    | some .pronoun =>
      if objectCCommandsSubject clause ∧ sameLocalDomain clause
      then .blocked
      else .possible
    | _ => .possible
  else
    .unspecified
end Minimalism.Phenomena.Coreference
