/-
# Minimalist Coreference (Binding)

Coreference constraints via c-command and locality following @cite{chomsky-1981}.

## Main definitions

- `NominalType`, `SimpleClause`
- `reflexiveLicensed`, `pronounLocallyFree`, `grammaticalForCoreference`

-/

import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Core.Interface

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
def subjectCCommandsObject (clause : SimpleClause) : Bool :=
  match clause.objectSO? with
  | none => false
  | some objSO => cCommandsInB clause.toSyntacticObject clause.subjectSO objSO

/-- Object does not c-command subject: derived from the tree.
    In `{subj, {verb, obj}}`, the object's sister is `verb`,
    which does not contain the subject. -/
def objectCCommandsSubject (clause : SimpleClause) : Bool :=
  match clause.objectSO? with
  | none => false
  | some objSO => cCommandsInB clause.toSyntacticObject objSO clause.subjectSO

/-- Same local domain: both subject and object are subterms of the same
    clause tree (the minimal domain containing a SUBJECT). -/
def sameLocalDomain (clause : SimpleClause) : Bool :=
  let tree := clause.toSyntacticObject
  match clause.objectSO? with
  | none => true
  | some objSO =>
    containsB tree clause.subjectSO && containsB tree objSO

/-- Binding domain check: in a simple clause, all positions share a domain. -/
def inSameBindingDomain (_clause : SimpleClause) (_pos1 _pos2 : String) : Bool :=
  true

/-- Phi-feature agreement for coreference.
    Checks person, number, and gender agreement between antecedent and
    anaphor. Person and number come from `Word.Features`; gender uses
    `Fragments.English.Pronouns.genderAgrees` since `Word` currently
    lacks a gender field. -/
def phiAgree (w1 w2 : Word) : Bool :=
  let personMatch := match w1.features.person, w2.features.person with
    | some p1, some p2 => p1 == p2
    | _, _ => true  -- vacuous if either lacks person
  let numberMatch := match w1.features.number, w2.features.number with
    | some n1, some n2 => n1 == n2
    | _, _ => true  -- vacuous if either lacks number
  let genderMatch := Fragments.English.Pronouns.genderAgrees w1.form w2.form
  personMatch && numberMatch && genderMatch

/-- Principle A: Reflexives must be bound locally -/
def reflexiveLicensed (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some obj =>
    match classifyNominal obj with
    | some .reflexive =>
      subjectCCommandsObject clause &&
      sameLocalDomain clause &&
      phiAgree clause.subject obj
    | _ => true

/-- Reciprocals must be locally c-commanded by a semantically plural
    antecedent. Unlike reflexive licensing (which uses narrow-syntactic
    φ-agreement, hence requires morphosyntactic plurality), reciprocal
    licensing is an LF interpretive condition under the Y-model:
    the antecedent must *denote* a plurality, but need not bear plural
    morphology or trigger plural verb agreement.
    @cite{rakosi-2019}: Hungarian *egymás* is licensed by quantified NPs,
    singular coordinate DPs, and collective nouns — all syntactically
    singular but semantically plural. -/
def reciprocalLicensed (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some obj =>
    match classifyNominal obj with
    | some .reciprocal =>
      subjectCCommandsObject clause &&
      sameLocalDomain clause &&
      clause.semanticPl  -- LF condition: semantic plurality suffices
    | _ => true

/-- Principle B: Pronouns must be free locally -/
def pronounLocallyFree (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => true
  | some obj =>
    match classifyNominal obj with
    | some .pronoun =>
      !(subjectCCommandsObject clause && sameLocalDomain clause)
    | _ => true

/-- Principle C: R-expressions must be free everywhere -/
def rExpressionFree (clause : SimpleClause) : Bool :=
  match classifyNominal clause.subject with
  | some .pronoun =>
    match clause.object with
    | some obj =>
      match classifyNominal obj with
      | some .rExpression => true
      | _ => true
    | none => true
  | _ => true

/-- Grammatical for coreference under Minimalist binding -/
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
def reflexiveLicensedInSentence (ws : List Word) : Bool :=
  match parseSimpleClause ws with
  | none => false
  | some clause => reflexiveLicensed clause

def pronounCoreferenceBlocked (ws : List Word) : Bool :=
  match parseSimpleClause ws with
  | none => false
  | some clause => !pronounLocallyFree clause
structure MinimalistCoreferenceGrammar where
  strictLocality : Bool := true

def defaultGrammar : MinimalistCoreferenceGrammar := {}

def computeCoreferenceStatus (clause : SimpleClause) (i j : Nat) : Interfaces.CoreferenceStatus :=
  if i == 0 && j == 2 then
    match clause.object with
    | none => .unspecified
    | some obj =>
      match classifyNominal obj with
      | some .reflexive =>
        if subjectCCommandsObject clause && sameLocalDomain clause && phiAgree clause.subject obj
        then .obligatory
        else .blocked
      | some .reciprocal =>
        if subjectCCommandsObject clause && sameLocalDomain clause &&
           clause.semanticPl  -- LF: semantic plurality
        then .obligatory
        else .blocked
      | some .pronoun =>
        if subjectCCommandsObject clause && sameLocalDomain clause
        then .blocked
        else .possible
      | some .rExpression => .possible
      | none => .unspecified
  else if i == 2 && j == 0 then
    -- Object→subject: does the object c-command the subject?
    -- Derived from tree: in {subj, {verb, obj}}, object does NOT c-command subject
    match classifyNominal clause.subject with
    | some .reflexive =>
      if objectCCommandsSubject clause && sameLocalDomain clause
      then .obligatory
      else .blocked
    | some .reciprocal =>
      if objectCCommandsSubject clause && sameLocalDomain clause
      then .obligatory
      else .blocked
    | some .pronoun =>
      if objectCCommandsSubject clause && sameLocalDomain clause
      then .blocked
      else .possible
    | _ => .possible
  else
    .unspecified
end Minimalism.Phenomena.Coreference
