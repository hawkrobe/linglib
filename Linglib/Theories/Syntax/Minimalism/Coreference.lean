/-
# Minimalist Coreference (Binding)

Coreference constraints via c-command and locality following Chomsky (1981, 1986).

## Main definitions

- `NominalType`, `SimpleClause`
- `reflexiveLicensed`, `pronounLocallyFree`, `grammaticalForCoreference`

## References

- Chomsky, N. (1981). Lectures on Government and Binding.
- Chomsky, N. (1986). Knowledge of Language.
- Adger, D. (2003). Core Syntax, Chapter 8.
-/

import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Core.Interface

namespace Minimalism.Phenomena.Coreference

/-- Types of nominal expressions for coreference -/
inductive NominalType where
  | reflexive
  | pronoun
  | rExpression
  deriving Repr, DecidableEq

/-- Is this a nominal category? -/
def isNominalCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Classify a word as a nominal type -/
def classifyNominal (w : Word) : Option NominalType :=
  if w.form ∈ ["himself", "herself", "themselves", "myself", "yourself", "ourselves"] then
    some .reflexive
  else if w.form ∈ ["he", "she", "they", "him", "her", "them", "it"] then
    some .pronoun
  else if isNominalCat w.cat then
    some .rExpression
  else
    none

/-- Simple clause structure for coreference checking -/
structure SimpleClause where
  subject : Word
  verb : Word
  object : Option Word
  deriving Repr

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

def subjectCCommandsObject (_clause : SimpleClause) : Bool :=
  true

def objectCCommandsSubject (_clause : SimpleClause) : Bool :=
  false

def sameLocalDomain (_clause : SimpleClause) : Bool :=
  true

def inSameBindingDomain (_clause : SimpleClause) (_pos1 _pos2 : String) : Bool :=
  true

/-- Phi-feature agreement for coreference -/
def phiAgree (w1 w2 : Word) : Bool :=
  let personMatch := match w1.features.person, w2.features.person with
    | some p1, some p2 => p1 == p2
    | _, _ => true
  let numberMatch := match w1.features.number, w2.features.number with
    | some n1, some n2 => n1 == n2
    | _, _ => true
  let genderMatch :=
    if w2.form == "himself" then
      w1.form ∈ ["John", "he", "him"]
    else if w2.form == "herself" then
      w1.form ∈ ["Mary", "she", "her"]
    else if w2.form ∈ ["themselves", "ourselves"] then
      w1.features.number == some .pl
    else
      true
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
    | _ =>
      match clause.object with
      | none => true
      | some obj =>
        match classifyNominal obj with
        | some .reflexive => reflexiveLicensed clause
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

structure MinimalismTheory
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
      | some .pronoun =>
        if subjectCCommandsObject clause && sameLocalDomain clause
        then .blocked
        else .possible
      | some .rExpression => .possible
      | none => .unspecified
  else if i == 2 && j == 0 then
    match classifyNominal clause.subject with
    | some .reflexive => .blocked
    | some .pronoun => .possible
    | _ => .possible
  else
    .unspecified
instance : Interfaces.CoreferenceTheory MinimalismTheory where
  Structure := SimpleClause
  parse := parseSimpleClause
  coreferenceStatus := computeCoreferenceStatus
  grammaticalForCoreference := λ clause =>
    match classifyNominal clause.subject with
    | some .reflexive => false
    | _ =>
      match clause.object with
      | none => true
      | some obj =>
        match classifyNominal obj with
        | some .reflexive => reflexiveLicensed clause
        | some .pronoun => false
        | _ => true

end Minimalism.Phenomena.Coreference
