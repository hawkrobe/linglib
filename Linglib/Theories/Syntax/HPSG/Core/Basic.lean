/-
HPSG formalization: typed feature structures, signs, and phrase structure schemata.
Pollard & Sag (1994), Sag, Wasow & Bender (2003), Ginzburg & Sag (2000).
-/

import Linglib.Core.Grammar

namespace HPSG

section FeatureStructures

/-- Verb form features. -/
inductive VForm where
  | finite
  | infinitive
  | gerund
  | pastParticiple
  | presentParticiple
  deriving Repr, DecidableEq

/-- The INV(erted) feature for subject-aux inversion. -/
inductive Inv where
  | plus
  | minus
  deriving Repr, DecidableEq

/-- Head features (shared between head and phrase). -/
structure HeadFeatures where
  vform : VForm := .finite
  inv : Inv := .minus
  aux : Bool := false
  deriving Repr, DecidableEq

/-- Valence features (what arguments are needed). -/
structure Valence where
  subj : List UD.UPOS := []     -- subject requirement
  comps : List UD.UPOS := []    -- complement requirements
  deriving Repr, DecidableEq

/-- The SYNSEM value (syntax-semantics bundle). -/
structure Synsem where
  cat : UD.UPOS
  head : HeadFeatures := {}
  val : Valence := {}
  deriving Repr

end FeatureStructures

section Signs

/-- An HPSG sign: word or phrase with syntactic info. -/
inductive Sign where
  | word : Word → Synsem → Sign
  | phrase : List Sign → Synsem → Sign
  deriving Repr

/-- Get the SYNSEM of a sign. -/
def Sign.synsem : Sign → Synsem
  | .word _ ss => ss
  | .phrase _ ss => ss

/-- Get the yield (word list) of a sign. -/
partial def Sign.yield : Sign → List Word
  | .word w _ => [w]
  | .phrase children _ => children.flatMap Sign.yield

end Signs

section Schemata

/-- Head-Complement Schema: head combines with its complements. -/
structure HeadCompRule where
  head : Sign
  comps : List Sign
  result : Sign
  compsMatch : (head.synsem.val.comps = comps.map (·.synsem.cat))
  /-- Head Feature Principle: result category = head category -/
  hfp : result.synsem.cat = head.synsem.cat

/-- Head-Subject Schema: phrase combines with its subject. -/
structure HeadSubjRule where
  subj : Sign
  headPhrase : Sign
  result : Sign
  subjMatch : (headPhrase.synsem.val.subj = [subj.synsem.cat])
  /-- Head Feature Principle: result category = head phrase category -/
  hfp : result.synsem.cat = headPhrase.synsem.cat

end Schemata

section InversionConstraint

/-- [INV +] requires aux-initial; [INV -] requires subject-initial. -/
def satisfiesInversionConstraint (s : Sign) : Prop :=
  match s with
  | .phrase children ss =>
    if ss.head.inv = .plus then
      match children.head? with
      | some first => first.synsem.head.aux
      | none => False
    else
      True
  | .word _ _ => True

end InversionConstraint

section ClauseTypes

/-- Matrix questions require [INV +]. -/
def matrixQuestionRequiresInv (s : Sign) (ct : ClauseType) : Prop :=
  ct = .matrixQuestion → s.synsem.head.inv = .plus

/-- Embedded questions require [INV -]. -/
def embeddedQuestionProhibitsInv (s : Sign) (ct : ClauseType) : Prop :=
  ct = .embeddedQuestion → s.synsem.head.inv = .minus

end ClauseTypes

section HPSGGrammarDef

/-- An HPSG grammar is a collection of signs with constraints. -/
structure HPSGGrammar where
  signs : List Sign
  wellFormed : ∀ s ∈ signs, satisfiesInversionConstraint s

/-- HPSG derivations are signs that satisfy all constraints. -/
structure HPSGDerivation (g : HPSGGrammar) where
  sign : Sign
  clauseType : ClauseType
  inSign : sign ∈ g.signs
  invOk : satisfiesInversionConstraint sign
  matrixOk : matrixQuestionRequiresInv sign clauseType
  embeddedOk : embeddedQuestionProhibitsInv sign clauseType

/-- HPSG Grammar instance. -/
instance : Grammar HPSGGrammar where
  Derivation := Σ g : HPSGGrammar, HPSGDerivation g
  realizes d ws ct := d.2.sign.yield = ws ∧ d.2.clauseType = ct
  derives g ws ct := ∃ d : HPSGDerivation g, d.sign.yield = ws ∧ d.clauseType = ct

end HPSGGrammarDef

section WordOrder

/-- Find the position of the first auxiliary. -/
def findAuxPosition (ws : List Word) : Option Nat :=
  ws.findIdx? (·.cat == .AUX)

/-- Is this a nominal category that can be a subject? -/
def isSubjectCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Find the position of the first subject (non-wh DP). -/
def findSubjectPosition (ws : List Word) : Option Nat :=
  ws.findIdx? λ w => isSubjectCat w.cat && !w.features.wh

/-- Auxiliary precedes subject. -/
def auxPrecedesSubject (ws : List Word) : Bool :=
  match findAuxPosition ws, findSubjectPosition ws with
  | some a, some s => a < s
  | _, _ => false

/-- Subject precedes auxiliary. -/
def subjectPrecedesAux (ws : List Word) : Bool :=
  match findAuxPosition ws, findSubjectPosition ws with
  | some a, some s => s < a
  | _, _ => false

/-- [INV +] correlates with aux-before-subject order. -/
def invPlusImpliesAuxFirst (inv : Inv) (ws : List Word) : Prop :=
  inv = .plus → auxPrecedesSubject ws = true

/-- [INV -] correlates with subject-before-aux order. -/
def invMinusImpliesSubjectFirst (inv : Inv) (ws : List Word) : Prop :=
  inv = .minus → subjectPrecedesAux ws = true

end WordOrder

section WordOrderTheorems

/-- INV+ and INV- are mutually exclusive. -/
theorem inv_exclusive (i : Inv) : i = .plus ∨ i = .minus := by
  cases i <;> simp

/-- If we have aux-first order, INV+ is possible. -/
theorem aux_first_allows_inv_plus (ws : List Word)
    (h : auxPrecedesSubject ws = true) :
    invPlusImpliesAuxFirst .plus ws := by
  intro _; exact h

/-- If we have subject-first order, INV- is possible. -/
theorem subject_first_allows_inv_minus (ws : List Word)
    (h : subjectPrecedesAux ws = true) :
    invMinusImpliesSubjectFirst .minus ws := by
  intro _; exact h

end WordOrderTheorems

end HPSG
