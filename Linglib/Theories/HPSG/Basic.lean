/-
HPSG formalization: typed feature structures, signs, and phrase structure schemata.
Pollard & Sag (1994), Sag, Wasow & Bender (2003), Ginzburg & Sag (2000).
-/

import Linglib.Core.Basic

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

/-- Head features (shared between head and phrase). -/
structure HeadFeatures where
  vform : VForm := .finite
  inv : Bool := false      -- key for subject-aux inversion
  aux : Bool := false      -- is this an auxiliary?
  deriving Repr, DecidableEq

/-- Valence features (what arguments are needed). -/
structure Valence where
  subj : List Cat := []     -- subject requirement
  comps : List Cat := []    -- complement requirements
  deriving Repr, DecidableEq

/-- The SYNSEM value (syntax-semantics bundle). -/
structure Synsem where
  cat : Cat
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

/-- Head-Subject Schema: phrase combines with its subject. -/
structure HeadSubjRule where
  subj : Sign
  headPhrase : Sign
  result : Sign
  subjMatch : (headPhrase.synsem.val.subj = [subj.synsem.cat])

end Schemata

section InversionConstraint

/-- [INV +] requires aux-initial; [INV -] requires subject-initial. -/
def satisfiesInversionConstraint (s : Sign) : Prop :=
  match s with
  | .phrase children ss =>
    if ss.head.inv then
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
  ct = .matrixQuestion → s.synsem.head.inv = true

/-- Embedded questions require [INV -]. -/
def embeddedQuestionProhibitsInv (s : Sign) (ct : ClauseType) : Prop :=
  ct = .embeddedQuestion → s.synsem.head.inv = false

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

end HPSG
