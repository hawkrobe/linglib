/-
HPSG formalization: typed feature structures, signs, and phrase structure schemata.
[pollard-sag-1994], [sag-wasow-bender-2003], [ginzburg-sag-2000].
-/

import Linglib.Data.UD.Basic
import Linglib.Morphology.Word.Basic

open Morphology (Word)

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

/-- The MODE feature on CONTENT, per [sag-wasow-bender-2003] Ch. 7.

    SWB2003 uses MODE to classify the semantic type of CONTENT:
    - `ref`: referential — pronouns, R-expressions, nouns
    - `ana`: anaphoric — reflexives, reciprocals
    - `prop`: propositional — declarative clauses
    - `ques`: question — interrogative clauses
    - `dir`: directive — imperative clauses
    - `noneMode`: for elements with no MODE specification -/
inductive Mode where
  | ref       -- referential: pronouns, R-expressions
  | ana       -- anaphoric: reflexives, reciprocals
  | prop      -- propositional: declarative clauses
  | ques      -- question: interrogative clauses
  | dir       -- directive: imperative clauses
  | noneMode  -- unspecified
  deriving Repr, DecidableEq

/-- Head features (shared between head and phrase). -/
structure HeadFeatures where
  vform : VForm := .finite
  inv : Inv := .minus
  aux : Bool := false
  deriving Repr, DecidableEq

/-- Content features for binding theory, per [sag-wasow-bender-2003] Ch. 7.

    SWB2003's binding theory uses MODE and ARG-ST outranking:
    - Principle A: [MODE ana] must be outranked by a coindexed element
    - Principle B: [MODE ref] must NOT be outranked by a coindexed element

    This subsumes the Chomskyan three-principle system — both pronouns and
    R-expressions are [MODE ref], so Principle B handles both. No separate
    "Principle C" is needed. -/
structure ContentFeatures where
  /-- MODE feature: ana for anaphors, ref for referential NPs -/
  mode : Mode := .ref
  /-- Referential index (for coindexation) -/
  index : Option Nat := none
  deriving Repr, DecidableEq

/-- Valence features (what arguments are needed). -/
structure Valence where
  subj : List UD.UPOS := []     -- subject requirement (SPR in SWB2003)
  comps : List UD.UPOS := []    -- complement requirements
  deriving Repr, DecidableEq

/-- The SYNSEM value (syntax-semantics bundle). -/
structure Synsem where
  cat : UD.UPOS
  head : HeadFeatures := {}
  val : Valence := {}
  cont : ContentFeatures := {}
  /-- MOD feature: what this sign modifies (none = not a modifier).

      Per [pollard-sag-1994] Ch. 1, MOD is a HEAD feature that
      restricts what a modifier can combine with. Relative clauses
      have `[MOD NP]`; adjectives have `[MOD N]`. -/
  mod : Option UD.UPOS := none
  deriving Repr

/-- ARG-ST: the ordered list of a word's arguments, per [sag-wasow-bender-2003] Ch. 7.

    ARG-ST = SPR ⊕ COMPS. Outranking is defined over position in this list:
    element i outranks element j iff i < j. -/
structure ArgSt where
  args : List Synsem := []
  deriving Repr

/-- Build ARG-ST from valence (SPR ⊕ COMPS). -/
def Valence.toArgSt (v : Valence) : ArgSt :=
  { args := (v.subj ++ v.comps).map (fun c => { cat := c : Synsem }) }

/-- Does element at position i outrank element at position j on ARG-ST?

    Per [sag-wasow-bender-2003]: "X outranks Y iff X precedes Y on
    some ARG-ST list." -/
def ArgSt.outranks (argSt : ArgSt) (i j : Nat) : Bool :=
  i < j && j < argSt.args.length

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

end HPSG
