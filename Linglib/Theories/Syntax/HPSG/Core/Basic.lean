/-
HPSG formalization: typed feature structures, signs, and phrase structure schemata.
@cite{pollard-sag-1994}, @cite{sag-wasow-bender-2003}, @cite{ginzburg-sag-2000}.
-/

import Linglib.Theories.Syntax.Common.Inversion

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

/-- The MODE feature on CONTENT, per @cite{sag-wasow-bender-2003} Ch. 7.

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

/-- Content features for binding theory, per @cite{sag-wasow-bender-2003} Ch. 7.

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

      Per @cite{pollard-sag-1994} Ch. 1, MOD is a HEAD feature that
      restricts what a modifier can combine with. Relative clauses
      have `[MOD NP]`; adjectives have `[MOD N]`. -/
  mod : Option UD.UPOS := none
  deriving Repr

/-- ARG-ST: the ordered list of a word's arguments, per @cite{sag-wasow-bender-2003} Ch. 7.

    ARG-ST = SPR ⊕ COMPS. Outranking is defined over position in this list:
    element i outranks element j iff i < j. -/
structure ArgSt where
  args : List Synsem := []
  deriving Repr

/-- Build ARG-ST from valence (SPR ⊕ COMPS). -/
def Valence.toArgSt (v : Valence) : ArgSt :=
  { args := (v.subj ++ v.comps).map (fun c => { cat := c : Synsem }) }

/-- Does element at position i outrank element at position j on ARG-ST?

    Per @cite{sag-wasow-bender-2003}: "X outranks Y iff X precedes Y on
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

/-- Head-Modifier Schema: head combines with a modifier.

Per @cite{sag-wasow-bender-2003} (46), a saturated head combines with
a modifier whose MOD value matches the head's category. Used for
adjective modification ("tall boy"), PP modification ("book on the table"),
and relative clauses ("book that John read"). -/
structure HeadModRule where
  headSign : Sign
  modifier : Sign
  result : Sign
  /-- The modifier's MOD value must match the head's category -/
  modMatch : modifier.synsem.mod = some (headSign.synsem.cat)
  /-- Head Feature Principle: result category = head category -/
  hfp : result.synsem.cat = headSign.synsem.cat

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

section WordOrder

/-- [INV +] correlates with aux-before-subject order. -/
def invPlusImpliesAuxFirst (inv : Inv) (ws : List Word) : Prop :=
  inv = .plus → Inversion.auxPrecedesSubject ws = true

/-- [INV -] correlates with subject-before-aux order. -/
def invMinusImpliesSubjectFirst (inv : Inv) (ws : List Word) : Prop :=
  inv = .minus → Inversion.subjectPrecedesAux ws = true

end WordOrder

end HPSG
