/-
# CCG-Montague Homomorphism

Syntax-semantics mapping in CCG is structure-preserving: every syntactic rule
corresponds to a semantic operation.

## Main definitions

- `TypedDeriv`: Well-typed CCG derivation with category and meaning
- `fappSem`, `bappSem`: Semantic rules for application
- `fcompSem`: Semantic rule for composition (B combinator)
- `HomomorphismProperty`: Structure encoding rule-to-rule correspondence

-/

import Linglib.Theories.Syntax.CCG.Core.Basic
import Linglib.Theories.Interfaces.SyntaxSemantics.CCG.Interface
import Linglib.Theories.Syntax.CCG.Core.Combinators
import Linglib.Core.IntensionalLogic.Frame
import Linglib.Fragments.ToyDomain

namespace CCG.Homomorphism

open CCG
open CCG.Combinators
open Core.IntensionalLogic
open Semantics.Montague

-- Well-Typed Derivations

/-- Well-typed CCG derivation with category and meaning. -/
structure TypedDeriv (F : Frame) where
  deriv : DerivStep
  cat : Cat
  catOk : deriv.cat = some cat
  meaning : F.Denot (catToTy cat)

/-- Category paired with semantic denotation. -/
structure CatMeaning (F : Frame) where
  cat : Cat
  meaning : F.Denot (catToTy cat)

/-- Forward application is semantic function application. -/
theorem fapp_sem {F : Frame} {x y : Cat}
    (f_sem : F.Denot (catToTy (x.rslash y)))
    (a_sem : F.Denot (catToTy y)) :
    -- The type of f_sem is (catToTy y ⇒ catToTy x) by definition of catToTy
    -- So f_sem a_sem has type catToTy x
    ∃ (result : F.Denot (catToTy x)), result = f_sem a_sem := by
  exact ⟨f_sem a_sem, rfl⟩

/-- Semantic rule for forward application. -/
def fappSem {F : Frame} {x y : Cat}
    (f_sem : F.Denot (catToTy (x.rslash y)))
    (a_sem : F.Denot (catToTy y)) : F.Denot (catToTy x) :=
  f_sem a_sem

/-- Forward application types align. -/
theorem fapp_types_align (x y : Cat) :
    catToTy (x.rslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Backward application is semantic function application. -/
theorem bapp_sem {F : Frame} {x y : Cat}
    (a_sem : F.Denot (catToTy y))
    (f_sem : F.Denot (catToTy (x.lslash y))) :
    ∃ (result : F.Denot (catToTy x)), result = f_sem a_sem := by
  exact ⟨f_sem a_sem, rfl⟩

/-- Semantic rule for backward application. -/
def bappSem {F : Frame} {x y : Cat}
    (a_sem : F.Denot (catToTy y))
    (f_sem : F.Denot (catToTy (x.lslash y))) : F.Denot (catToTy x) :=
  f_sem a_sem

/-- Backward application types align. -/
theorem bapp_types_align (x y : Cat) :
    catToTy (x.lslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Forward composition is the B combinator. -/
theorem fcomp_sem {F : Frame} {x y z : Cat}
    (f_sem : F.Denot (catToTy (x.rslash y)))
    (g_sem : F.Denot (catToTy (y.rslash z))) :
    -- f_sem : catToTy z → catToTy y by fapp_types_align
    -- g_sem : catToTy y → catToTy x by fapp_types_align
    -- B f_sem g_sem : catToTy z → catToTy x = catToTy (x.rslash z)
    ∃ (result : F.Denot (catToTy (x.rslash z))),
      result = B f_sem g_sem := by
  exact ⟨B f_sem g_sem, rfl⟩

/-- Semantic rule for forward composition. -/
def fcompSem {F : Frame} {x y z : Cat}
    (f_sem : F.Denot (catToTy (x.rslash y)))
    (g_sem : F.Denot (catToTy (y.rslash z)))
    : F.Denot (catToTy (x.rslash z)) :=
  B f_sem g_sem

/-- Forward type-raising is the T combinator. -/
theorem ftr_sem {F : Frame} {x t : Cat}
    (a_sem : F.Denot (catToTy x)) :
    ∃ (result : F.Denot (catToTy (forwardTypeRaise x t))),
      ∀ (f : F.Denot (catToTy (t.lslash x))),
        result f = f a_sem := by
  use λ f => f a_sem
  intro f
  rfl

/-- Semantic rule for forward type-raising. -/
def ftrSem {F : Frame} {x t : Cat}
    (a_sem : F.Denot (catToTy x))
    : F.Denot (catToTy (forwardTypeRaise x t)) :=
  λ f => f a_sem

/-- Well-formed derivations have categories. -/
def wellFormed (d : DerivStep) : Prop :=
  d.cat.isSome

/-- Lexical entries are well-formed. -/
theorem lex_wellFormed (e : LexEntry) :
    wellFormed (DerivStep.lex e) := by
  simp only [wellFormed, DerivStep.cat, Option.isSome_some]

/-- Well-formed derivations have categories. -/
theorem wellFormed_has_cat (d : DerivStep) (h : wellFormed d) :
    ∃ c : Cat, d.cat = some c := by
  simp only [wellFormed] at h
  exact Option.isSome_iff_exists.mp h

/-- Derivation meanings are unique. -/
theorem interp_deterministic (d : DerivStep) (lex : SemLexicon toyModel)
    (i1 i2 : Interp toyModel)
    (h1 : d.interp lex = some i1)
    (h2 : d.interp lex = some i2) :
    i1 = i2 := by
  rw [h1] at h2
  injection h2

/-- Homomorphism property: syntactic rules correspond to semantic operations. -/
structure HomomorphismProperty where
  fapp : ∀ {F : Frame} {x y : Cat}
    (f : F.Denot (catToTy (x.rslash y)))
    (a : F.Denot (catToTy y)),
    fappSem f a = f a
  bapp : ∀ {F : Frame} {x y : Cat}
    (a : F.Denot (catToTy y))
    (f : F.Denot (catToTy (x.lslash y))),
    bappSem a f = f a
  fcomp : ∀ {F : Frame} {x y z : Cat}
    (f : F.Denot (catToTy (x.rslash y)))
    (g : F.Denot (catToTy (y.rslash z))),
    fcompSem f g = B f g
  ftr : ∀ {F : Frame} {x t : Cat}
    (a : F.Denot (catToTy x)),
    ftrSem (x := x) (t := t) a = T a

/-- CCG-Montague homomorphism satisfies all structural properties. -/
def ccgHomomorphism : HomomorphismProperty where
  fapp := λ _ _ => rfl
  bapp := λ _ _ => rfl
  fcomp := λ _ _ => rfl
  ftr := λ _ => rfl

/-- "John sleeps" derivation structure. -/
example :
    let john_meaning : toyModel.Denot (catToTy NP) := ToyEntity.john
    let sleeps_meaning : toyModel.Denot (catToTy IV) := ToyLexicon.sleeps_sem
    bappSem john_meaning sleeps_meaning = sleeps_meaning john_meaning := rfl

/-- "sees Mary" derivation structure. -/
example :
    let sees_meaning : toyModel.Denot (catToTy TV) := ToyLexicon.sees_sem
    let mary_meaning : toyModel.Denot (catToTy NP) := ToyEntity.mary
    fappSem sees_meaning mary_meaning = sees_meaning mary_meaning := rfl

/-- "John sees Mary" derivation structure. -/
example :
    let john_meaning : toyModel.Denot (catToTy NP) := ToyEntity.john
    let sees_meaning : toyModel.Denot (catToTy TV) := ToyLexicon.sees_sem
    let mary_meaning : toyModel.Denot (catToTy NP) := ToyEntity.mary
    let sees_mary := fappSem sees_meaning mary_meaning
    let john_sees_mary := bappSem john_meaning sees_mary
    john_sees_mary := trivial

/-- Rule-to-rule relation: each syntactic rule has unique semantic rule. -/
structure RuleToRuleRelation where
  fapp_rule : ∀ {F : Frame} {x y : Cat}
    (f : F.Denot (catToTy (x.rslash y)))
    (a : F.Denot (catToTy y)),
    ∃! (result : F.Denot (catToTy x)), result = f a
  bapp_rule : ∀ {F : Frame} {x y : Cat}
    (a : F.Denot (catToTy y))
    (f : F.Denot (catToTy (x.lslash y))),
    ∃! (result : F.Denot (catToTy x)), result = f a
  comp_rule : ∀ {F : Frame} {x y z : Cat}
    (f : F.Denot (catToTy (x.rslash y)))
    (g : F.Denot (catToTy (y.rslash z))),
    ∃! (result : F.Denot (catToTy (x.rslash z))),
      ∀ arg, result arg = f (g arg)

/-- CCG satisfies rule-to-rule. -/
def ccgRuleToRule : RuleToRuleRelation where
  fapp_rule := λ f a => ⟨f a, rfl, λ _ h => h⟩
  bapp_rule := λ a f => ⟨f a, rfl, λ _ h => h⟩
  comp_rule := λ f g => ⟨λ arg => f (g arg), λ _ => rfl, λ _ h => funext h⟩

/-- Monotonic grammars preserve well-formedness. -/
def Monotonic (combine : DerivStep → DerivStep → Option DerivStep) : Prop :=
  ∀ d1 d2 d3, combine d1 d2 = some d3 →
    (d1.cat.isSome ∧ d2.cat.isSome → d3.cat.isSome)

/-- CCG has direct lexicon-to-meaning architecture. -/
structure DirectArchitecture where
  lexMeaning : LexEntry → Option (toyModel.Denot (catToTy NP) ⊕
                                   toyModel.Denot (catToTy IV) ⊕
                                   toyModel.Denot (catToTy TV))
  derivMeaning : DerivStep → Option (Interp toyModel)
  directness : ∀ d, derivMeaning d = d.interp toySemLexicon

end CCG.Homomorphism
