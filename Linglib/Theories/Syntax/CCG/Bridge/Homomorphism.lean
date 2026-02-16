/-
# CCG-Montague Homomorphism

Syntax-semantics mapping in CCG is structure-preserving: every syntactic rule
corresponds to a semantic operation.

## Main definitions

- `TypedDeriv`: Well-typed CCG derivation with category and meaning
- `fappSem`, `bappSem`: Semantic rules for application
- `fcompSem`: Semantic rule for composition (B combinator)
- `HomomorphismProperty`: Structure encoding rule-to-rule correspondence

## References

- Steedman (2000). The Syntactic Process.
- Montague (1973). The Proper Treatment of Quantification.
-/

import Linglib.Theories.Syntax.CCG.Core.Basic
import Linglib.Theories.Syntax.CCG.Bridge.Interface
import Linglib.Theories.Syntax.CCG.Core.Combinators
import Linglib.Theories.Semantics.Compositional.Basic

namespace CCG.Homomorphism

open CCG
open CCG.Combinators
open TruthConditional

-- Well-Typed Derivations

/-- Well-typed CCG derivation with category and meaning. -/
structure TypedDeriv (m : Model) where
  deriv : DerivStep
  cat : Cat
  catOk : deriv.cat = some cat
  meaning : m.interpTy (catToTy cat)

/-- Category paired with semantic denotation. -/
structure CatMeaning (m : Model) where
  cat : Cat
  meaning : m.interpTy (catToTy cat)

/-- Forward application is semantic function application. -/
theorem fapp_sem {m : Model} {x y : Cat}
    (f_sem : m.interpTy (catToTy (x.rslash y)))
    (a_sem : m.interpTy (catToTy y)) :
    -- The type of f_sem is (catToTy y ⇒ catToTy x) by definition of catToTy
    -- So f_sem a_sem has type catToTy x
    ∃ (result : m.interpTy (catToTy x)), result = f_sem a_sem := by
  exact ⟨f_sem a_sem, rfl⟩

/-- Semantic rule for forward application. -/
def fappSem {m : Model} {x y : Cat}
    (f_sem : m.interpTy (catToTy (x.rslash y)))
    (a_sem : m.interpTy (catToTy y)) : m.interpTy (catToTy x) :=
  f_sem a_sem

/-- Forward application types align. -/
theorem fapp_types_align (x y : Cat) :
    catToTy (x.rslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Backward application is semantic function application. -/
theorem bapp_sem {m : Model} {x y : Cat}
    (a_sem : m.interpTy (catToTy y))
    (f_sem : m.interpTy (catToTy (x.lslash y))) :
    ∃ (result : m.interpTy (catToTy x)), result = f_sem a_sem := by
  exact ⟨f_sem a_sem, rfl⟩

/-- Semantic rule for backward application. -/
def bappSem {m : Model} {x y : Cat}
    (a_sem : m.interpTy (catToTy y))
    (f_sem : m.interpTy (catToTy (x.lslash y))) : m.interpTy (catToTy x) :=
  f_sem a_sem

/-- Backward application types align. -/
theorem bapp_types_align (x y : Cat) :
    catToTy (x.lslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Forward composition is the B combinator. -/
theorem fcomp_sem {m : Model} {x y z : Cat}
    (f_sem : m.interpTy (catToTy (x.rslash y)))
    (g_sem : m.interpTy (catToTy (y.rslash z))) :
    -- f_sem : catToTy z → catToTy y by fapp_types_align
    -- g_sem : catToTy y → catToTy x by fapp_types_align
    -- B f_sem g_sem : catToTy z → catToTy x = catToTy (x.rslash z)
    ∃ (result : m.interpTy (catToTy (x.rslash z))),
      result = B f_sem g_sem := by
  exact ⟨B f_sem g_sem, rfl⟩

/-- Semantic rule for forward composition. -/
def fcompSem {m : Model} {x y z : Cat}
    (f_sem : m.interpTy (catToTy (x.rslash y)))
    (g_sem : m.interpTy (catToTy (y.rslash z)))
    : m.interpTy (catToTy (x.rslash z)) :=
  B f_sem g_sem

/-- Forward type-raising is the T combinator. -/
theorem ftr_sem {m : Model} {x t : Cat}
    (a_sem : m.interpTy (catToTy x)) :
    ∃ (result : m.interpTy (catToTy (forwardTypeRaise x t))),
      ∀ (f : m.interpTy (catToTy (t.lslash x))),
        result f = f a_sem := by
  use λ f => f a_sem
  intro f
  rfl

/-- Semantic rule for forward type-raising. -/
def ftrSem {m : Model} {x t : Cat}
    (a_sem : m.interpTy (catToTy x))
    : m.interpTy (catToTy (forwardTypeRaise x t)) :=
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
  fapp : ∀ {m : Model} {x y : Cat}
    (f : m.interpTy (catToTy (x.rslash y)))
    (a : m.interpTy (catToTy y)),
    fappSem f a = f a
  bapp : ∀ {m : Model} {x y : Cat}
    (a : m.interpTy (catToTy y))
    (f : m.interpTy (catToTy (x.lslash y))),
    bappSem a f = f a
  fcomp : ∀ {m : Model} {x y z : Cat}
    (f : m.interpTy (catToTy (x.rslash y)))
    (g : m.interpTy (catToTy (y.rslash z))),
    fcompSem f g = B f g
  ftr : ∀ {m : Model} {x t : Cat}
    (a : m.interpTy (catToTy x)),
    ftrSem (x := x) (t := t) a = T a

/-- CCG-Montague homomorphism satisfies all structural properties. -/
def ccgHomomorphism : HomomorphismProperty where
  fapp := λ _ _ => rfl
  bapp := λ _ _ => rfl
  fcomp := λ _ _ => rfl
  ftr := λ _ => rfl

/-- "John sleeps" derivation structure. -/
example :
    let john_meaning : toyModel.interpTy (catToTy NP) := ToyEntity.john
    let sleeps_meaning : toyModel.interpTy (catToTy IV) := ToyLexicon.sleeps_sem
    bappSem john_meaning sleeps_meaning = sleeps_meaning john_meaning := rfl

/-- "sees Mary" derivation structure. -/
example :
    let sees_meaning : toyModel.interpTy (catToTy TV) := ToyLexicon.sees_sem
    let mary_meaning : toyModel.interpTy (catToTy NP) := ToyEntity.mary
    fappSem sees_meaning mary_meaning = sees_meaning mary_meaning := rfl

/-- "John sees Mary" derivation structure. -/
example :
    let john_meaning : toyModel.interpTy (catToTy NP) := ToyEntity.john
    let sees_meaning : toyModel.interpTy (catToTy TV) := ToyLexicon.sees_sem
    let mary_meaning : toyModel.interpTy (catToTy NP) := ToyEntity.mary
    let sees_mary := fappSem sees_meaning mary_meaning
    let john_sees_mary := bappSem john_meaning sees_mary
    john_sees_mary = true := rfl

/-- Rule-to-rule relation: each syntactic rule has unique semantic rule. -/
structure RuleToRuleRelation where
  fapp_rule : ∀ {m : Model} {x y : Cat}
    (f : m.interpTy (catToTy (x.rslash y)))
    (a : m.interpTy (catToTy y)),
    ∃! (result : m.interpTy (catToTy x)), result = f a
  bapp_rule : ∀ {m : Model} {x y : Cat}
    (a : m.interpTy (catToTy y))
    (f : m.interpTy (catToTy (x.lslash y))),
    ∃! (result : m.interpTy (catToTy x)), result = f a
  comp_rule : ∀ {m : Model} {x y z : Cat}
    (f : m.interpTy (catToTy (x.rslash y)))
    (g : m.interpTy (catToTy (y.rslash z))),
    ∃! (result : m.interpTy (catToTy (x.rslash z))),
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
  lexMeaning : LexEntry → Option (toyModel.interpTy (catToTy NP) ⊕
                                   toyModel.interpTy (catToTy IV) ⊕
                                   toyModel.interpTy (catToTy TV))
  derivMeaning : DerivStep → Option (Interp toyModel)
  directness : ∀ d, derivMeaning d = d.interp toySemLexicon

end CCG.Homomorphism
