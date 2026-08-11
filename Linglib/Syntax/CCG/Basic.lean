import Linglib.Syntax.Category.Coordinator
import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# Combinatory Categorial Grammar (CCG)

This file defines Combinatory Categorial Grammar in its modern form
([steedman-2019]): categories whose directional slashes carry Baldridge modalities
([baldridge-2002]), the combinatory rules gated by those modalities, and
intrinsically typed derivations.

Categories are stated over an arbitrary type `α` of atomic categories, so a grammar
needing featured atoms (agreement, case) can instantiate a richer inventory than the
featureless core `CCG.Atom`. Each slash carries a `Modality` from the Baldridge
hierarchy — `dot` (unrestricted), `diamond` (order-preserving), `cross` (permuting),
`star` (application-only) — ordered by restrictiveness: a rule class indexed `m`
applies to a functor whose slash has modality `s` iff `s ≤ m`. Application is indexed
`⊤`, harmonic composition `diamond`, crossing composition `cross`; the lexicon
controls combinatory potential through the modalities it assigns, which is the modern
replacement for per-grammar rule restrictions (compare `CCG.TargetRestricted`).

Following [steedman-2019], type-raising is *morpholexical* — the work of case
morphemes, not a syntactic rule — so raised categories enter derivations as lexical
leaves (`Cat.forwardTypeRaise` builds them), and coordination is likewise lexical:
a conjunction is an ordinary entry of category `(X \⋆ X) /⋆ X` whose `star` slashes
confine it to application. Composition stops at second order, the chapter's full
inventory. The substitution rules and the morphemic slash of [steedman-2019] are not
modeled.

## Main definitions

* `Modality`: the Baldridge slash modalities, a bounded partial order (`dot = ⊥`,
  `star = ⊤`, `diamond` and `cross` incomparable).
* `Cat`: categories over an atom type `α` — atoms plus modality-carrying slashes.
* `Cat.generalizedForwardComp`, `Cat.generalizedBackwardComp`: the degree-`n`
  composition schema (modality-blind, for `CCG.TargetRestricted`).
* `Cat.forwardTypeRaise`, `Cat.backwardTypeRaise`: raised categories, for lexicons.
* `Derivation`: intrinsically typed derivations over the modern rule inventory —
  application, first- and second-order composition in harmonic and crossing variants,
  each gated on the primary slash's modality; `Derivation.yield` reads off the
  surface string, `Derivation.opCount` the number of rule applications, and
  `Derivation.HasComp` whether composition occurs.

## Notation

* `X / Y`, `X \ Y`: slashes with the unrestricted modality `dot` (absence of an
  annotation means unrestricted, as in [steedman-2019]).
* `X /⋄ Y`, `X \⋄ Y`, `X /× Y`, `X \× Y`, `X /⋆ Y`, `X \⋆ Y`: slashes with the
  annotated modality.

All are scoped to the `CCG` namespace. Because `/` overloads Lean's division,
categories are written fully parenthesized (`(S \ NP) / NP`) rather than relying on
the Steedman left-to-right reading.
-/

namespace CCG

/-! ### Slash modalities -/

/-- The Baldridge slash modalities ([baldridge-2002], [steedman-2019]), ordered by
restrictiveness: a rule class indexed `m` applies to a slash of modality `s` iff
`s ≤ m`. -/
inductive Modality where
  /-- Unrestricted (written as an unannotated slash): combines by any rule. -/
  | dot
  /-- Order-preserving `⋄`: licenses application and harmonic composition. -/
  | diamond
  /-- Permuting `×`: licenses application and crossing composition. -/
  | cross
  /-- `⋆`: licenses application only. -/
  | star
  deriving DecidableEq, Repr, Fintype

namespace Modality

instance : LE Modality where
  le a b := a = dot ∨ a = b ∨ b = star

instance : DecidableLE Modality := fun _ _ =>
  decidable_of_iff (_ = dot ∨ _ = _ ∨ _ = star) Iff.rfl

instance : PartialOrder Modality where
  le_refl _ := Or.inr (Or.inl rfl)
  le_trans := by decide
  le_antisymm := by decide

instance : BoundedOrder Modality where
  top := star
  le_top _ := Or.inr (Or.inr rfl)
  bot := dot
  bot_le _ := Or.inl rfl

end Modality

/-! ### Categories -/

/-- The core atomic categories of the English fragment (`S`, `NP`, `N`, `PP`, as in
[steedman-2000]), stated without features. -/
inductive Atom where
  /-- Sentence. -/
  | S
  /-- Noun phrase. -/
  | NP
  /-- Common noun. -/
  | N
  /-- Prepositional phrase. -/
  | PP
  deriving Repr, DecidableEq

/-- CCG categories over a type `α` of atomic categories: atoms plus directional
slashes, each carrying a `Modality`. -/
inductive Cat (α : Type*) where
  /-- An atomic category. -/
  | atom : α → Cat α
  /-- `X/ₘY`: looking right for a `Y` to give an `X`, at modality `m`. -/
  | rslash : Cat α → Modality → Cat α → Cat α
  /-- `X\ₘY`: looking left for a `Y` to give an `X`, at modality `m`. -/
  | lslash : Cat α → Modality → Cat α → Cat α
  deriving Repr, DecidableEq

scoped notation:60 X "/" Y => Cat.rslash X Modality.dot Y
scoped notation:60 X "\\" Y => Cat.lslash X Modality.dot Y
scoped notation:60 X "/⋄" Y => Cat.rslash X Modality.diamond Y
scoped notation:60 X "\\⋄" Y => Cat.lslash X Modality.diamond Y
scoped notation:60 X "/×" Y => Cat.rslash X Modality.cross Y
scoped notation:60 X "\\×" Y => Cat.lslash X Modality.cross Y
scoped notation:60 X "/⋆" Y => Cat.rslash X Modality.star Y
scoped notation:60 X "\\⋆" Y => Cat.lslash X Modality.star Y

def S : Cat Atom := .atom .S
def NP : Cat Atom := .atom .NP
def N : Cat Atom := .atom .N
def PP : Cat Atom := .atom .PP

def IV : Cat Atom := S \ NP
def TV : Cat Atom := (S \ NP) / NP
def Det : Cat Atom := NP / N

variable {α : Type*} [DecidableEq α]

namespace Cat

/-! ### The generalized composition schema -/

/-- `generalizedForwardComp n f g` is forward composition of degree `n` (`>Bⁿ`): when
`f = X/Y` and `g = Y|Z₁…|Zₙ`, the result is `X|Z₁…|Zₙ` with each argument keeping its
own slash direction and modality, and `none` otherwise. Modality-blind — the schema
of `CCG.TargetRestricted`, where rule control is per-grammar rather than lexical. -/
def generalizedForwardComp : Nat → Cat α → Cat α → Option (Cat α)
  | 0, .rslash x _ y, z => if y = z then some x else none
  | n + 1, f, .rslash g m z => (generalizedForwardComp n f g).map (Cat.rslash · m z)
  | n + 1, f, .lslash g m z => (generalizedForwardComp n f g).map (Cat.lslash · m z)
  | _, _, _ => none

/-- `generalizedBackwardComp n g f` is backward composition of degree `n` (`<Bⁿ`), the
mirror of `generalizedForwardComp`: when `g = Y|Z₁…|Zₙ` and `f = X\Y`, the result is
`X|Z₁…|Zₙ`, and `none` otherwise. -/
def generalizedBackwardComp : Nat → Cat α → Cat α → Option (Cat α)
  | 0, z, .lslash x _ y => if y = z then some x else none
  | n + 1, .rslash g m z, f => (generalizedBackwardComp n g f).map (Cat.rslash · m z)
  | n + 1, .lslash g m z, f => (generalizedBackwardComp n g f).map (Cat.lslash · m z)
  | _, _, _ => none

/-! ### Type-raising

Type-raising is morpholexical in [steedman-2019] — the work of case morphemes rather
than a syntactic rule — so these build the *categories* raised lexical entries carry;
there is no corresponding `Derivation` constructor. -/

/-- `forwardTypeRaise x t` is `t / (t \ x)` — the forward-raised (`>T`) category of
`x` at target `t`. -/
def forwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t / (t \ x)

/-- `backwardTypeRaise x t` is `t \ (t / x)` — the backward-raised (`<T`) category of
`x` at target `t`. -/
def backwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t \ (t / x)

end Cat

/-! ### Rules and derivations

The Combinatory Projection Principle ([steedman-2019]): syntactic combinatory rules
are *binary*, linearly ordered, type-dependent rules applying to string-adjacent
categories. `Rule` is the modern rule inventory as an indexed family — application,
first- and second-order composition in harmonic and crossing variants, each gated on
the primary functor's slash modality — and `Derivation` therefore needs exactly one
binary `node` constructor. Type-raising and coordination are lexical, so they
contribute leaves rather than rules; the substitution rules are not modeled. -/

/-- `Rule α l r c`: a binary combinatory rule instance combining a left constituent of
category `l` with a right constituent of category `r` to give `c`. Harmonic rules
require the primary slash's modality `≤ diamond`, crossing rules `≤ cross`;
application admits every modality. -/
inductive Rule (α : Type*) : Cat α → Cat α → Cat α → Type _ where
  /-- Forward application `>`: X/Y Y ⇒ X. -/
  | fapp {x y : Cat α} {m : Modality} : Rule α (.rslash x m y) y x
  /-- Backward application `<`: Y X\Y ⇒ X. -/
  | bapp {x y : Cat α} {m : Modality} : Rule α y (.lslash x m y) x
  /-- Forward harmonic composition `>B`: X/⋄Y Y/Z ⇒ X/Z. -/
  | fcomp {x y z : Cat α} {m n : Modality} (h : m ≤ Modality.diamond) :
      Rule α (.rslash x m y) (.rslash y n z) (.rslash x n z)
  /-- Backward harmonic composition `<B`: Y\Z X\⋄Y ⇒ X\Z. -/
  | bcomp {x y z : Cat α} {m n : Modality} (h : m ≤ Modality.diamond) :
      Rule α (.lslash y n z) (.lslash x m y) (.lslash x n z)
  /-- Forward crossing composition `>B×`: X/×Y Y\Z ⇒ X\Z. -/
  | fcompx {x y z : Cat α} {m n : Modality} (h : m ≤ Modality.cross) :
      Rule α (.rslash x m y) (.lslash y n z) (.lslash x n z)
  /-- Backward crossing composition `<B×`: Y/Z X\×Y ⇒ X/Z. -/
  | bcompx {x y z : Cat α} {m n : Modality} (h : m ≤ Modality.cross) :
      Rule α (.rslash y n z) (.lslash x m y) (.rslash x n z)
  /-- Forward second-order composition `>B²`: X/⋄Y (Y/Z)/W ⇒ (X/Z)/W. -/
  | fcomp2 {x y z w : Cat α} {m n p : Modality} (h : m ≤ Modality.diamond) :
      Rule α (.rslash x m y) (.rslash (.rslash y n z) p w) (.rslash (.rslash x n z) p w)
  /-- Backward second-order composition `<B²`: (Y\Z)\W X\⋄Y ⇒ (X\Z)\W. -/
  | bcomp2 {x y z w : Cat α} {m n p : Modality} (h : m ≤ Modality.diamond) :
      Rule α (.lslash (.lslash y n z) p w) (.lslash x m y) (.lslash (.lslash x n z) p w)
  /-- Forward crossing second-order composition `>B²×`: X/×Y (Y\Z)\W ⇒ (X\Z)\W. -/
  | fcompx2 {x y z w : Cat α} {m n p : Modality} (h : m ≤ Modality.cross) :
      Rule α (.rslash x m y) (.lslash (.lslash y n z) p w) (.lslash (.lslash x n z) p w)
  /-- Backward crossing second-order composition `<B²×`: (Y/Z)/W X\×Y ⇒ (X/Z)/W. -/
  | bcompx2 {x y z w : Cat α} {m n p : Modality} (h : m ≤ Modality.cross) :
      Rule α (.rslash (.rslash y n z) p w) (.lslash x m y) (.rslash (.rslash x n z) p w)

/-- The rule is a composition (of any order or direction) rather than an application. -/
def Rule.IsComp {l r c : Cat α} : Rule α l r c → Prop
  | .fapp => False
  | .bapp => False
  | _ => True

instance {l r c : Cat α} : ∀ ru : Rule α l r c, Decidable ru.IsComp
  | .fapp => isFalse fun h => h
  | .bapp => isFalse fun h => h
  | .fcomp _ => isTrue trivial
  | .bcomp _ => isTrue trivial
  | .fcompx _ => isTrue trivial
  | .bcompx _ => isTrue trivial
  | .fcomp2 _ => isTrue trivial
  | .bcomp2 _ => isTrue trivial
  | .fcompx2 _ => isTrue trivial
  | .bcompx2 _ => isTrue trivial

/-- A CCG derivation of category `c`, intrinsically typed: a lexical leaf, or a
binary `Rule` node — the Combinatory Projection Principle's binarity, once. A value
of `Derivation α c` *is* a well-formed derivation, so "derives `c`" is
typechecking. -/
inductive Derivation (α : Type*) : Cat α → Type _ where
  /-- A lexical leaf: a surface form, at category `c`. -/
  | lex (form : String) (c : Cat α) : Derivation α c
  /-- A binary rule application. -/
  | node {l r c : Cat α} :
      Rule α l r c → Derivation α l → Derivation α r → Derivation α c

namespace Derivation

variable {x y z w : Cat α} {m n p : Modality}

/-- Forward application `>`. -/
abbrev fapp (d₁ : Derivation α (.rslash x m y)) (d₂ : Derivation α y) :
    Derivation α x := .node .fapp d₁ d₂

/-- Backward application `<`. -/
abbrev bapp (d₁ : Derivation α y) (d₂ : Derivation α (.lslash x m y)) :
    Derivation α x := .node .bapp d₁ d₂

/-- Forward harmonic composition `>B`. -/
abbrev fcomp (h : m ≤ Modality.diamond) (d₁ : Derivation α (.rslash x m y))
    (d₂ : Derivation α (.rslash y n z)) : Derivation α (.rslash x n z) :=
  .node (.fcomp h) d₁ d₂

/-- Backward harmonic composition `<B`. -/
abbrev bcomp (h : m ≤ Modality.diamond) (d₁ : Derivation α (.lslash y n z))
    (d₂ : Derivation α (.lslash x m y)) : Derivation α (.lslash x n z) :=
  .node (.bcomp h) d₁ d₂

/-- Forward crossing composition `>B×`. -/
abbrev fcompx (h : m ≤ Modality.cross) (d₁ : Derivation α (.rslash x m y))
    (d₂ : Derivation α (.lslash y n z)) : Derivation α (.lslash x n z) :=
  .node (.fcompx h) d₁ d₂

/-- Backward crossing composition `<B×`. -/
abbrev bcompx (h : m ≤ Modality.cross) (d₁ : Derivation α (.rslash y n z))
    (d₂ : Derivation α (.lslash x m y)) : Derivation α (.rslash x n z) :=
  .node (.bcompx h) d₁ d₂

/-- Forward second-order composition `>B²`. -/
abbrev fcomp2 (h : m ≤ Modality.diamond) (d₁ : Derivation α (.rslash x m y))
    (d₂ : Derivation α (.rslash (.rslash y n z) p w)) :
    Derivation α (.rslash (.rslash x n z) p w) := .node (.fcomp2 h) d₁ d₂

/-- Backward second-order composition `<B²`. -/
abbrev bcomp2 (h : m ≤ Modality.diamond)
    (d₁ : Derivation α (.lslash (.lslash y n z) p w))
    (d₂ : Derivation α (.lslash x m y)) :
    Derivation α (.lslash (.lslash x n z) p w) := .node (.bcomp2 h) d₁ d₂

/-- Forward crossing second-order composition `>B²×`. -/
abbrev fcompx2 (h : m ≤ Modality.cross) (d₁ : Derivation α (.rslash x m y))
    (d₂ : Derivation α (.lslash (.lslash y n z) p w)) :
    Derivation α (.lslash (.lslash x n z) p w) := .node (.fcompx2 h) d₁ d₂

/-- Backward crossing second-order composition `<B²×`. -/
abbrev bcompx2 (h : m ≤ Modality.cross)
    (d₁ : Derivation α (.rslash (.rslash y n z) p w))
    (d₂ : Derivation α (.lslash x m y)) :
    Derivation α (.rslash (.rslash x n z) p w) := .node (.bcompx2 h) d₁ d₂

end Derivation

/-- The surface string a derivation spells out: its leaf forms, left to right.

Rule nodes concatenate their daughters, so the yield is independent of the
derivation's combinatory structure — the property that lets a CCG derivation witness
a string language. -/
def Derivation.yield {c : Cat α} : Derivation α c → List String
  | .lex f _ => [f]
  | .node _ d₁ d₂ => d₁.yield ++ d₂.yield

/-- The number of combinatory rule applications in a derivation. -/
def Derivation.opCount {c : Cat α} : Derivation α c → Nat
  | .lex _ _ => 0
  | .node _ d₁ d₂ => 1 + d₁.opCount + d₂.opCount

/-- The derivation contains a composition node (of any order or direction). -/
def Derivation.HasComp {c : Cat α} : Derivation α c → Prop
  | .lex _ _ => False
  | .node ru d₁ d₂ => ru.IsComp ∨ d₁.HasComp ∨ d₂.HasComp

instance Derivation.HasComp.decidable {c : Cat α} :
    ∀ d : Derivation α c, Decidable d.HasComp
  | .lex _ _ => isFalse fun h => h
  | .node _ d₁ d₂ =>
      @instDecidableOr _ _ inferInstance
        (@instDecidableOr _ _ (decidable d₁) (decidable d₂))

end CCG
