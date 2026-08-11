import Linglib.Syntax.CCG.Cat

/-!
# CCG derivations

This file defines the modern rule theory of CCG ([steedman-2019]): the combinatory
rules as an indexed family, and intrinsically typed derivations over them.

The Combinatory Projection Principle: syntactic combinatory rules are *binary*,
linearly ordered, type-dependent rules applying to string-adjacent categories.
`Rule` is the modern rule inventory — application, first- and second-order
composition in harmonic and crossing variants, each gated on the primary functor's
slash modality — and `Derivation` therefore needs exactly one binary `node`
constructor, so a value of `Derivation α c` *is* a derivation of category `c` and
"derives `c`" is typechecking. Following [steedman-2019], type-raising is
*morpholexical* — the work of case morphemes, not a syntactic rule — so raised
categories enter as lexical leaves, and coordination is likewise lexical: a
conjunction is an ordinary entry of category `(X \⋆ X) /⋆ X` whose `star` slashes
confine it to application. Composition stops at second order, the chapter's full
inventory. The substitution rules and the morphemic slash of [steedman-2019] are
not modeled.

## Main definitions

* `Rule`: the binary combinatory rules, indexed by left input, right input, and
  result category.
* `Derivation`: intrinsically typed derivations — a lexical leaf or a binary `Rule`
  node; `Derivation.yield` reads off the surface string, `Derivation.opCount` the
  number of rule applications, and `Derivation.HasComp` whether composition occurs.
-/

namespace CCG

variable {α : Type*} [DecidableEq α]

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

/-- The surface string a derivation spells out: its leaf forms, left to right.

Rule nodes concatenate their daughters, so the yield is independent of the
derivation's combinatory structure — the property that lets a CCG derivation witness
a string language. -/
def yield {c : Cat α} : Derivation α c → List String
  | .lex f _ => [f]
  | .node _ d₁ d₂ => d₁.yield ++ d₂.yield

/-- The number of combinatory rule applications in a derivation. -/
def opCount {c : Cat α} : Derivation α c → Nat
  | .lex _ _ => 0
  | .node _ d₁ d₂ => 1 + d₁.opCount + d₂.opCount

/-- The derivation contains a composition node (of any order or direction). -/
def HasComp {c : Cat α} : Derivation α c → Prop
  | .lex _ _ => False
  | .node ru d₁ d₂ => ru.IsComp ∨ d₁.HasComp ∨ d₂.HasComp

instance HasComp.decidable {c : Cat α} : ∀ d : Derivation α c, Decidable d.HasComp
  | .lex _ _ => isFalse fun h => h
  | .node _ d₁ d₂ =>
      @instDecidableOr _ _ inferInstance
        (@instDecidableOr _ _ (decidable d₁) (decidable d₂))

end Derivation

end CCG
