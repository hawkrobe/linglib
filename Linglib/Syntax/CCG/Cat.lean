import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# CCG categories

This file defines the categories of Combinatory Categorial Grammar in their modern
form ([steedman-2019]): atoms plus directional slashes, each slash carrying a
Baldridge modality ([baldridge-2002]) — the shared substrate of the rule theory
(`Syntax/CCG/Derivation`) and the capacity theory (`Syntax/CCG/Grammar`).

Categories are stated over an arbitrary type `α` of atomic categories, so a grammar
needing featured atoms (agreement, case) can instantiate a richer inventory than the
featureless core `CCG.Atom`. Each slash carries a `Modality` from the Baldridge
hierarchy — `dot` (unrestricted), `diamond` (order-preserving), `cross` (permuting),
`star` (application-only) — ordered by restrictiveness: a rule class indexed `m`
applies to a functor whose slash has modality `s` iff `s ≤ m`. The lexicon controls
combinatory potential through the modalities it assigns, the modern replacement for
per-grammar rule restrictions (compare `CCG.Grammar`).

## Main definitions

* `Modality`: the Baldridge slash modalities, a bounded partial order (`dot = ⊥`,
  `star = ⊤`, `diamond` and `cross` incomparable).
* `Cat`: categories over an atom type `α` — atoms plus modality-carrying slashes.
* `Cat.generalizedForwardComp`, `Cat.generalizedBackwardComp`: the degree-`n`
  composition schema (modality-blind, for `CCG.Grammar`).
* `Cat.forwardTypeRaise`, `Cat.backwardTypeRaise`: raised categories, for lexicons.
* `Cat.target`: a category's leftmost atom, the locus of per-grammar rule
  restrictions.

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

/-- The modality a slash carries, determining which rule classes it licenses. The
order is reverse inclusion of licenses — `s ≤ m` iff `s` licenses every rule class
`m` does — so composition gates on `s ≤ diamond` (harmonic) and `s ≤ cross`
(crossing), while application is licensed by every modality (`s ≤ ⊤`). -/
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
of the grammars in `Syntax/CCG/Grammar`, where rule control is per-grammar rather
than lexical. -/
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

/-! ### Targets

Each category has a *target* — its leftmost atom, "similar to the return type of a
function" ([steedman-2019]) — the locus of the per-grammar rule restrictions of
`Syntax/CCG/Grammar`. -/

/-- The target of a category: its leftmost atom, after stripping all arguments. -/
def target : Cat α → α
  | .atom a => a
  | .rslash x _ _ => target x
  | .lslash x _ _ => target x

@[simp] theorem target_atom (a : α) : target (Cat.atom a) = a := rfl

@[simp] theorem target_rslash (x y : Cat α) (m : Modality) :
    target (Cat.rslash x m y) = target x := rfl

@[simp] theorem target_lslash (x y : Cat α) (m : Modality) :
    target (Cat.lslash x m y) = target x := rfl

end Cat

end CCG
