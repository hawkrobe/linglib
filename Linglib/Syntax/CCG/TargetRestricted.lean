import Linglib.Syntax.CCG.Basic

/-!
# Target-restricted CCG

This file defines the target-restricted variant of CCG — the formalism of
[vijay-shanker-weir-1994] and [weir-joshi-1988], "VW-CCG" in
[kuhlmann-koller-satta-2015]'s terminology — in which combinatory rules are
restricted per grammar, rather than by the lexicalized slash modalities of the
modern theory (`Syntax/CCG/Basic`). The restriction modelled is the one
[kuhlmann-koller-satta-2015]'s generative-capacity results turn on, a *target
restriction*: a rule fires only when the target of its primary input category (the
leftmost atom, after stripping all arguments) is a distinguished atom `s`.

Rules are the generalized-composition schema `CCG.Cat.generalizedForwardComp` /
`CCG.Cat.generalizedBackwardComp`, gated on the target: a derivation node records
only its degree and direction, per the [vijay-shanker-weir-1994] rule form — degree
0 is application, and the harmonic/crossed distinction is a consequence of the slash
directions rather than a separate rule class. The schema is modality-blind (VW-CCG
predates slash typing); grammars instantiate categories at the unrestricted
modality.

The two rule-control mechanisms differ in expressive power
([kuhlmann-koller-satta-2015]): with target restrictions VW-CCG is weakly equivalent
to TAG, without them it is strictly weaker, and the slash-typing variant is likewise
slightly less expressive than TAG. This file is the substrate for the equivalence
side — the constructions of CCGs for non-context-free languages in
`Studies/KuhlmannKollerSatta2015`.

## Main definitions

* `CCG.TargetRestricted.target`: the target of a category — its leftmost atom.
* `CCG.TargetRestricted.Derivation`: a raw derivation tree whose nodes record degree
  and direction; `Derivation.cat s` reads off its category under the target
  restriction to `s`, and `Derivation.yield` its surface string.

## Implementation notes

`Derivation` is deliberately extrinsic, in contrast to the intrinsically typed
`CCG.Derivation`: the generative-capacity results quantify over candidate trees, so
well-formedness is the proposition `d.cat s = some c` rather than a typing fact.
-/

namespace CCG.TargetRestricted

open CCG

variable {α : Type*}

/-- The target of a category: its leftmost atom (strip all arguments). -/
def target : Cat α → α
  | .atom a => a
  | .rslash x _ _ => target x
  | .lslash x _ _ => target x

@[simp] theorem target_atom (a : α) : target (Cat.atom a) = a := rfl

@[simp] theorem target_rslash (x y : Cat α) (m : Modality) :
    target (Cat.rslash x m y) = target x := rfl

@[simp] theorem target_lslash (x y : Cat α) (m : Modality) :
    target (Cat.lslash x m y) = target x := rfl

/-- A raw derivation tree over the degree-`n` composition schema: nodes record degree
and direction only; well-formedness under a target restriction is read off by
`Derivation.cat`. -/
inductive Derivation (α : Type*) where
  /-- A lexical leaf: a surface form at a category. -/
  | lex : String → Cat α → Derivation α
  /-- Forward composition of degree `n` (`>Bⁿ`; degree 0 is application). -/
  | fc : Nat → Derivation α → Derivation α → Derivation α
  /-- Backward composition of degree `n` (`<Bⁿ`; degree 0 is application). -/
  | bc : Nat → Derivation α → Derivation α → Derivation α
  deriving Repr

/-- The category derived under the target restriction to `s`: each rule fires only when
the target of its primary (functor) input is `s` (`none` otherwise, or if the schema
does not apply). -/
def Derivation.cat [DecidableEq α] (s : α) : Derivation α → Option (Cat α)
  | .lex _ c => some c
  | .fc n l r => do
    let a ← l.cat s
    let b ← r.cat s
    if target a = s then Cat.generalizedForwardComp n a b else none
  | .bc n l r => do
    let a ← l.cat s
    let b ← r.cat s
    if target b = s then Cat.generalizedBackwardComp n a b else none

/-- Surface string: leaf forms left to right. -/
def Derivation.yield : Derivation α → List String
  | .lex w _ => [w]
  | .fc _ l r | .bc _ l r => l.yield ++ r.yield

end CCG.TargetRestricted
