import Linglib.Syntax.CCG.Basic

/-!
# Target-restricted CCG

The CCG formalism of [vijay-shanker-weir-1994] and [weir-joshi-1988] ("VW-CCG" in
[kuhlmann-koller-satta-2015]'s terminology), in which combinatory rules may be
**restricted per grammar**. The restriction modelled here is the one
[kuhlmann-koller-satta-2015]'s generative-capacity results turn on, a **target
restriction**: a rule fires only when the *target* of its primary input category (the
leftmost atom, after stripping all arguments) is a distinguished atom `s` — their
equivalence-with-TAG theorem needs it, and without it the power drops strictly below
TAG.

Rules are the degree-`n` composition schema `CCG.forwardCompN` / `CCG.backwardCompN`
of `Syntax/CCG/Basic`, gated on the target — a derivation node records only its degree
and direction, per the [vijay-shanker-weir-1994] rule form (degree 0 is application;
the harmonic/crossed distinction is a consequence of the slash directions, not a
separate rule class).

This is the substrate that makes the CCG≡TAG weak-equivalence — and constructions of
CCGs for non-context-free languages — expressible. It is distinct from the
*unrestricted*, universal-rule CCG of `Syntax/CCG/Basic` (`CCG.DerivStep`), which
[kuhlmann-koller-satta-2015] show is strictly weaker than TAG.

## Main definitions

- `CCG.TargetRestricted.target` — the target of a category: its leftmost atom.
- `CCG.TargetRestricted.Derivation` — a derivation tree whose nodes record degree and
  direction; `Derivation.cat s` reads off its category under the target restriction
  to `s`, and `Derivation.yield` its surface string.
-/

namespace CCG.TargetRestricted

open CCG

variable {α : Type*}

/-- The target of a category: its leftmost atom (strip all arguments). -/
def target : Cat α → α
  | .atom a => a
  | .rslash x _ => target x
  | .lslash x _ => target x

@[simp] theorem target_atom (a : α) : target (Cat.atom a) = a := rfl

@[simp] theorem target_rslash (x y : Cat α) : target (Cat.rslash x y) = target x := rfl

@[simp] theorem target_lslash (x y : Cat α) : target (Cat.lslash x y) = target x := rfl

/-- A derivation under the rule-restricted degree-`n` composition schema: nodes record
degree and direction only. -/
inductive Derivation (α : Type*) where
  /-- A lexical leaf: category and surface form. -/
  | lex : Cat α → String → Derivation α
  /-- Forward composition of degree `n` (`>Bⁿ`; degree 0 is application). -/
  | fc : Nat → Derivation α → Derivation α → Derivation α
  /-- Backward composition of degree `n` (`<Bⁿ`; degree 0 is application). -/
  | bc : Nat → Derivation α → Derivation α → Derivation α
  deriving Repr

/-- The category derived under the target restriction to `s`: each rule fires only when
the target of its primary (functor) input is `s` (`none` otherwise, or if the schema
does not apply). -/
def Derivation.cat [DecidableEq α] (s : α) : Derivation α → Option (Cat α)
  | .lex c _ => some c
  | .fc n l r => do
    let a ← l.cat s
    let b ← r.cat s
    if target a = s then forwardCompN n a b else none
  | .bc n l r => do
    let a ← l.cat s
    let b ← r.cat s
    if target b = s then backwardCompN n a b else none

/-- Surface string: leaf forms left to right. -/
def Derivation.yield : Derivation α → List String
  | .lex _ w => [w]
  | .fc _ l r | .bc _ l r => l.yield ++ r.yield

end CCG.TargetRestricted
