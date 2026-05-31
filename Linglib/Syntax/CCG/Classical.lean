import Linglib.Syntax.CCG.Basic

/-!
# Classical (rule-restricted) CCG

The *classical* CCG formalism of @cite{vijay-shanker-weir-1994} and @cite{weir-joshi-1988},
in which combinatory rules may be **restricted per grammar**. Following
@cite{kuhlmann-koller-satta-2015}, the restriction modelled here is a **target
restriction**: a rule fires only when the *target* of its primary input category (the
leftmost atom, after stripping all arguments) is the distinguished atom `S`.

This is the substrate that makes the CCG≡TAG weak-equivalence — and constructions of CCGs
for non-context-free languages — expressible. It is distinct from the *unrestricted*,
universal-rule CCG of `Syntax/CCG/Basic` (`CCG.DerivStep`), which @cite{kuhlmann-koller-satta-2015}
show is strictly weaker than TAG.

## Main definitions

- `CCG.Classical.target` / `targetIsS` — the target of a category, and the restriction.
- `fapp`, `bapp`, `fcomp1`, `fcomp2`, `fcompX1` — application and (harmonic/crossed)
  composition, each gated on `target (primary) = S`.
- `CCG.Classical.RDeriv` — a derivation under these restricted rules, with `cat`/`yield`.

## Implementation notes

The rule set here (application; harmonic composition of degree 1–2; crossed composition
of degree 1) is the fragment used by the constructions in `Studies/KuhlmannKollerSatta2015`
and `Syntax/CCG/CrossSerial`. The target restriction is fixed to `S`, the common case in
@cite{kuhlmann-koller-satta-2015} Example 2 and in @cite{steedman-2000}; general VW-CCG
permits other per-grammar restrictions.
-/

namespace CCG.Classical

open CCG

/-- The target of a category: its leftmost atom (strip all arguments). -/
def target : Cat → Atom
  | .atom a => a
  | .rslash x _ => target x
  | .lslash x _ => target x

/-- Whether a category's target is the distinguished atom `S`. -/
def targetIsS (c : Cat) : Bool :=
  match target c with
  | .S => true
  | _ => false

@[simp] theorem targetIsS_rslash (x y : Cat) : targetIsS (.rslash x y) = targetIsS x := rfl

@[simp] theorem targetIsS_lslash (x y : Cat) : targetIsS (.lslash x y) = targetIsS x := rfl

/-! ### Rule-restricted combinatory rules

Each rule is gated on `target (primary) = S` (the target restriction of
@cite{kuhlmann-koller-satta-2015}, Example 2). -/

/-- Forward application: `(X/Y) Y ⇒ X`, target of the functor `S`. -/
def fapp : Cat → Cat → Option Cat
  | p@(.rslash x y), z => if targetIsS p && y == z then some x else none
  | _, _ => none

/-- Backward application: `Y (X\Y) ⇒ X`, target of the functor `S`. -/
def bapp : Cat → Cat → Option Cat
  | y, p@(.lslash x y') => if targetIsS p && y == y' then some x else none
  | _, _ => none

/-- Forward composition, degree 1 (harmonic): `(X/Y) (Y/Z) ⇒ X/Z`, target `S`. -/
def fcomp1 : Cat → Cat → Option Cat
  | p@(.rslash x y), .rslash y' z =>
      if targetIsS p && y == y' then some (.rslash x z) else none
  | _, _ => none

/-- Forward composition, degree 2 (harmonic): `(X/Y) (Y/Z/W) ⇒ X/Z/W`, target `S`. -/
def fcomp2 : Cat → Cat → Option Cat
  | p@(.rslash x y), .rslash (.rslash y' z) w =>
      if targetIsS p && y == y' then some (.rslash (.rslash x z) w) else none
  | _, _ => none

/-- Forward crossed composition, degree 1: `(X/Y) (Y\Z) ⇒ X\Z`, target `S`. -/
def fcompX1 : Cat → Cat → Option Cat
  | p@(.rslash x y), .lslash y' z =>
      if targetIsS p && y == y' then some (.lslash x z) else none
  | _, _ => none

/-! ### Derivations -/

/-- A derivation under the rule-restricted rules. -/
inductive RDeriv where
  | lex : Cat → String → RDeriv
  | fa : RDeriv → RDeriv → RDeriv
  | ba : RDeriv → RDeriv → RDeriv
  | fc1 : RDeriv → RDeriv → RDeriv
  | fc2 : RDeriv → RDeriv → RDeriv
  | fcx1 : RDeriv → RDeriv → RDeriv

/-- The category derived, threading the restricted rules (`none` if any rule is illegal,
e.g. its target restriction fails). -/
def RDeriv.cat : RDeriv → Option Cat
  | .lex c _ => some c
  | .fa l r => do let a ← l.cat; let b ← r.cat; fapp a b
  | .ba l r => do let a ← l.cat; let b ← r.cat; bapp a b
  | .fc1 l r => do let a ← l.cat; let b ← r.cat; fcomp1 a b
  | .fc2 l r => do let a ← l.cat; let b ← r.cat; fcomp2 a b
  | .fcx1 l r => do let a ← l.cat; let b ← r.cat; fcompX1 a b

/-- Surface string: leaf forms left to right. -/
def RDeriv.yield : RDeriv → List String
  | .lex _ s => [s]
  | .fa l r => l.yield ++ r.yield
  | .ba l r => l.yield ++ r.yield
  | .fc1 l r => l.yield ++ r.yield
  | .fc2 l r => l.yield ++ r.yield
  | .fcx1 l r => l.yield ++ r.yield

end CCG.Classical
