import Linglib.Syntax.CCG.Basic
import Linglib.Semantics.Intensional.Defs
import Linglib.Semantics.Intensional.Conjunction
import Linglib.Semantics.Composition.CoordinatorOp
import Linglib.Semantics.Composition.Combinator

/-!
# CCG Syntax-Semantics Interface

This file defines the compositional interpretation of CCG derivations. Categories
encode semantic types (`catToTy`), and because `Derivation` is intrinsically typed,
`Derivation.interp` needs no run-time category checks and no casts: application is
function application, composition is the `B` combinator, type-raising is the `T`
combinator, and coordination is generalized conjunction ([partee-rooth-1983],
[steedman-2000]). A lexicon is well-typed by construction — it returns meanings at
the queried category — so soundness of the interface is a typing fact rather than a
theorem.

## Main definitions

* `catToTy`: maps CCG categories to semantic types.
* `SemLexicon`: a semantic lexicon — for each word and category, optionally a meaning
  at that category.
* `Derivation.interp`: the meaning of a derivation of category `c`, at type
  `catToTy c`; `none` only when a word is missing from the lexicon or a coordination
  is at a non-conjoinable type.

## Main statements

* `Derivation.interp_fcomp_assoc`, `Derivation.interp_fapp_fcomp` (and backward
  mirrors): spurious ambiguity — reassociating a composition-application chain cannot
  change a constituent's interpretation ([steedman-2000]; the matching-entry tests of
  [karttunen-1989] and [pareschi-steedman-1987] exploit exactly this invariance).

Worked toy-fragment derivations and the non-constituent-coordination semantics
theorems live in `Studies/Steedman2000.lean`.
-/

namespace CCG

open Intensional
open Intensional.Conjunction
open Combinator

/-! ### Type correspondence -/

/-- Map CCG categories to semantic types -/
def catToTy : Cat Atom → Ty
  | .atom .S => .t
  | .atom .NP => .e
  | .atom .N => .e ⇒ .t    -- common nouns are properties
  | .atom .PP => .e ⇒ .t   -- PPs are modifiers (simplified)
  | .rslash x y => catToTy y ⇒ catToTy x
  | .lslash x y => catToTy y ⇒ catToTy x

/-- Forward application preserves semantic typing:
    if X/Y combines with Y to give X, then (σ→τ) applied to σ gives τ. -/
theorem forward_app_type_preservation (x y : Cat Atom) :
    catToTy (x.rslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Backward application preserves semantic typing:
    if Y combines with X\Y to give X, then (σ→τ) applied to σ gives τ. -/
theorem backward_app_type_preservation (x y : Cat Atom) :
    catToTy (x.lslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Type correspondence for transitive verbs -/
theorem tv_type_is_relation :
    catToTy TV = (.e ⇒ .e ⇒ .t) := rfl

/-- Type correspondence for intransitive verbs -/
theorem iv_type_is_property :
    catToTy IV = (.e ⇒ .t) := rfl

/-- Type correspondence for forward type-raising: `T/(T\X)` denotes a function over
`X`-seeking functions. -/
theorem forward_type_raise_type (x t : Cat Atom) :
    catToTy (x.forwardTypeRaise t) = ((catToTy x ⇒ catToTy t) ⇒ catToTy t) := rfl

/-- Type correspondence for backward type-raising, identical to the forward case. -/
theorem backward_type_raise_type (x t : Cat Atom) :
    catToTy (x.backwardTypeRaise t) = ((catToTy x ⇒ catToTy t) ⇒ catToTy t) := rfl

/-! ### Derivation interpretation -/

/-- Semantic lexicon: for each word and queried category, optionally a meaning at that
category — well-typed by construction. -/
def SemLexicon (E W : Type) := String → (c : Cat Atom) → Option (Denot E W (catToTy c))

/-- Interpret a derivation compositionally: application is function application,
composition is the `B` combinator, type-raising is the `T` combinator, and
coordination is `Coordinator.engineOp` of the carried coordinator's `role`
(generalized conjunction [partee-rooth-1983] at `.j`), restricted to conjoinable
types. The category bookkeeping is carried by `Derivation`'s index, so no run-time
category checks (and no casts) are needed; the result is `none` only when a word is
missing from the lexicon or a coordination is at a non-conjoinable type. -/
def Derivation.interp {E W : Type} (lex : SemLexicon E W) :
    {c : Cat Atom} → Derivation Atom c → Option (Denot E W (catToTy c))
  | _, .lex e => lex e.form e.cat
  | _, .fapp d1 d2 => do
      let m1 ← d1.interp lex
      let m2 ← d2.interp lex
      some (m1 m2)
  | _, .bapp d1 d2 => do
      let m1 ← d1.interp lex
      let m2 ← d2.interp lex
      some (m2 m1)
  | _, .fcomp d1 d2 => do
      let m1 ← d1.interp lex
      let m2 ← d2.interp lex
      some (B m1 m2)
  | _, .bcomp d1 d2 => do
      let m1 ← d1.interp lex
      let m2 ← d2.interp lex
      some (B m2 m1)
  | _, .fcompx d1 d2 => do
      let m1 ← d1.interp lex
      let m2 ← d2.interp lex
      some (B m1 m2)
  | _, .ftr d _ => do
      let m ← d.interp lex
      some (T m)
  | _, .btr d _ => do
      let m ← d.interp lex
      some (T m)
  | x, .coord co d1 d2 => do
      let m1 ← d1.interp lex
      let m2 ← d2.interp lex
      if (catToTy x).isConjoinable then
        some (Coordinator.engineOp co.role (catToTy x) E W m1 m2)
      else none

/-! ### Spurious ambiguity

Composition is semantically associative, so left- and right-branching derivations of
the same composition-application chain receive the same interpretation — with no
assumption on the lexicon. This is the local source of CCG's "spurious ambiguity"
([steedman-2000]; the matching-entry tests of [karttunen-1989] and
[pareschi-steedman-1987] exploit exactly this invariance): a chart parser may keep
one derivation per equivalence class, because reassociating `fcomp`/`fapp` (or
`bcomp`/`bapp`) nodes cannot change what a constituent means. -/

/-- Reassociating a forward-composition chain preserves interpretation: `B` is
semantically associative. -/
theorem Derivation.interp_fcomp_assoc {E W : Type} (lex : SemLexicon E W)
    {x y z w : Cat Atom} (d₁ : Derivation Atom (x / y)) (d₂ : Derivation Atom (y / z))
    (d₃ : Derivation Atom (z / w)) :
    (Derivation.fcomp (.fcomp d₁ d₂) d₃).interp lex
      = (Derivation.fcomp d₁ (.fcomp d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

/-- Composing before applying is the same as applying twice: `B f g x = f (g x)`,
lifted to derivations. -/
theorem Derivation.interp_fapp_fcomp {E W : Type} (lex : SemLexicon E W)
    {x y z : Cat Atom} (d₁ : Derivation Atom (x / y)) (d₂ : Derivation Atom (y / z))
    (d₃ : Derivation Atom z) :
    (Derivation.fapp (.fcomp d₁ d₂) d₃).interp lex
      = (Derivation.fapp d₁ (.fapp d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

/-- Reassociating a backward-composition chain preserves interpretation — the mirror
of `interp_fcomp_assoc`. -/
theorem Derivation.interp_bcomp_assoc {E W : Type} (lex : SemLexicon E W)
    {x y z w : Cat Atom} (d₁ : Derivation Atom (y \ z)) (d₂ : Derivation Atom (x \ y))
    (d₃ : Derivation Atom (w \ x)) :
    (Derivation.bcomp (.bcomp d₁ d₂) d₃).interp lex
      = (Derivation.bcomp d₁ (.bcomp d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

/-- Applying twice is the same as backward-composing first — the mirror of
`interp_fapp_fcomp`. -/
theorem Derivation.interp_bapp_bcomp {E W : Type} (lex : SemLexicon E W)
    {x y w : Cat Atom} (d₁ : Derivation Atom y) (d₂ : Derivation Atom (x \ y))
    (d₃ : Derivation Atom (w \ x)) :
    (Derivation.bapp (.bapp d₁ d₂) d₃).interp lex
      = (Derivation.bapp d₁ (.bcomp d₂ d₃)).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

end CCG
