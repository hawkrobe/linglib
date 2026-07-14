import Linglib.Syntax.CCG.Basic
import Linglib.Semantics.Intensional.Defs
import Linglib.Semantics.Intensional.Conjunction
import Linglib.Semantics.Coordination.Basic
import Linglib.Semantics.Composition.Combinator

/-!
# CCG Syntax-Semantics Interface

Syntactic categories directly encode semantic types and the combinatory rules
correspond to function application and composition ([steedman-2000]), so a
derivation's meaning is read off compositionally from its structure.

## Main definitions

- `catToTy` — maps CCG categories to semantic types
- `SemLexEntry`, `SemLexicon` — lexical entries with semantics
- `DerivStep.interp` — computes a meaning from a derivation compositionally:
  application is function application, composition is the `B` combinator,
  type-raising is the `T` combinator, coordination is generalized
  conjunction ([partee-rooth-1983])

Worked toy-fragment derivations and the non-constituent-coordination
semantics theorems live in `Studies/Steedman2000.lean`.
-/

namespace CCG

open Intensional
open Intensional.Conjunction
open Combinator

/-! ### Type correspondence -/

/-- Map CCG categories to semantic types -/
def catToTy : Cat → Ty
  | .atom .S => .t
  | .atom .NP => .e
  | .atom .N => .e ⇒ .t    -- common nouns are properties
  | .atom .PP => .e ⇒ .t   -- PPs are modifiers (simplified)
  | .rslash x y => catToTy y ⇒ catToTy x
  | .lslash x y => catToTy y ⇒ catToTy x

/-- A CCG lexical entry with semantics -/
structure SemLexEntry (E W : Type) where
  form : String
  cat : Cat
  sem : Denot E W (catToTy cat)

/-! ### Type preservation

CCG combinatory rules preserve semantic well-typedness: if the syntactic
combination succeeds, the semantic combination is well-typed. -/

/-- Forward application preserves semantic typing:
    if X/Y combines with Y to give X, then (σ→τ) applied to σ gives τ. -/
theorem forward_app_type_preservation (x y : Cat) :
    catToTy (x.rslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Backward application preserves semantic typing:
    if Y combines with X\Y to give X, then (σ→τ) applied to σ gives τ. -/
theorem backward_app_type_preservation (x y : Cat) :
    catToTy (x.lslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Type correspondence for transitive verbs -/
theorem tv_type_is_relation :
    catToTy TV = (.e ⇒ .e ⇒ .t) := rfl

/-- Type correspondence for intransitive verbs -/
theorem iv_type_is_property :
    catToTy IV = (.e ⇒ .t) := rfl

/-! ### Derivation interpretation -/

/-- A semantic interpretation: category paired with its meaning -/
structure Interp (E W : Type) where
  cat : Cat
  meaning : Denot E W (catToTy cat)

/-- Semantic lexicon: maps words to interpretations -/
def SemLexicon (E W : Type) := String → Cat → Option (Interp E W)

/--
Interpret a CCG derivation, computing its meaning from the lexicon.

Every combinatory rule corresponds to a semantic operation: application is
function application, composition is the `B` combinator, type-raising is the
`T` combinator, and coordination is generalized conjunction (restricted to
conjoinable types). Returns `none` if the derivation is ill-formed or uses
unknown words.
-/
def DerivStep.interp {E W : Type} (d : DerivStep) (lex : SemLexicon E W)
    : Option (Interp E W) :=
  match d with
  | .lex entry => lex entry.form entry.cat

  | .fapp d1 d2 => do
      -- Forward application: X/Y Y → X
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c1, m1 with
      | .rslash x y, m1 =>
          if h : c2 = y then
            let m2' : Denot E W (catToTy y) := h ▸ m2
            some ⟨x, m1 m2'⟩
          else none
      | _, _ => none

  | .bapp d1 d2 => do
      -- Backward application: Y X\Y → X
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c2, m2 with
      | .lslash x y, m2 =>
          if h : c1 = y then
            let m1' : Denot E W (catToTy y) := h ▸ m1
            some ⟨x, m2 m1'⟩
          else none
      | _, _ => none

  | .fcomp d1 d2 => do
      -- Forward composition: X/Y + Y/Z → X/Z, semantically B (f ∘ g)
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c1, m1 with
      | .rslash x y1, m1 =>
          match c2, m2 with
          | .rslash y2 z, m2 =>
              if h : y1 = y2 then
                let m2' : Denot E W (catToTy z ⇒ catToTy y1) :=
                  h ▸ m2
                some ⟨x / z, B m1 m2'⟩
              else none
          | _, _ => none
      | _, _ => none

  | .bcomp d1 d2 => do
      -- Backward composition: Y\Z + X\Y → X\Z, semantically B (f ∘ g)
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c1, m1 with
      | .lslash y1 z, m1 =>
          match c2, m2 with
          | .lslash x y2, m2 =>
              if h : y1 = y2 then
                let m1' : Denot E W (catToTy z ⇒ catToTy y2) :=
                  h ▸ m1
                some ⟨x \ z, B m2 m1'⟩
              else none
          | _, _ => none
      | _, _ => none

  | .fcompx d1 d2 => do
      -- Forward crossed composition: X/Y + Y\Z → X\Z, semantically B (f ∘ g)
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c1, m1 with
      | .rslash x y1, m1 =>
          match c2, m2 with
          | .lslash y2 z, m2 =>
              if h : y1 = y2 then
                let m2' : Denot E W (catToTy z ⇒ catToTy y1) :=
                  h ▸ m2
                some ⟨x \ z, B m1 m2'⟩
              else none
          | _, _ => none
      | _, _ => none

  | .ftr d t => do
      -- Forward type-raising: X → T/(T\X), semantically T (λf. f x)
      let ⟨x, m⟩ ← d.interp lex
      some ⟨forwardTypeRaise x t, T m⟩

  | .btr d t => do
      -- Backward type-raising: X → T\(T/X), semantically T (λf. f x)
      let ⟨x, m⟩ ← d.interp lex
      some ⟨backwardTypeRaise x t, T m⟩

  | .coord role d1 d2 => do
      -- Coordination: X c X → X, via the Coordinator API — the meaning is `Coordinator.op`
      -- of the coordinator's own `role` (runtime form `engineOp`; = generalized conjunction
      -- [partee-rooth-1983] at `.j`), restricted to conjoinable types. The `role` is read off
      -- the derivation, so *which* coordinator is used is truth-conditionally load-bearing.
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      if h : c1 = c2 then
        let ty := catToTy c1
        if ty.isConjoinable then
          let m2' : Denot E W (catToTy c1) := h ▸ m2
          some ⟨c1, Coordinator.engineOp role ty E W m1 m2'⟩
        else none
      else none

/-- Extract a sentence meaning (category S) from an interpretation result. -/
def getMeaning {E W : Type} (result : Option (Interp E W)) : Option Prop :=
  match result with
  | some ⟨.atom .S, m⟩ => some m
  | _ => none

/-- Extract a predicate meaning (category S/NP) from an interpretation result. -/
def getPredicateMeaning {E W : Type} (result : Option (Interp E W))
    : Option (E → Prop) :=
  match result with
  | some ⟨.rslash (.atom .S) (.atom .NP), m⟩ => some m
  | _ => none

end CCG
