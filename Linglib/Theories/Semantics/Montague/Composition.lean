/-
# Type-Driven Interpretation (Heim & Kratzer 1998, Ch. 3-4)

Composition principles:
1. Terminal Nodes (TN): lexical lookup
2. Non-Branching Nodes (NN): identity
3. Functional Application (FA): `⟦α⟧ = ⟦β⟧(⟦γ⟧)` when types match
4. Predicate Modification (PM): combine two `⟨e,t⟩` predicates (Ch. 4)

Interpretation is syntax-agnostic: it works with any structure providing
terminals and branching via the `SemanticStructure` interface.

## References

- Heim & Kratzer (1998). Semantics in Generative Grammar, Ch. 3-4.
- Klein & Sag (1985). Type-Driven Translation.
-/

import Linglib.Theories.Semantics.Montague.Basic
import Linglib.Theories.Semantics.Montague.Modification
import Linglib.Core.Interface

namespace Semantics.Montague.Composition

open Semantics.Montague Semantics.Montague.Modification Core.Interfaces

structure TypedDenot (m : Model) where
  ty : Ty
  val : m.interpTy ty

def canApply (funTy argTy : Ty) : Option Ty :=
  match funTy with
  | .fn σ τ => if σ = argTy then some τ else none
  | _ => none

/-- TN: lexical lookup. -/
def interpTerminal (m : Model) (lex : Lexicon m) (word : String)
    : Option (TypedDenot m) :=
  (lex word).map λ entry => ⟨entry.ty, entry.denot⟩

/-- NN: identity. -/
def interpNonBranching {m : Model} (daughter : TypedDenot m) : TypedDenot m :=
  daughter

/-- FA: `⟦β⟧(⟦γ⟧)` -/
def interpFA {m : Model} {σ τ : Ty}
    (f : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) : m.interpTy τ :=
  f x

/-- Try FA in both orders. -/
def tryFA {m : Model} (d1 d2 : TypedDenot m) : Option (TypedDenot m) :=
  match hf : d1.ty with
  | .fn σ τ =>
    if ha : σ = d2.ty then
      let f : m.interpTy (σ ⇒ τ) := hf ▸ d1.val
      let a : m.interpTy σ := ha ▸ d2.val
      some ⟨τ, f a⟩
    else
      match hf' : d2.ty with
      | .fn σ' τ' =>
        if ha' : σ' = d1.ty then
          let f : m.interpTy (σ' ⇒ τ') := hf' ▸ d2.val
          let a : m.interpTy σ' := ha' ▸ d1.val
          some ⟨τ', f a⟩
        else none
      | _ => none
  | _ =>
    match hf : d2.ty with
    | .fn σ τ =>
      if ha : σ = d1.ty then
        let f : m.interpTy (σ ⇒ τ) := hf ▸ d2.val
        let a : m.interpTy σ := ha ▸ d1.val
        some ⟨τ, f a⟩
      else none
    | _ => none

/-- PM: combine two `⟨e,t⟩` predicates. -/
def tryPM {m : Model} (d1 d2 : TypedDenot m) : Option (TypedDenot m) :=
  match h1 : d1.ty, h2 : d2.ty with
  | .fn .e .t, .fn .e .t =>
    let p1 : m.interpTy (.e ⇒ .t) := h1 ▸ d1.val
    let p2 : m.interpTy (.e ⇒ .t) := h2 ▸ d2.val
    some ⟨.fn .e .t, predicateModification p1 p2⟩
  | _, _ => none

/-- Binary node: try FA, then PM. -/
def interpBinary {m : Model} (d1 d2 : TypedDenot m) : Option (TypedDenot m) :=
  tryFA d1 d2 <|> tryPM d1 d2

/-- Generic recursive interpretation for any syntax via `SemanticStructure`. -/
def interpret {S : Type} [HasTerminals S] [HasBinaryComposition S] [HasUnaryProjection S]
    (m : Model) (lex : Lexicon m) (interp : S → Option (TypedDenot m)) (s : S)
    : Option (TypedDenot m) :=
  match HasTerminals.getTerminal s with
  | some word => interpTerminal m lex word
  | none =>
    match HasUnaryProjection.getUnaryChild s with
    | some child => (interp child).map interpNonBranching
    | none =>
      match HasBinaryComposition.getBinaryChildren s with
      | some (left, right) => do
        let d1 ← interp left
        let d2 ← interp right
        interpBinary d1 d2
      | none => none

section SynTree

inductive SynTree where
  | terminal : String → SynTree
  | unary : SynTree → SynTree
  | binary : SynTree → SynTree → SynTree
  deriving Repr

instance : HasTerminals SynTree where
  getTerminal
    | .terminal w => some w
    | _ => none

instance : HasBinaryComposition SynTree where
  getBinaryChildren
    | .binary t1 t2 => some (t1, t2)
    | _ => none

instance : HasUnaryProjection SynTree where
  getUnaryChild
    | .unary t => some t
    | _ => none

instance : HasBinding SynTree where
  getBinder _ := none

instance : HasSemanticType SynTree Ty where
  getType _ := none

instance : SemanticStructure SynTree Ty where

def interpTree (m : Model) (lex : Lexicon m) : SynTree → Option (TypedDenot m)
  | .terminal w => interpTerminal m lex w
  | .unary t =>
    (interpTree m lex t).map interpNonBranching
  | .binary t1 t2 => do
    let d1 ← interpTree m lex t1
    let d2 ← interpTree m lex t2
    interpBinary d1 d2

end SynTree

section Interpretability

def isInterpretableWith {S : Type} {m : Model} (interp : S → Option (TypedDenot m)) (s : S) : Bool :=
  (interp s).isSome

def satisfiesInterpretabilityWith {S : Type} {m : Model} (interp : S → Option (TypedDenot m)) (s : S) : Prop :=
  isInterpretableWith interp s = true

def isInterpretable (m : Model) (lex : Lexicon m) (t : SynTree) : Bool :=
  (interpTree m lex t).isSome

def satisfiesInterpretability (m : Model) (lex : Lexicon m) (t : SynTree) : Prop :=
  isInterpretable m lex t = true

end Interpretability

section TypeMismatch

example : canApply .t .e = none := rfl
example : canApply .e .t = none := rfl
example : canApply (.fn .t .t) (.fn .e .t) = none := rfl
example : canApply (.fn .e .t) (.fn .t .t) = none := rfl

end TypeMismatch

section Properties

theorem interpNonBranching_id {m : Model} (d : TypedDenot m) :
    interpNonBranching d = d := rfl

theorem interpFA_type {m : Model} {σ τ : Ty}
    (f : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ)
    : (interpFA f x : m.interpTy τ) = f x := rfl

theorem tryPM_preserves_type {m : Model} (d1 d2 : TypedDenot m)
    (h1 : d1.ty = .fn .e .t) (h2 : d2.ty = .fn .e .t)
    : ∃ d, tryPM d1 d2 = some d ∧ d.ty = .fn .e .t := by
  cases d1 with | mk ty1 val1 =>
  cases d2 with | mk ty2 val2 =>
  simp only at h1 h2
  subst h1 h2
  exact ⟨_, rfl, rfl⟩

theorem interpBinary_eq {m : Model} (d1 d2 : TypedDenot m) :
    interpBinary d1 d2 = (tryFA d1 d2).orElse (λ _ => tryPM d1 d2) := rfl

end Properties

end Semantics.Montague.Composition
