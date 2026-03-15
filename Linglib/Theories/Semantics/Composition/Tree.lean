/-
# Type-Driven Interpretation (@cite{heim-kratzer-1998}, Ch. 3-5)
@cite{klein-sag-1985}

Composition principles:
1. Terminal Nodes (TN): lexical lookup
2. Non-Branching Nodes (NN): identity
3. Functional Application (FA): `⟦α⟧ = ⟦β⟧(⟦γ⟧)` when types match
4. Predicate Modification (PM): combine two `⟨e,t⟩` predicates (Ch. 4)
5. Predicate Abstraction (PA): `⟦[n β]⟧^g = λx. ⟦β⟧^{g[n↦x]}` (Ch. 5)

-/

import Linglib.Core.Tree
import Linglib.Theories.Semantics.Montague.Types
import Linglib.Theories.Semantics.Montague.Modification
import Linglib.Theories.Semantics.Montague.Variables

namespace Semantics.Composition.Tree

open Semantics.Montague Semantics.Montague.Modification
open Semantics.Montague.Variables

-- ============================================================================
-- Composition Primitives
-- ============================================================================

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

-- ============================================================================
-- Tree Interpretation
-- ============================================================================

open Core.Tree

section TreeInterp

variable {C : Type}

/-- Interpret a tree under an assignment.

Implements @cite{heim-kratzer-1998} Ch. 3-5 type-driven interpretation:
- **TN**: terminal → lexical lookup
- **NN**: unary node → identity
- **FA/PM**: binary node → try FA then PM
- **Traces/Pronouns**: `⟦tₙ⟧^g = g(n)`
- **Predicate Abstraction (PA)**: `⟦[n β]⟧^g = λx. ⟦β⟧^{g[n↦x]}`

PA is the key to quantifier scope: after QR moves a quantifier DP
to a higher position, PA abstracts over the trace it leaves behind,
producing a predicate that the quantifier can take as its scope argument.

The category parameter `C` is ignored during interpretation — composition
is type-driven, not category-driven. This means the same function works
for `Tree Cat String` (UD-grounded), `Tree Unit String` (category-free),
or any other category system. -/
def interp (m : Model) (lex : Lexicon m) (g : Assignment m)
    : Tree C String → Option (TypedDenot m)
  | .terminal _ w => interpTerminal m lex w
  | .node _ (t :: []) => (interp m lex g t).map interpNonBranching
  | .node _ (t1 :: t2 :: []) => do
    let d1 ← interp m lex g t1
    let d2 ← interp m lex g t2
    interpBinary d1 d2
  | .node _ _ => none
  | .trace n _ => some ⟨.e, g n⟩
  | .bind n _ body => do
    let ⟨bodyTy, probeVal⟩ ← interp m lex g body
    some ⟨.fn .e bodyTy, λ (x : m.Entity) =>
      match interp m lex (g[n ↦ x]) body with
      | some ⟨ty, val⟩ => if h : ty = bodyTy then h ▸ val else probeVal
      | none => probeVal⟩

/-- Extract truth value from tree interpretation. -/
def evalTree {m : Model} (lex : Lexicon m) (g : Assignment m) (t : Tree C String)
    : Option Bool :=
  match interp m lex g t with
  | some ⟨.t, b⟩ => some b
  | _ => none

end TreeInterp

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

end Semantics.Composition.Tree
