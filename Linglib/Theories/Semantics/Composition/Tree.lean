/-
# Type-Driven Interpretation (@cite{heim-kratzer-1998}, Ch. 3-5; @cite{von-fintel-heim-2011}, Ch. 1)


Composition principles:
1. Terminal Nodes (TN): lexical lookup
2. Non-Branching Nodes (NN): identity
3. Functional Application (FA): `⟦α⟧ = ⟦β⟧(⟦γ⟧)` when types match
4. Intensional Functional Application (IFA): `⟦α⟧ = ⟦β⟧(^⟦γ⟧)` when
   β expects an intension `⟨s,σ⟩` and γ has type σ (@cite{von-fintel-heim-2011} Step 10)
5. Predicate Modification (PM): combine two `⟨e,t⟩` predicates (Ch. 4)
6. Predicate Abstraction (PA): `⟦[n β]⟧^g = λx. ⟦β⟧^{g[n↦x]}` (Ch. 5)

-/

import Linglib.Core.Tree
import Linglib.Core.IntensionalLogic.Frame
import Linglib.Core.IntensionalLogic.Variables
import Linglib.Theories.Semantics.Composition.LexEntry
import Linglib.Theories.Semantics.Composition.Modification

namespace Semantics.Composition.Tree

open Core.IntensionalLogic Semantics.Composition.Modification
open Core.IntensionalLogic.Variables
open Semantics.Montague (Lexicon)

-- ============================================================================
-- Composition Primitives
-- ============================================================================

structure TypedDenot (F : Frame) where
  ty : Ty
  val : F.Denot ty

def canApply (funTy argTy : Ty) : Option Ty :=
  match funTy with
  | .fn σ τ => if σ = argTy then some τ else none
  | _ => none

/-- TN: lexical lookup. -/
def interpTerminal (F : Frame) (lex : Lexicon F) (word : String)
    : Option (TypedDenot F) :=
  (lex word).map λ entry => ⟨entry.ty, entry.denot⟩

/-- NN: identity. -/
def interpNonBranching {F : Frame} (daughter : TypedDenot F) : TypedDenot F :=
  daughter

/-- FA: `⟦β⟧(⟦γ⟧)` -/
def interpFA {F : Frame} {σ τ : Ty}
    (f : F.Denot (σ ⇒ τ)) (x : F.Denot σ) : F.Denot τ :=
  f x

/-- Try FA in both orders. -/
def tryFA {F : Frame} (d1 d2 : TypedDenot F) : Option (TypedDenot F) :=
  match hf : d1.ty with
  | .fn σ τ =>
    if ha : σ = d2.ty then
      let f : F.Denot (σ ⇒ τ) := hf ▸ d1.val
      let a : F.Denot σ := ha ▸ d2.val
      some ⟨τ, f a⟩
    else
      match hf' : d2.ty with
      | .fn σ' τ' =>
        if ha' : σ' = d1.ty then
          let f : F.Denot (σ' ⇒ τ') := hf' ▸ d2.val
          let a : F.Denot σ' := ha' ▸ d1.val
          some ⟨τ', f a⟩
        else none
      | _ => none
  | _ =>
    match hf : d2.ty with
    | .fn σ τ =>
      if ha : σ = d1.ty then
        let f : F.Denot (σ ⇒ τ) := hf ▸ d2.val
        let a : F.Denot σ := ha ▸ d1.val
        some ⟨τ, f a⟩
      else none
    | _ => none

/-- IFA: Intensional Functional Application (@cite{von-fintel-heim-2011} Step 10).

    If β expects an intension `⟨s,σ⟩` as argument and γ has type σ,
    then `⟦α⟧ = ⟦β⟧(^⟦γ⟧)` — we wrap γ's denotation in `up` (rigid intension)
    before applying. This lets intensional operators (modals, attitude verbs)
    take the intension of their sister as argument via type-driven composition.

    Tries both orders (β,γ) and (γ,β). -/
def tryIFA {F : Frame} (d1 d2 : TypedDenot F) : Option (TypedDenot F) :=
  match hf : d1.ty with
  | .fn (.intens σ) τ =>
    if ha : σ = d2.ty then
      let f : F.Denot (.fn (.intens σ) τ) := hf ▸ d1.val
      let a : F.Denot σ := ha ▸ d2.val
      some ⟨τ, f (up a)⟩
    else
      match hf' : d2.ty with
      | .fn (.intens σ') τ' =>
        if ha' : σ' = d1.ty then
          let f : F.Denot (.fn (.intens σ') τ') := hf' ▸ d2.val
          let a : F.Denot σ' := ha' ▸ d1.val
          some ⟨τ', f (up a)⟩
        else none
      | _ => none
  | _ =>
    match hf : d2.ty with
    | .fn (.intens σ) τ =>
      if ha : σ = d1.ty then
        let f : F.Denot (.fn (.intens σ) τ) := hf ▸ d2.val
        let a : F.Denot σ := ha ▸ d1.val
        some ⟨τ, f (up a)⟩
      else none
    | _ => none

/-- PM: combine two `⟨e,t⟩` predicates. -/
def tryPM {F : Frame} (d1 d2 : TypedDenot F) : Option (TypedDenot F) :=
  match h1 : d1.ty, h2 : d2.ty with
  | .fn .e .t, .fn .e .t =>
    let p1 : F.Denot (.e ⇒ .t) := h1 ▸ d1.val
    let p2 : F.Denot (.e ⇒ .t) := h2 ▸ d2.val
    some ⟨.fn .e .t, predicateModification p1 p2⟩
  | _, _ => none

/-- Binary node: try FA, then IFA, then PM. -/
def interpBinary {F : Frame} (d1 d2 : TypedDenot F) : Option (TypedDenot F) :=
  tryFA d1 d2 <|> tryIFA d1 d2 <|> tryPM d1 d2

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
def interp (F : Frame) (lex : Lexicon F) (g : Core.Assignment F.Entity)
    : Tree C String → Option (TypedDenot F)
  | .terminal _ w => interpTerminal F lex w
  | .node _ (t :: []) => (interp F lex g t).map interpNonBranching
  | .node _ (t1 :: t2 :: []) => do
    let d1 ← interp F lex g t1
    let d2 ← interp F lex g t2
    interpBinary d1 d2
  | .node _ _ => none
  | .trace n _ => some ⟨.e, g n⟩
  | .bind n _ body => do
    let ⟨bodyTy, probeVal⟩ ← interp F lex g body
    some ⟨.fn .e bodyTy, λ (x : F.Entity) =>
      match interp F lex (g[n ↦ x]) body with
      | some ⟨ty, val⟩ => if h : ty = bodyTy then h ▸ val else probeVal
      | none => probeVal⟩

/-- Extract truth value from tree interpretation. -/
def evalTree {F : Frame} [∀ (p : F.Denot .t), Decidable p]
    (lex : Lexicon F) (g : Core.Assignment F.Entity) (t : Tree C String)
    : Option Bool :=
  match interp F lex g t with
  | some ⟨.t, b⟩ => some (decide b)
  | _ => none

/-- Extract proposition (`s→t`) from tree interpretation.

    For intensional trees where the root denotes a proposition
    rather than a bare truth value — e.g., trees containing EXH
    or other propositional operators. Evaluate the result at a
    specific world to get a truth value. -/
def evalTreeProp {F : Frame} [∀ (p : F.Denot .t), Decidable p]
    (lex : Lexicon F) (g : Core.Assignment F.Entity) (t : Tree C String)
    : Option (F.Index → Bool) :=
  match interp F lex g t with
  | some ⟨.intens .t, p⟩ => some (λ w => decide (p w))
  | _ => none

end TreeInterp

section TypeMismatch

example : canApply .t .e = none := rfl
example : canApply .e .t = none := rfl
example : canApply (.fn .t .t) (.fn .e .t) = none := rfl
example : canApply (.fn .e .t) (.fn .t .t) = none := rfl

end TypeMismatch

section Properties

theorem interpNonBranching_id {F : Frame} (d : TypedDenot F) :
    interpNonBranching d = d := rfl

theorem interpFA_type {F : Frame} {σ τ : Ty}
    (f : F.Denot (σ ⇒ τ)) (x : F.Denot σ)
    : (interpFA f x : F.Denot τ) = f x := rfl

theorem tryPM_preserves_type {F : Frame} (d1 d2 : TypedDenot F)
    (h1 : d1.ty = .fn .e .t) (h2 : d2.ty = .fn .e .t)
    : ∃ d, tryPM d1 d2 = some d ∧ d.ty = .fn .e .t := by
  cases d1 with | mk ty1 val1 =>
  cases d2 with | mk ty2 val2 =>
  simp only at h1 h2
  subst h1 h2
  exact ⟨_, rfl, rfl⟩

theorem interpBinary_eq {F : Frame} (d1 d2 : TypedDenot F) :
    interpBinary d1 d2 =
    (tryFA d1 d2 <|> tryIFA d1 d2 <|> tryPM d1 d2) := rfl

end Properties

end Semantics.Composition.Tree
