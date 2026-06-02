/-
# Anaphora and Binding
[barker-shan-2014]

The continuation approach to binding and its equivalence with assignment-based
binding ([heim-kratzer-1998] Ch. 5).

Per [buring-2012] §3, a bound pronoun has the *same* denotation as a free
one — the variable `g(i)` — with binding supplied externally by the β-operator.
That assignment-based binding is the project-canonical `interpPronoun` /
`lambdaAbsG` (`Core.Logic.Intensional.Variables`), also the selector of the
unified pronoun denotation `PersonalPronoun.denote`; this file develops the
continuation rendering (`W`, `hkBinding`/`bsBinding`) and the cylindric-algebra
view of the assignment update.

-/

import Linglib.Core.Logic.Intensional.Frame
import Linglib.Core.Logic.Intensional.Variables
import Linglib.Semantics.Composition.ToyDomain
import Linglib.Semantics.Quantification.Quantifier

namespace Semantics.Reference.Binding

open Core.Logic.Intensional
open Core.Logic.Intensional.Variables
open Semantics.Montague


section Continuations

/-- Duplicator combinator `W = λκ λx. κ x x`. -/
def W {A B : Type} (κ : A → A → B) (x : A) : B := κ x x

example : W (λ x y => x = y) 5 = (5 = 5) := rfl

/-- H&K interpretation of binding. -/
def hkBinding {F : Frame} (n : Nat) (body : F.Entity → Prop)
    (binder : F.Entity) (g : Core.Assignment F.Entity) : Prop :=
  body (g[n ↦ binder] n)

/-- B&S interpretation of binding (continuation-based). -/
def bsBinding {Entity : Type} (body : Entity → Entity → Prop)
    (binder : Entity) : Prop :=
  W body binder

/-- H&K and B&S agree for reflexive binding: both produce `body(binder, binder)`. -/
theorem hk_bs_reflexive_equiv {F : Frame} (n : Nat)
    (body : F.Entity → F.Entity → Prop)
    (binder : F.Entity) (g : Core.Assignment F.Entity) :
    body (g[n ↦ binder] n) (g[n ↦ binder] n) = W body binder := by
  simp only [W, update_same]

section CategoricalPerspective

/-- The Reader monad (H&K assignments are Reader computations). -/
abbrev Reader (E A : Type) := E → A

/-- Reader is a monad. -/
instance {E : Type} : Monad (Reader E) where
  pure a := λ _ => a
  bind m f := λ e => f (m e) e

/-- CPS transform: Reader → Continuation-expecting function. -/
def cpsTransform {E A R : Type} (f : Reader E A) : (A → R) → E → R :=
  λ k e => k (f e)

/-- CPS transform preserves binding semantics. -/
theorem cps_preserves_semantics {E A : Type} (f : Reader E A) (e : E) (k : A → Prop) :
    cpsTransform f k e = k (f e) := rfl

/-- W is the semantic content of binding in both frameworks. -/
theorem binding_is_contraction {A : Type} (rel : A → A → Prop) (x : A) :
    (λ _ : Unit => rel x x) () = W rel x := rfl

end CategoricalPerspective


section EvaluationOrder

/-- Evaluation context tracks which binders are "active". -/
structure EvalContext (Entity : Type) where
  activeBinders : List Entity
  position : Nat
  deriving Repr

/-- A pronoun can be bound only if its binder is active. -/
def canBind {Entity : Type}
    (ctx : EvalContext Entity) (binder : Entity) : Prop :=
  binder ∈ ctx.activeBinders

/-- Crossover: pronoun position < binder position → binding fails. -/
def crossover (pronounPos binderPos : Nat) : Prop :=
  pronounPos < binderPos


end EvaluationOrder

section VPEllipsis

/-- Strict reading: pronoun resolves to original antecedent. -/
def strictReading {Entity : Type}
    (vp : Entity → Entity → Prop)
    (antecedent : Entity)
    (ellipsisSite : Entity)
    : Prop :=
  vp ellipsisSite antecedent

/-- Sloppy reading: pronoun re-binds to new subject. -/
def sloppyReading {Entity : Type}
    (vp : Entity → Entity → Prop)
    (ellipsisSite : Entity)
    : Prop :=
  W vp ellipsisSite

/-- VPE ambiguity: both readings available. -/
structure VPEAmbiguity (Entity : Type) where
  vp : Entity → Entity → Prop
  antecedentSubj : Entity
  ellipsisSite : Entity

def VPEAmbiguity.strictValue {Entity : Type} (a : VPEAmbiguity Entity) : Prop :=
  strictReading a.vp a.antecedentSubj a.ellipsisSite

def VPEAmbiguity.sloppyValue {Entity : Type} (a : VPEAmbiguity Entity) : Prop :=
  sloppyReading a.vp a.ellipsisSite


end VPEllipsis

end Continuations

-- ════════════════════════════════════════════════════════════════
-- § Cylindric Algebra Connection
-- ════════════════════════════════════════════════════════════════

/-! ### Binding as cylindric algebra substitution

The connection between Heim & Kratzer's binding mechanism and
cylindric algebra ([henkin-monk-tarski-1971]):

- **Binder at index n** creates `fun x => body(g[n↦x])`, the function
  whose existential closure is cylindrification `cₙ`
- **Bound pronoun at index n** reads `g(n)`, a register projection
- **Binding resolution** (pronoun κ bound by binder l) = cylindric
  substitution `σ^κ_l(φ) = fun g => φ(g[κ↦g(l)])`

These are not mere analogies: H&K's assignment update `g[n↦x]` IS
the cylindric set algebra's coordinate update, and their quantifier
scope `∃x.φ(g[n↦x])` IS cylindrification `cₙ(φ)`. -/

section CylindricAlgebra

/-- Binding links pronoun κ to binder l by substituting g(l) for g(κ).

After binding, `g(κ) = g(l)`, which is the diagonal element `Dκl`.
The semantic effect on a predicate φ is `φ(g[κ↦g(l)])`, which is
cylindric substitution `σ^κ_l(φ)`. -/
theorem binding_eq_resolve {F : Frame} (κ l : Nat)
    (φ : Core.Assignment F.Entity → Prop) (g : Core.Assignment F.Entity) :
    φ (g[κ ↦ g l]) = resolve κ l φ g := rfl

/-- After binding, the bound pronoun and its binder agree:
`(g[κ↦g(l)])(κ) = (g[κ↦g(l)])(l)`. This is the diagonal condition
`Dκl` that cylindric substitution enforces. -/
theorem binding_establishes_diagonal {F : Frame} (κ l : Nat)
    (g : Core.Assignment F.Entity) (h : κ ≠ l) :
    diag κ l (g[κ ↦ g l]) := by
  simp [diag, update_same, update_other g κ l (g l) (Ne.symm h)]

end CylindricAlgebra

end Semantics.Reference.Binding
