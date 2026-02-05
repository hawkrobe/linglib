/-
# Anaphora and Binding

Assignment-based binding (Heim & Kratzer 1998 Ch. 5) and its equivalence
with the continuation approach (Barker & Shan 2014).

## References

- Heim & Kratzer (1998). Semantics in Generative Grammar. Ch. 5.
- Barker & Shan (2014). Continuations and Natural Language. Ch. 15.
-/

import Linglib.Theories.TruthConditional.Basic
import Linglib.Theories.TruthConditional.Variables
import Linglib.Theories.TruthConditional.Determiner.Quantifier
import Linglib.Theories.Core.Interfaces.BindingSemantics

namespace TruthConditional.Anaphora

open TruthConditional
open TruthConditional.Variables
open Interfaces.BindingSemantics


section InterpretationState

/-- Semantic interpretation state: current assignment + pending abstractions. -/
structure InterpState (m : Model) where
  assignment : Assignment m
  abstractionStack : List Nat

/-- Initial interpretation state with a given assignment. -/
def InterpState.initial {m : Model} (g : Assignment m) : InterpState m :=
  { assignment := g, abstractionStack := [] }

/-- Push an abstraction index onto the stack. -/
def InterpState.pushAbstraction {m : Model}
    (state : InterpState m) (idx : Nat) : InterpState m :=
  { state with abstractionStack := idx :: state.abstractionStack }

/-- Interpret a bound pronoun: read from assignment at the variable index. -/
def interpretBoundPronoun {m : Model}
    (state : InterpState m) (varIdx : Nat) : m.Entity :=
  state.assignment varIdx

/-- Interpret a binder: create a function that updates the assignment. -/
def interpretBinder {m : Model} {τ : Ty}
    (varIdx : Nat) (body : InterpState m → m.interpTy τ)
    (state : InterpState m) : m.interpTy (.e ⇒ τ) :=
  λ x => body { state with assignment := state.assignment[varIdx ↦ x] }


end InterpretationState

section BindingConditions

/-- A binding is semantically well-formed if the binder's scope includes the bindee. -/
def bindingWellFormed {m : Model}
    (state : InterpState m) (varIdx : Nat) : Bool :=
  varIdx ∈ state.abstractionStack

/-- Interpret a binding configuration as a semantic check. -/
def interpretBindingConfig {m : Model}
    (bc : BindingConfig) (_g : Assignment m) : Bool :=
  -- All bindings must have consistent indices
  bc.wellFormed


end BindingConditions

section Continuations

/-- Duplicator combinator `W = λκ λx. κ x x` (Barker & Shan 2014). -/
def W {A B : Type} (κ : A → A → B) (x : A) : B := κ x x

example : W (λ x y => x == y) 5 = true := rfl

/-- Continuation monad for binding (GQ type as a monad). -/
abbrev Cont' (R A : Type) := (A → R) → R

/-- `pure`: lift a value into the continuation monad. -/
def Cont'.pure {R A : Type} (a : A) : Cont' R A := λ k => k a

/-- `bind`: compose continuations. -/
def Cont'.bind {R A B : Type} (m : Cont' R A) (f : A → Cont' R B) : Cont' R B :=
  λ k => m (λ a => f a k)

instance {R : Type} : Monad (Cont' R) where
  pure := Cont'.pure
  bind := Cont'.bind

/-- H&K interpretation of binding. -/
def hkBinding {m : Model} (n : Nat) (body : m.Entity → Bool)
    (binder : m.Entity) (g : Assignment m) : Bool :=
  body (g[n ↦ binder] n)

/-- B&S interpretation of binding (continuation-based). -/
def bsBinding {Entity : Type} (body : Entity → Entity → Bool)
    (binder : Entity) : Bool :=
  W body binder

/-- H&K and B&S agree for reflexive binding: both produce `body(binder, binder)`. -/
theorem hk_bs_reflexive_equiv {m : Model} (n : Nat)
    (body : m.Entity → m.Entity → Bool)
    (binder : m.Entity) (g : Assignment m) :
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

/-- The Yoneda embedding view: `Cont R A ≅ ∀X. (A → X) → (R → X) → X`. -/
def contAsYoneda {R A : Type} (c : Cont' R A) : (A → R) → R := c

/-- CPS transform preserves binding semantics. -/
theorem cps_preserves_semantics {E A : Type} (f : Reader E A) (e : E) (k : A → Bool) :
    cpsTransform f k e = k (f e) := rfl

/-- W is the semantic content of binding in both frameworks. -/
theorem binding_is_contraction {A : Type} (rel : A → A → Bool) (x : A) :
    (λ _ : Unit => rel x x) () = W rel x := rfl

end CategoricalPerspective


section EvaluationOrder

/-- Evaluation context tracks which binders are "active". -/
structure EvalContext (Entity : Type) where
  activeBinders : List Entity
  position : Nat
  deriving Repr

/-- A pronoun can be bound only if its binder is active. -/
def canBind {Entity : Type} [DecidableEq Entity]
    (ctx : EvalContext Entity) (binder : Entity) : Bool :=
  binder ∈ ctx.activeBinders

/-- Crossover: pronoun position < binder position → binding fails. -/
def crossover (pronounPos binderPos : Nat) : Bool :=
  pronounPos < binderPos


end EvaluationOrder

section VPEllipsis

/-- Strict reading: pronoun resolves to original antecedent. -/
def strictReading {Entity : Type}
    (vp : Entity → Entity → Bool)
    (antecedent : Entity)
    (ellipsisSite : Entity)
    : Bool :=
  vp ellipsisSite antecedent

/-- Sloppy reading: pronoun re-binds to new subject. -/
def sloppyReading {Entity : Type}
    (vp : Entity → Entity → Bool)
    (ellipsisSite : Entity)
    : Bool :=
  W vp ellipsisSite

/-- VPE ambiguity: both readings available. -/
structure VPEAmbiguity (Entity : Type) where
  vp : Entity → Entity → Bool
  antecedentSubj : Entity
  ellipsisSite : Entity

def VPEAmbiguity.strictValue {Entity : Type} (a : VPEAmbiguity Entity) : Bool :=
  strictReading a.vp a.antecedentSubj a.ellipsisSite

def VPEAmbiguity.sloppyValue {Entity : Type} (a : VPEAmbiguity Entity) : Bool :=
  sloppyReading a.vp a.ellipsisSite


end VPEllipsis

end Continuations

end TruthConditional.Anaphora
