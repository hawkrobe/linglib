import Linglib.Core.Basic

/-!
# BindingSemantics

Abstract interface for H&K-style assignment-based binding semantics.
-/

namespace Interfaces.BindingSemantics

/-- A position in a syntactic structure. -/
structure Position where
  /-- Linear index (word position) -/
  index : Nat
  deriving Repr, DecidableEq, BEq, Hashable

/-- A binding relation: which binder binds which bindee. -/
structure BindingRelation where
  /-- Position of the binder (quantifier, λ-operator, etc.) -/
  binder : Position
  /-- Position of the bindee (pronoun, trace, etc.) -/
  bindee : Position
  /-- The variable index used in the assignment function -/
  varIndex : Nat
  deriving Repr, DecidableEq

/-- A complete binding configuration for a structure. -/
structure BindingConfig where
  /-- All binding relations in the structure -/
  bindings : List BindingRelation
  /-- Positions that are free (unbound) variables -/
  freeVariables : List (Position × Nat)  -- position and its index
  deriving Repr

/-- What a syntactic theory must provide for H&K binding semantics. -/
class HasBindingConfig (T : Type) where
  /-- The theory's syntactic structure type -/
  Structure : Type
  /-- Extract binding configuration from a structure -/
  bindingConfig : Structure → BindingConfig

variable {T : Type} [HasBindingConfig T]

/-- Get all binders in a structure -/
def binders (s : HasBindingConfig.Structure T) : List Position :=
  (HasBindingConfig.bindingConfig s).bindings.map (·.binder)

/-- Get all bindees in a structure -/
def bindees (s : HasBindingConfig.Structure T) : List Position :=
  (HasBindingConfig.bindingConfig s).bindings.map (·.bindee)

/-- Is position p bound in structure s? -/
def isBound (s : HasBindingConfig.Structure T) (p : Position) : Bool :=
  (HasBindingConfig.bindingConfig s).bindings.any (·.bindee == p)

/-- Is position p a binder in structure s? -/
def isBinder (s : HasBindingConfig.Structure T) (p : Position) : Bool :=
  (HasBindingConfig.bindingConfig s).bindings.any (·.binder == p)

/-- Get the binder for a bound position (if any) -/
def binderOf (s : HasBindingConfig.Structure T) (p : Position) : Option Position :=
  (HasBindingConfig.bindingConfig s).bindings.find? (·.bindee == p) |>.map (·.binder)

/-- Get the variable index for a bound position -/
def varIndexOf (s : HasBindingConfig.Structure T) (p : Position) : Option Nat :=
  (HasBindingConfig.bindingConfig s).bindings.find? (·.bindee == p) |>.map (·.varIndex)

/-- Get all positions bound by a given binder -/
def boundBy (s : HasBindingConfig.Structure T) (binder : Position) : List Position :=
  (HasBindingConfig.bindingConfig s).bindings.filter (·.binder == binder) |>.map (·.bindee)

/-- A binding configuration is well-formed. -/
def BindingConfig.wellFormed (bc : BindingConfig) : Bool :=
  -- No double binding
  let noDoubleBinding := bc.bindings.all fun r1 =>
    bc.bindings.all fun r2 =>
      r1.bindee != r2.bindee || r1.binder == r2.binder
  -- No self-binding
  let noSelfBinding := bc.bindings.all fun r =>
    r.binder != r.bindee
  -- Consistent indices
  let consistentIndices := bc.bindings.all fun r1 =>
    bc.bindings.all fun r2 =>
      r1.binder != r2.binder || r1.varIndex == r2.varIndex
  noDoubleBinding && noSelfBinding && consistentIndices

/-- A structure has well-formed binding -/
def hasWellFormedBinding (s : HasBindingConfig.Structure T) : Bool :=
  (HasBindingConfig.bindingConfig s).wellFormed

variable {T1 T2 : Type} [HasBindingConfig T1] [HasBindingConfig T2]

/-- Two theories agree on binding if they produce equivalent configurations. -/
def bindingEquivalent
    (s1 : HasBindingConfig.Structure T1)
    (s2 : HasBindingConfig.Structure T2) : Bool :=
  let bc1 := HasBindingConfig.bindingConfig s1
  let bc2 := HasBindingConfig.bindingConfig s2
  -- Check same binder-bindee pairs (ignoring indices)
  let pairs1 := bc1.bindings.map fun r => (r.binder, r.bindee)
  let pairs2 := bc2.bindings.map fun r => (r.binder, r.bindee)
  pairs1.all (pairs2.contains ·) && pairs2.all (pairs1.contains ·)

end Interfaces.BindingSemantics
