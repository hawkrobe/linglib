/-!
# Binding Semantics

Data types for H&K-style assignment-based binding semantics.
-/

namespace Interfaces.BindingSemantics

/-- A position in a syntactic structure. -/
structure Position where
  /-- Linear index (word position) -/
  index : Nat
  deriving Repr, DecidableEq, BEq, Hashable

/-- A binding relation: which binder binds which bindee. -/
structure BindingRelation where
  /-- Position of the binder (quantifier, lambda-operator, etc.) -/
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

/-- A binding configuration is well-formed. -/
def BindingConfig.wellFormed (bc : BindingConfig) : Bool :=
  -- No double binding
  let noDoubleBinding := bc.bindings.all λ r1 =>
    bc.bindings.all λ r2 =>
      r1.bindee != r2.bindee || r1.binder == r2.binder
  -- No self-binding
  let noSelfBinding := bc.bindings.all λ r =>
    r.binder != r.bindee
  -- Consistent indices
  let consistentIndices := bc.bindings.all λ r1 =>
    bc.bindings.all λ r2 =>
      r1.binder != r2.binder || r1.varIndex == r2.varIndex
  noDoubleBinding && noSelfBinding && consistentIndices

end Interfaces.BindingSemantics
