/-
# BindingSemantics: Abstract Interface for Semantic Binding

This typeclass defines what a syntactic theory must provide to enable
Heim & Kratzer-style assignment-based binding semantics.

## The Key Abstraction

For H&K semantics to work, the syntax must tell us:
1. Which positions contain bindable expressions (pronouns, traces)
2. Which positions contain binders (quantifiers, λ-operators)
3. Which binders bind which bindees (the binding relation)

Different syntactic theories derive this information differently:
- **Minimalism**: Movement creates λ-abstraction; traces are bound variables
- **HPSG**: Index features are structure-shared via unification
- **CCG**: Hypothetical reasoning with λ-abstraction
- **LFG**: Functional control equations

But semantically, they all reduce to: "position i is bound by position j with index n"

## Design

The interface is maximally abstract:
- `BindingConfig`: What's bound to what
- `HasBindingConfig`: Syntax theories provide this for their structures

The Montague semantics (Variables.lean) then interprets binding configs
uniformly via assignment functions.

## References

- Heim & Kratzer (1998). Semantics in Generative Grammar. Ch. 5.
- Jacobson (1999). Towards a Variable-Free Semantics. (alternative)
-/

import Linglib.Core.Basic

namespace Interfaces.BindingSemantics

-- ============================================================================
-- Part 1: Binding Configuration
-- ============================================================================

/-- A position in a syntactic structure.

This is abstract - different theories will map their positions to this. -/
structure Position where
  /-- Linear index (word position) -/
  index : Nat
  deriving Repr, DecidableEq, BEq, Hashable

/-- A binding relation: which binder binds which bindee.

In H&K terms: the binder introduces a λ-abstraction over variable `varIndex`,
and the bindee is interpreted as that variable.
-/
structure BindingRelation where
  /-- Position of the binder (quantifier, λ-operator, etc.) -/
  binder : Position
  /-- Position of the bindee (pronoun, trace, etc.) -/
  bindee : Position
  /-- The variable index used in the assignment function -/
  varIndex : Nat
  deriving Repr, DecidableEq

/-- A complete binding configuration for a structure.

This captures ALL the binding relations in a single syntactic structure.
The semantic interpretation uses this to set up assignment functions.
-/
structure BindingConfig where
  /-- All binding relations in the structure -/
  bindings : List BindingRelation
  /-- Positions that are free (unbound) variables -/
  freeVariables : List (Position × Nat)  -- position and its index
  deriving Repr

-- ============================================================================
-- Part 2: The Interface
-- ============================================================================

/-- What a syntactic theory must provide for H&K binding semantics.

Type parameter `T` is a marker type for the theory.
Type parameter `S` is the theory's structure type.

A theory satisfies this interface by showing how to extract
binding information from its syntactic representations.
-/
class HasBindingConfig (T : Type) where
  /-- The theory's syntactic structure type -/
  Structure : Type
  /-- Extract binding configuration from a structure -/
  bindingConfig : Structure → BindingConfig

-- ============================================================================
-- Part 3: Derived Operations
-- ============================================================================

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

-- ============================================================================
-- Part 4: Well-formedness Conditions
-- ============================================================================

/-- A binding configuration is well-formed if:
1. No position is bound by multiple binders
2. Binders don't bind themselves
3. Variable indices are consistent (same binder → same index)
-/
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

-- ============================================================================
-- Part 5: Theory Comparison
-- ============================================================================

variable {T1 T2 : Type} [HasBindingConfig T1] [HasBindingConfig T2]

/-- Two theories agree on binding if they produce equivalent configurations.

"Equivalent" means: same binding relations up to variable index renaming.
-/
def bindingEquivalent
    (s1 : HasBindingConfig.Structure T1)
    (s2 : HasBindingConfig.Structure T2) : Bool :=
  let bc1 := HasBindingConfig.bindingConfig s1
  let bc2 := HasBindingConfig.bindingConfig s2
  -- Check same binder-bindee pairs (ignoring indices)
  let pairs1 := bc1.bindings.map fun r => (r.binder, r.bindee)
  let pairs2 := bc2.bindings.map fun r => (r.binder, r.bindee)
  pairs1.all (pairs2.contains ·) && pairs2.all (pairs1.contains ·)

-- ============================================================================
-- Part 6: Documentation
-- ============================================================================

/-!
## How Syntactic Theories Implement This

### Minimalism

In Minimalist syntax, binding comes from movement:
- A quantifier moves to a scope position
- This creates λ-abstraction over a variable
- The trace/copy in the base position is the bound variable

```
instance : HasBindingConfig MinimalismTheory where
  Structure := MinimalistTree
  bindingConfig tree :=
    { bindings := tree.movementChains.map fun chain =>
        { binder := chain.landingSite
          bindee := chain.launchSite
          varIndex := chain.index }
      freeVariables := tree.unboundPronouns }
```

### HPSG

In HPSG, binding is index sharing:
- NPs have INDEX features (referential indices)
- Binding = two NPs share the same INDEX value
- The o-command hierarchy determines which is binder vs bindee

```
instance : HasBindingConfig HPSGTheory where
  Structure := HPSGSign
  bindingConfig sign :=
    { bindings := sign.coindexedPairs.map fun (np1, np2) =>
        { binder := if oCommands np1 np2 then np1.pos else np2.pos
          bindee := if oCommands np1 np2 then np2.pos else np1.pos
          varIndex := np1.index.value }
      freeVariables := sign.freeIndices }
```

### CCG

In CCG, binding uses hypothetical reasoning:
- Type-raise creates a λ-abstraction
- Hypothetical categories (gaps) become bound variables

```
instance : HasBindingConfig CCGTheory where
  Structure := CCGDerivation
  bindingConfig deriv :=
    { bindings := deriv.hypotheticals.map fun hyp =>
        { binder := hyp.withdrawalSite
          bindee := hyp.hypothesisSite
          varIndex := hyp.index }
      freeVariables := deriv.unboundHypotheticals }
```

## Connection to Montague Semantics

Once a theory provides `HasBindingConfig`, the Montague semantics
in `Variables.lean` can interpret the structure:

1. For each binding relation with index n:
   - The binder introduces λx_n
   - The bindee is interpreted as x_n

2. For free variables:
   - Interpreted via the ambient assignment function

This separation means:
- Syntactic theories handle WHAT binds WHAT
- Montague semantics handles HOW binding is interpreted
-/

end Interfaces.BindingSemantics
