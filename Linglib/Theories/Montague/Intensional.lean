/-
# Intensional Montague Semantics

World-parameterized meanings for RSA integration.

## The Problem

Current Montague meanings are extensional - evaluated in a fixed model, producing
values like `Bool`. But RSA needs `meaning : World → Bool` to compute L0:

```lean
-- Current (extensional)
meaning : m.interpTy .t  -- just Bool

-- Desired (intensional)
meaning : World → Bool   -- varies with world
```

## Solution

This module provides an intensional layer where meanings are functions from
possible worlds to extensions:

- `IntensionalModel`: A model with an explicit World type
- `Intension τ`: Type of intensions (World → Extension(τ))
- `Proposition`: Intension of type t (World → Bool)
- `IntensionalDerivation`: Derivation with world-parameterized meaning

## RSA Integration

RSA's L0 can now evaluate compositional semantics directly:

```lean
L0(u, w) = ⟦u⟧(w)  -- where ⟦u⟧ : World → Bool
```

## References

- Montague (1973) "The Proper Treatment of Quantification in Ordinary English"
- Gallin (1975) "Intensional and Higher-Order Modal Logic"
-/

import Linglib.Theories.Montague.Basic
import Linglib.Theories.Montague.SemDerivation
import Linglib.Theories.Montague.Quantifiers

namespace Montague.Intensional

open Montague

-- ============================================================================
-- Intensional Models
-- ============================================================================

/--
An intensional model extends a Montague model with possible worlds.

The base model provides the domain of entities (shared across worlds).
The World type provides indices for evaluating intensions.
-/
structure IntensionalModel where
  /-- The underlying extensional model -/
  base : Model
  /-- The type of possible worlds -/
  World : Type
  /-- Decidable equality on worlds -/
  worldDecEq : DecidableEq World

/-- Make World decidable -/
instance (m : IntensionalModel) : DecidableEq m.World := m.worldDecEq

-- ============================================================================
-- Intensions
-- ============================================================================

/--
An intension is a function from possible worlds to extensions.

For type τ, an intension maps each world to a value of type ⟦τ⟧.
-/
def Intension (m : IntensionalModel) (τ : Ty) : Type :=
  m.World → m.base.interpTy τ

/-- A proposition is an intension of type t (World → Bool) -/
def Proposition (m : IntensionalModel) : Type := m.World → Bool

/-- A property intension: World → (Entity → Bool) -/
def PropertyIntension (m : IntensionalModel) : Type :=
  m.World → (m.base.Entity → Bool)

/-- A relation intension: World → (Entity → Entity → Bool) -/
def RelationIntension (m : IntensionalModel) : Type :=
  m.World → (m.base.Entity → m.base.Entity → Bool)

-- ============================================================================
-- Intensional Interpretation of Types
-- ============================================================================

/--
Full intensional type interpretation (Gallin's IL).

Every type gets lifted to an intension:
- ⟦e⟧ = World → Entity (individual concepts)
- ⟦t⟧ = World → Bool (propositions)
- ⟦σ → τ⟧ = World → (⟦σ⟧_ext → ⟦τ⟧_ext) (intensions of functions)

Note: We use the simpler approach where function arguments are extensional
at each world, following standard practice for RSA applications.
-/
def IntensionalModel.interpTyIntensional (m : IntensionalModel) (τ : Ty) : Type :=
  m.World → m.base.interpTy τ

-- ============================================================================
-- Evaluation
-- ============================================================================

/-- Evaluate an intension at a world to get its extension -/
def evalAt {m : IntensionalModel} {τ : Ty} (meaning : Intension m τ) (w : m.World)
    : m.base.interpTy τ :=
  meaning w

/-- Evaluate a proposition at a world -/
def Proposition.evalAt {m : IntensionalModel} (p : Proposition m) (w : m.World) : Bool :=
  p w

/-- Check if a proposition is true at a world -/
def Proposition.trueAt {m : IntensionalModel} (p : Proposition m) (w : m.World) : Prop :=
  p w = true

-- ============================================================================
-- Intensional Derivations
-- ============================================================================

/--
An intensional semantic derivation.

Like `SemDeriv.Derivation` but with a world-parameterized meaning.
This is what RSA needs: a meaning that can be evaluated at any world.
-/
structure IntensionalDerivation (m : IntensionalModel) where
  /-- The surface form -/
  surface : List String
  /-- The result semantic type -/
  ty : Ty
  /-- The world-parameterized meaning -/
  meaning : Intension m ty
  /-- Scalar item positions -/
  scalarItems : List (SemDeriv.ScalarOccurrence m.base) := []

/-- Evaluate the derivation at a specific world -/
def IntensionalDerivation.evalAt {m : IntensionalModel}
    (d : IntensionalDerivation m) (w : m.World) : m.base.interpTy d.ty :=
  d.meaning w

/-- For type t, get the truth value at a world -/
def IntensionalDerivation.trueAt {m : IntensionalModel}
    (d : IntensionalDerivation m) (h : d.ty = .t) (w : m.World) : Bool :=
  cast (by rw [h]; rfl) (d.meaning w)

-- ============================================================================
-- Lifting Extensional to Intensional
-- ============================================================================

/--
Lift a constant extension to an intension (rigid designator).

For entities like proper names, the extension doesn't vary by world.
-/
def rigid {m : IntensionalModel} {τ : Ty} (ext : m.base.interpTy τ) : Intension m τ :=
  fun _ => ext

/--
Create a world-varying intension from a function.
-/
def varying {m : IntensionalModel} {τ : Ty}
    (f : m.World → m.base.interpTy τ) : Intension m τ := f

-- ============================================================================
-- Intensional Semantics for Quantifiers
-- ============================================================================

open Quantifiers in
/--
"Some" with world-varying property: ∃x. P(w)(x) ∧ Q(w)(x)
-/
def someIntensional {m : IntensionalModel} [FiniteModel m.base]
    (P : PropertyIntension m) (Q : PropertyIntension m) : Proposition m :=
  fun w => FiniteModel.elements.any fun x => P w x && Q w x

open Quantifiers in
/--
"Every" with world-varying property: ∀x. P(w)(x) → Q(w)(x)
-/
def everyIntensional {m : IntensionalModel} [FiniteModel m.base]
    (P : PropertyIntension m) (Q : PropertyIntension m) : Proposition m :=
  fun w => FiniteModel.elements.all fun x => !P w x || Q w x

open Quantifiers in
/--
"No" with world-varying property: ¬∃x. P(w)(x) ∧ Q(w)(x)
-/
def noIntensional {m : IntensionalModel} [FiniteModel m.base]
    (P : PropertyIntension m) (Q : PropertyIntension m) : Proposition m :=
  fun w => !FiniteModel.elements.any fun x => P w x && Q w x

-- ============================================================================
-- Example: Scalar Implicature Scenario
-- ============================================================================

/--
Worlds for scalar implicature reasoning.

These represent different states of affairs:
- none: No individuals satisfy the predicate
- someNotAll: Some but not all satisfy
- all: All individuals satisfy
-/
inductive ScalarWorld where
  | none      -- 0 out of n
  | someNotAll -- 1 to n-1 out of n
  | all       -- n out of n
  deriving DecidableEq, Repr, Inhabited

/--
A simple intensional model for scalar implicatures.
Uses ToyEntity as the domain.
-/
def scalarModel : IntensionalModel := {
  base := toyModel
  World := ScalarWorld
  worldDecEq := inferInstance
}

/-- FiniteModel instance for scalarModel.base -/
instance scalarModelFinite : Quantifiers.FiniteModel scalarModel.base where
  elements := [.john, .mary, .pizza, .book]
  complete := fun x => by cases x <;> simp

/--
"Students" is a rigid property (doesn't vary by world).
In the toy model, John and Mary are students.
-/
def students_rigid : PropertyIntension scalarModel :=
  fun _ => Quantifiers.student_sem

/--
"Sleep" varies by world:
- none: nobody sleeps
- someNotAll: only John sleeps
- all: both John and Mary sleep
-/
def sleep_varying : PropertyIntension scalarModel := fun w =>
  match w with
  | .none => fun _ => false
  | .someNotAll => fun x => match x with
      | .john => true
      | _ => false
  | .all => fun x => match x with
      | .john => true
      | .mary => true
      | _ => false

/--
"Some students sleep" as an intensional derivation.

Meaning varies by world:
- none: false (no students sleep)
- someNotAll: true (John sleeps)
- all: true (both sleep)
-/
def someStudentsSleep_intensional : IntensionalDerivation scalarModel := {
  surface := ["some", "students", "sleep"]
  ty := .t
  meaning := someIntensional students_rigid sleep_varying
  scalarItems := [⟨0, Lexicon.some_entry⟩]
}

/--
"Every student sleeps" as an intensional derivation.

Meaning varies by world:
- none: false (not all students sleep)
- someNotAll: false (Mary doesn't sleep)
- all: true (both sleep)
-/
def everyStudentsSleep_intensional : IntensionalDerivation scalarModel := {
  surface := ["every", "student", "sleeps"]
  ty := .t
  meaning := everyIntensional students_rigid sleep_varying
  scalarItems := [⟨0, Lexicon.every_entry⟩]
}

-- ============================================================================
-- Key Theorems: Truth Conditions Vary by World
-- ============================================================================

/-- Helper: directly evaluate "some students sleep" at a world -/
def someStudentsSleep_at (w : ScalarWorld) : Bool :=
  someStudentsSleep_intensional.meaning w

/-- Helper: directly evaluate "every student sleeps" at a world -/
def everyStudentsSleep_at (w : ScalarWorld) : Bool :=
  everyStudentsSleep_intensional.meaning w

/-- "Some students sleep" is false when no one sleeps -/
theorem some_false_at_none :
    someStudentsSleep_at .none = false := by native_decide

/-- "Some students sleep" is true when some but not all sleep -/
theorem some_true_at_someNotAll :
    someStudentsSleep_at .someNotAll = true := by native_decide

/-- "Some students sleep" is true when all sleep -/
theorem some_true_at_all :
    someStudentsSleep_at .all = true := by native_decide

/-- "Every student sleeps" is false when no one sleeps -/
theorem every_false_at_none :
    everyStudentsSleep_at .none = false := by native_decide

/-- "Every student sleeps" is false when some but not all sleep -/
theorem every_false_at_someNotAll :
    everyStudentsSleep_at .someNotAll = false := by native_decide

/-- "Every student sleeps" is true when all sleep -/
theorem every_true_at_all :
    everyStudentsSleep_at .all = true := by native_decide

-- ============================================================================
-- RSA Integration: The φ Function
-- ============================================================================

/--
The literal semantics function φ for RSA.

This is the key connection: RSA's φ(u, w) is just evaluating
the intensional meaning at world w.

```
φ(u, w) = ⟦u⟧(w)
```
-/
def phi {m : IntensionalModel} (d : IntensionalDerivation m)
    (h : d.ty = .t) (w : m.World) : Bool :=
  d.trueAt h w

/--
Theorem: φ is definitionally equal to evaluating the meaning at the world.

Note: `d.evalAt w` has type `m.base.interpTy d.ty`, which equals `Bool` when `d.ty = .t`.
The `phi` function handles this type coercion.
-/
theorem phi_def {m : IntensionalModel} (d : IntensionalDerivation m)
    (h : d.ty = .t) (w : m.World) :
    phi d h w = d.trueAt h w := rfl

-- ============================================================================
-- Summary: What This Module Provides
-- ============================================================================

/-
## Types

- `IntensionalModel`: Model with World type
- `Intension m τ`: World → m.base.interpTy τ
- `Proposition m`: World → Bool
- `IntensionalDerivation m`: Derivation with intensional meaning

## Key Functions

- `evalAt`: Evaluate intension at a world
- `rigid`: Lift constant to intension
- `varying`: Create world-varying intension
- `someIntensional`, `everyIntensional`: Quantifiers over intensions
- `phi`: RSA's literal semantics (= eval at world)

## Key Theorems

- `some_false_at_none`, `some_true_at_someNotAll`, `some_true_at_all`
- `every_false_at_none`, `every_false_at_someNotAll`, `every_true_at_all`
- `phi_is_eval`: φ(u, w) = ⟦u⟧(w)

## RSA Integration

RSA can now use compositional semantics directly:

```lean
-- L0(u, w) = 1 if ⟦u⟧(w), 0 otherwise
def L0 (u : IntensionalDerivation m) (w : m.World) : Bool :=
  phi u rfl w
```

The meaning comes from the derivation, not from stipulation.
-/

end Montague.Intensional
