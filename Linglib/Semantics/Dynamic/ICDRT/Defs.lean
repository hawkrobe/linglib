import Linglib.Semantics.Dynamic.ContextChange
import Mathlib.Data.Fintype.Basic

/-!
# ICDRT discourse referents
[hofmann-2025], [brasoveanu-2006]

Carrier types of Intensional CDRT ([hofmann-2025]'s intensional extension
of [muskens-1996]'s Compositional DRT, following [brasoveanu-2006]'s
Dynamic Ty2): entities extended with the universal falsifier ⋆
(`Entity`, [brasoveanu-2006]'s dummy value for referent-less worlds), the
two variable sorts (`IVar` for individuals, `PVar` for the propositional
drefs that store local contexts), and the two-sorted assignment
(`ICDRTAssignment` — individual drefs as individual concepts `W → Entity E`,
propositional drefs as `Set W`).

The system built over these types — updates, dynamic conditions, the
veridicality typology — lives in `ICDRT/Basic.lean`; the paper-specific
apparatus in `Studies/Hofmann2025.lean`. (The concept drefs of
[krifka-2026] live with their consumer in `Studies/Krifka2026.lean`.)
-/

namespace Semantics.Dynamic.Core

/--
Entities extended with the universal falsifier ⋆ ([brasoveanu-2006]; adopted
by [hofmann-2025]): individual drefs map to ⋆ in worlds where the referent
does not exist — in "There's no bathroom", the bathroom variable maps to ⋆
in all worlds. Lexical relations are axiomatically false of ⋆
(`star_falsifies`).
-/
inductive Entity (E : Type*) where
  | some : E → Entity E
  | star : Entity E  -- The universal falsifier ⋆
  deriving DecidableEq, Repr

namespace Entity

variable {E : Type*}

/-- Lift a predicate to handle ⋆ (false for ⋆) -/
def liftPred (p : E → Bool) : Entity E → Bool
  | .some e => p e
  | .star => false

/-- Lift a binary predicate (false if either is ⋆) -/
def liftPred₂ (p : E → E → Bool) : Entity E → Entity E → Bool
  | .some e₁, .some e₂ => p e₁ e₂
  | _, _ => false

/-- Is this a real entity (not ⋆)? -/
def isSome : Entity E → Prop
  | .some _ => True
  | .star => False

instance : DecidablePred (@isSome E) := fun e => by unfold isSome; cases e <;> infer_instance

/-- ⋆ is the universal falsifier: any lifted predicate yields false for ⋆ —
[hofmann-2025]'s axiom that lexical relations are false of ⋆. -/
@[simp] theorem star_falsifies (p : E → Bool) :
    Entity.liftPred p (.star : Entity E) = false := rfl

/-- ⋆ falsifies binary predicates from the left. -/
@[simp] theorem star_falsifies₂_left (p : E → E → Bool) (e : Entity E) :
    Entity.liftPred₂ p (.star : Entity E) e = false := by cases e <;> rfl

/-- ⋆ falsifies binary predicates from the right. -/
@[simp] theorem star_falsifies₂_right (p : E → E → Bool) (e : Entity E) :
    Entity.liftPred₂ p e (.star : Entity E) = false := by cases e <;> rfl

instance [Inhabited E] : Inhabited (Entity E) where
  default := .star

/-- `Entity` is a functor: `f <$> .some e = .some (f e)` and `f <$> .star = .star` —
`Option`'s functor structure under the renaming `some ↔ Entity.some`,
`none ↔ Entity.star`. Used by the effect-functor-parameterized lookup
interface in `Semantics/Dynamic/Accessibility.lean`. -/
instance : Functor Entity where
  map f
    | .some e => .some (f e)
    | .star => .star

instance [Fintype E] : Fintype (Entity E) where
  elems := Finset.cons .star (Finset.map ⟨Entity.some, λ _ _ h => by cases h; rfl⟩ Finset.univ)
    (by simp [Finset.mem_map])
  complete := λ x => by cases x <;> simp [Finset.mem_cons]

end Entity

/--
Variable indices for discourse referents.

We use natural numbers but provide type wrappers for clarity.
-/
abbrev Var := Nat

/--
A propositional variable (names a propositional dref).

Propositional variables track local contexts - the set of worlds where
an individual dref was introduced.
-/
structure PVar where
  idx : Nat
  deriving DecidableEq, Repr, Hashable

/--
An individual variable (names an individual dref).
-/
structure IVar where
  idx : Nat
  deriving DecidableEq, Repr, Hashable

/--
An ICDRT assignment maps variables to values.

In ICDRT, we need to track two kinds of assignments:
1. Individual variable assignments: IVar → Entity E
2. Propositional variable assignments: PVar → Set W

This is used by the ICDRT system (`ICDRT/Basic.lean`); simpler theories
can use Nat → E.
-/
structure ICDRTAssignment (W : Type*) (E : Type*) where
  /-- Individual variable assignment: intensional individual drefs (individual
      concepts). Each variable maps worlds to entities, possibly ⋆.
      In [hofmann-2025]'s notation: type s(we), i.e., for each variable v,
      v(i) is a function from worlds to entities. v(i)(w) = ⋆ when v has no
      referent in w. -/
  indiv : IVar → W → Entity E
  /-- Propositional variable assignment -/
  prop : PVar → Set W

namespace ICDRTAssignment

variable {W E : Type*}

/-- Empty assignment (all variables map to ⋆ / empty set) -/
def empty : ICDRTAssignment W E where
  indiv := λ _ _ => .star
  prop := λ _ => ∅

/-- Update individual variable with an individual concept (world-dependent). -/
def updateIndiv (g : ICDRTAssignment W E) (v : IVar) (e : W → Entity E) : ICDRTAssignment W E :=
  { g with indiv := λ v' => if v' == v then e else g.indiv v' }

/-- Update individual variable with a constant entity (world-invariant).
    Convenience for cases where the entity is the same in all worlds. -/
def updateIndivConst (g : ICDRTAssignment W E) (v : IVar) (e : Entity E) : ICDRTAssignment W E :=
  g.updateIndiv v (λ _ => e)

/-- Update propositional variable -/
def updateProp (g : ICDRTAssignment W E) (p : PVar) (s : Set W) : ICDRTAssignment W E :=
  { g with prop := λ p' => if p' == p then s else g.prop p' }

end ICDRTAssignment

end Semantics.Dynamic.Core
