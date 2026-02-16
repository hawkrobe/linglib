import Linglib.Theories.Semantics.Dynamic.Systems.DynamicGQ.Basic

/-!
# Subtype Polymorphism for Dynamic GQs

Charlow's (2021) §4: a type system that distinguishes "complete" (T) from
"incomplete" (t) dynamic meanings. Modified numerals contribute incomplete
meanings (the cardinality test hasn't fired yet), and maximization expects
incomplete input. The subtyping relation t ⊏ T ensures that incomplete
meanings can be used where complete ones are expected, but NOT vice versa.

This blocks the pseudo-cumulative reading: the cardinality test forces
completion (T) inside M_v's scope, but M_v requires its argument to be
incomplete (t). The cumulative reading is well-typed because cardinality
tests scope outside M_v.

## References

- Charlow, S. (2021). Post-suppositions and semantic theory. *L&P* 44, 701–765.
  §4, equations 40–46.
-/

namespace DynamicSemantics.DynamicGQ.SubtypePolymorphism

/-- Completeness level: `incomplete` (t) or `complete` (T).
    Incomplete meanings await further composition (e.g., a cardinality test).
    Complete meanings are ready for discourse integration. -/
inductive Completeness where
  | incomplete  -- t: awaiting cardinality test
  | complete    -- T: fully specified
  deriving DecidableEq, Repr

open Completeness

/-- Subtyping: t ⊏ T, t ⊏ t, T ⊏ T, but NOT T ⊏ t.
    This ensures incomplete meanings can be promoted to complete,
    but complete meanings cannot be demoted. -/
def subtypeOf : Completeness → Completeness → Prop
  | incomplete, _ => True
  | complete, complete => True
  | complete, incomplete => False

instance (a b : Completeness) : Decidable (subtypeOf a b) := by
  cases a <;> cases b <;> simp [subtypeOf] <;> exact inferInstance

/-- Notation for subtyping -/
scoped infix:50 " ⊏ " => subtypeOf

/-- A DRS annotated with its completeness level. -/
structure TypedDRS (S : Type*) (c : Completeness) where
  /-- The underlying DRS -/
  drs : S → S → Prop

/-- Type assignment: E^v (existential introduction) is incomplete. -/
def Evar_type : Completeness := incomplete

/-- Type assignment: M_v (maximization) produces incomplete output. -/
def Mvar_type : Completeness := incomplete

/-- Type assignment: n_v (cardinality test) produces complete output. -/
def CardTest_type : Completeness := complete

/-- Dynamic conjunction is polymorphic: A → A → A for any A. -/
def dynConj_type (c : Completeness) : Completeness := c

/-- The cumulative formula is well-typed (equation 45):
    M_v(E^v ; M_u(E^u ; saw)) : t (incomplete), then ; 5_u : T, ; 3_v : T.
    Since t ⊏ T, the outer cardinality tests can accept incomplete input. -/
theorem cumulative_welltyped :
    subtypeOf (dynConj_type (dynConj_type Mvar_type)) CardTest_type := by
  simp [dynConj_type, Mvar_type, subtypeOf]

/-- The pseudo-cumulative formula is ill-typed (equation 46):
    5_u would need to be INSIDE M_v's scope, but 5_u forces type T (complete),
    and M_v requires type t (incomplete).
    Formalized as: CardTest_type (T) is NOT a subtype of Mvar_type (t). -/
theorem pseudo_cumulative_illtyped :
    ¬ subtypeOf CardTest_type Mvar_type := by
  simp [CardTest_type, Mvar_type, subtypeOf]

end DynamicSemantics.DynamicGQ.SubtypePolymorphism
