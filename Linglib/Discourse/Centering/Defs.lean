import Mathlib.Order.Basic
import Mathlib.Order.Nat
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Centering Theory — Core Definitions
[grosz-joshi-weinstein-1995] [kameyama-1986] [sidner-1979]

Theory-neutral types for Centering: realizations, utterances, and
typeclass plug-ins for ranking schemes (`CfRanker`/`CfRankerOf`),
realization (`Realizes`), and pronominalization (`Pronominalizes`).
Role type `R` is a parameter; `Instances/` provides per-paper rankers.
-/

namespace Discourse.Centering

/-! ### Cf Ranking Plug-In -/

/-- Numeric rank over a role type for ordering forward-looking centers
    (higher rank ⇒ more prominent in Cf). -/
class CfRanker (R : Type*) where
  rank : R → Nat

/-- Lift a `CfRanker` instance to a `LinearOrder`. For finite-enum role
    types, the injectivity obligation is dischargeable by `decide`. -/
abbrev CfRanker.toLinearOrder (R : Type*) [CfRanker R]
    [DecidableEq R] [Fintype R]
    (h : ∀ a b : R, CfRanker.rank a = CfRanker.rank b → a = b := by decide) :
    LinearOrder R :=
  LinearOrder.lift' CfRanker.rank h

/-! ### Realization and Utterance -/

/-- A noun-phrase realization: entity, role, pronoun flag. -/
structure Realization (E : Type*) (R : Type*) where
  entity : E
  role : R
  isPronoun : Bool
  deriving Repr, DecidableEq

/-- An utterance as a list of NP realizations in surface order. -/
structure Utterance (E : Type*) (R : Type*) where
  realizations : List (Realization E R)
  deriving Repr, DecidableEq

/-! ### Generalized Cf Ranking (per-realization) -/

/-- Rank a full `Realization` (not just its role). Needed by rankers
    that depend on surface position (Rambow 1993) or information status
    (Strube-Hahn 1999); `CfRanker R` lifts here via `cfRankerOf_of_role`. -/
class CfRankerOf (E : Type*) (R : Type*) where
  rank : Realization E R → Nat

/-- Default lift: rank by role only via `r.role`. Low priority so
    per-realization instances win. -/
instance (priority := low) cfRankerOf_of_role {E R : Type*} [r : CfRanker R] :
    CfRankerOf E R where
  rank rl := r.rank rl.role

/-! ### Realizes / Pronominalizes Plug-Ins -/

/-- "u realizes e": the entity `e` is among the referents contributed
    by `u`. `outParam E` so typeclass search infers entity type from `U`. -/
class Realizes (U : Type*) (E : outParam (Type*)) where
  /-- The predicate "u realizes e". -/
  Rel : U → E → Prop
  /-- The relation is pointwise decidable. -/
  decRel : ∀ u e, Decidable (Rel u e)

attribute [reducible, instance] Realizes.decRel

/-- "u realizes e", as a `Prop`. Ergonomic alias for `Realizes.Rel`. -/
abbrev realizes {U : Type*} {E : Type*} [Realizes U E] (u : U) (e : E) : Prop :=
  Realizes.Rel u e

/-- "u pronominalizes e": some realization of `e` in `u` is pronominal. -/
class Pronominalizes (U : Type*) (E : outParam (Type*)) where
  /-- The predicate "u pronominalizes e". -/
  Rel : U → E → Prop
  /-- The relation is pointwise decidable. -/
  decRel : ∀ u e, Decidable (Rel u e)

attribute [reducible, instance] Pronominalizes.decRel

/-- "u pronominalizes e", as a `Prop`. Ergonomic alias for `Pronominalizes.Rel`. -/
abbrev pronominalizes {U : Type*} {E : Type*} [Pronominalizes U E] (u : U) (e : E) : Prop :=
  Pronominalizes.Rel u e

end Discourse.Centering
