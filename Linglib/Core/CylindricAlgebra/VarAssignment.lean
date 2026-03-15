import Linglib.Core.CylindricAlgebra
import Linglib.Core.Semantics.Intension

/-!
# Bridge: VarAssignment = Assignment
@cite{henkin-monk-tarski-1971} @cite{partee-1973} @cite{heim-kratzer-1998}

The generic `VarAssignment D` (from `Core.Semantics.Intension`) and the
canonical `Assignment E` (from `Core.Assignment`) are the same type:
both are `ℕ → D`. Their update operations are the same function.

This makes every instantiation of `VarAssignment` — entity assignments
(@cite{heim-kratzer-1998}), temporal assignments (@cite{partee-1973}),
situation assignments (@cite{percus-2000}) — an instance of the same
cylindric set algebra defined in `Core.CylindricAlgebra`.

## Instantiations

| Framework | Domain `D` | Assignment type |
|---|---|---|
| Heim & Kratzer | `Entity` | `Assignment Entity` |
| Partee 1973 | `Time` | `TemporalAssignment Time` |
| Percus 2000 | `Situation W Time` | `SituationAssignment W Time` |
| CDRT (Muskens) | `E` | `Register E` |
| PLA (@cite{dekker-2012}) | `E` | `VarIdx → E` |

All share the same cylindric algebra axioms (C1–C7) and the same
substitution theory (HMT §1.5).
-/

namespace Core.CylindricAlgebra

open Core (Assignment)
open Core.VarAssignment (VarAssignment updateVar lookupVar varLambdaAbs)

-- ════════════════════════════════════════════════════════════════
-- § Type bridge
-- ════════════════════════════════════════════════════════════════

/-- `VarAssignment D` IS `Assignment D` — both are `ℕ → D`. -/
theorem varAssignment_eq_assignment {D : Type*} :
    VarAssignment D = Assignment D := rfl

-- ════════════════════════════════════════════════════════════════
-- § Operation bridges
-- ════════════════════════════════════════════════════════════════

/-- `updateVar` IS `Assignment.update`. -/
theorem updateVar_eq_update {D : Type*}
    (g : VarAssignment D) (n : ℕ) (d : D) :
    updateVar g n d = Assignment.update g n d := by
  ext i; simp [updateVar, Assignment.update]

/-- `lookupVar n g` is just `g n` — register projection. -/
theorem lookupVar_eq_apply {D : Type*} (n : ℕ) (g : VarAssignment D) :
    lookupVar n g = g n := rfl

-- ════════════════════════════════════════════════════════════════
-- § Cylindric algebra operations via VarAssignment
-- ════════════════════════════════════════════════════════════════

/-- Existential quantification over a VarAssignment register =
cylindrification on the underlying Assignment. -/
theorem exists_updateVar_iff_cylindrify {D : Type*} (n : ℕ)
    (p : VarAssignment D → Prop) (g : VarAssignment D) :
    (∃ d, p (updateVar g n d)) ↔ cylindrify n p g := by
  simp only [cylindrify]
  constructor
  · rintro ⟨d, h⟩; exact ⟨d, by rw [updateVar_eq_update] at h; exact h⟩
  · rintro ⟨d, h⟩; exact ⟨d, by rw [updateVar_eq_update]; exact h⟩

/-- Register equality = diagonal element. -/
theorem lookupVar_eq_iff_diagonal {D : Type*} (n m : ℕ) (g : VarAssignment D) :
    lookupVar n g = lookupVar m g ↔ diagonal n m g := by
  simp only [lookupVar, diagonal]

/-- Lambda abstraction is the integrand of cylindrification:
`varLambdaAbs n body g d = body (g[n↦d])`. Existential closure over `d`
gives cylindrification `cₙ(body)`. -/
theorem varLambdaAbs_integrand {D : Type*} {α : Type*} (n : ℕ)
    (body : VarAssignment D → α) (g : VarAssignment D) (d : D) :
    varLambdaAbs n body g d = body (updateVar g n d) := rfl

end Core.CylindricAlgebra
