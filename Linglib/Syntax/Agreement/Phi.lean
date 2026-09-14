/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.UD.Basic

/-!
# The φ-bundle capability

`HasPhi` equips a carrier with its agreement φ-features (person, number,
gender) as a UD bundle; `HasPhi.Agree` is the induced agreement relation.
The per-axis analytical capabilities are `HasPerson`/`HasNumber`/`HasGender`;
`HasPhi` is their UD-realization face, the bundle φ-agreement
(`UD.MorphFeatures.compatible`) consumes.
-/

/-- A φ-bearer is an expression that exposes person, number, and gender for
agreement, as a UD feature bundle. -/
class HasPhi (α : Type*) where
  /-- The agreement φ-features (person/number/gender). -/
  phi : α → UD.MorphFeatures

export HasPhi (phi)

/-- A φ-bundle bears itself. -/
instance : HasPhi UD.MorphFeatures := ⟨id⟩

/-- Two φ-bearers agree when their features unify
(`UD.MorphFeatures.compatible`), an unspecified feature acting as a wildcard. -/
def HasPhi.Agree {α β : Type*} [HasPhi α] [HasPhi β] (a : α) (b : β) : Prop :=
  (phi a).compatible (phi b)

instance {α β : Type*} [HasPhi α] [HasPhi β] (a : α) (b : β) :
    Decidable (HasPhi.Agree a b) := by
  unfold HasPhi.Agree; infer_instance
