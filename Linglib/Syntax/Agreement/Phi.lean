/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Agreement.Bundle

/-!
# The φ-bundle capability

`HasPhi` equips a carrier with its agreement features as an `Agreement.Bundle`;
`HasPhi.Agree` is the induced agreement relation, compatibility of the bundles,
an unspecified dimension acting as a wildcard.
-/

/-- A φ-bearer is an expression that exposes its agreement features as a bundle. -/
class HasPhi (α : Type*) where
  /-- The agreement features. -/
  phi : α → Agreement.Bundle

export HasPhi (phi)

/-- A bundle bears itself. -/
instance : HasPhi Agreement.Bundle := ⟨id⟩

/-- A Universal Dependencies bundle bears what it ingests as. -/
instance : HasPhi UD.MorphFeatures := ⟨Agreement.Bundle.ofUD⟩

/-- Two φ-bearers agree when their bundles are compatible, an unspecified dimension acting
as a wildcard. -/
def HasPhi.Agree {α β : Type*} [HasPhi α] [HasPhi β] (a : α) (b : β) : Prop :=
  Compat (phi a) (phi b)

instance {α β : Type*} [HasPhi α] [HasPhi β] (a : α) (b : β) :
    Decidable (HasPhi.Agree a b) := by
  unfold HasPhi.Agree; infer_instance
