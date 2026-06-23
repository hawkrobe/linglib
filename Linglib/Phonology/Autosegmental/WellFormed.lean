/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Linglib.Phonology.Autosegmental.AR

/-!
# The autosegmental category `WellFormedAR α β`

`WellFormedAR α β` is the category of **well-formed autosegmental representations**: the
full subcategory of the base category `AR α β` (`AR.lean`) cut out by
planarity — [goldsmith-1976]'s No-Crossing Constraint, equivalently
[pulleyblank-1986]'s reformulated Well-Formedness Condition.

In mathlib's pattern, `IsPlanar : ObjectProperty (AR α β)` is a property of
objects, and `WellFormedAR α β := IsPlanar.FullSubcategory`. Because planarity is a
**monoidal property** (`ObjectProperty.IsMonoidal`: it holds for the unit and is
stable under `⊗`), the `MonoidalCategory (WellFormedAR α β)` instance comes for free from
`ObjectProperty.fullMonoidalSubcategory` — the inclusion `WellFormedAR ⥤ AR` is monoidal
(`monoidalι`). That the well-formed ARs are closed under concatenation **is** the
NCC's morpheme-modularity ([bermudez-otero-2012]); see `Modularity.lean`.

The bundled name `WellFormedAR` matches the field's standard abbreviation across
[jardine-2017], [chandlee-jardine-2019], [burness-mcmullin-2020].

## Main definitions

* `Autosegmental.IsPlanar` — planarity as an `ObjectProperty (AR α β)`.
* `Autosegmental.IsPlanar.IsMonoidal` — planarity is a monoidal property.
* `Autosegmental.WellFormedAR α β` — the full monoidal subcategory of planar ARs.
-/

namespace Autosegmental

open CategoryTheory MonoidalCategory

variable {α β : Type*}

/-- Planarity (Goldsmith's NCC) as a property of the base object `AR`. -/
def IsPlanar : ObjectProperty (AR α β) := fun A => A.toGraph.IsPlanar

/-- Planarity is a **monoidal property**: the unit is planar and `concat`
    preserves planarity (using the left factor's in-boundedness via
    `Graph.isPlanar_concat`). This is the categorical content of the NCC's
    morpheme-modularity ([bermudez-otero-2012]) — see `Modularity.lean`. -/
instance instIsMonoidalIsPlanar : (IsPlanar (α := α) (β := β)).IsMonoidal where
  prop_unit := Graph.isPlanar_empty
  prop_tensor X₁ _X₂ h₁ h₂ := Graph.isPlanar_concat X₁.inBounds h₁ h₂

/-- The autosegmental category `WellFormedAR α β`: the full monoidal subcategory of `AR`
    cut out by planarity. Objects are planar in-bounds graphs; the
    `MonoidalCategory` instance is inherited from `AR` via
    `ObjectProperty.fullMonoidalSubcategory`. -/
abbrev WellFormedAR (α β : Type*) := (IsPlanar (α := α) (β := β)).FullSubcategory

namespace WellFormedAR

/-- Build a well-formed WellFormedAR from an in-bounds representation and a planarity
    proof. -/
abbrev mk (A : AR α β) (h : A.toGraph.IsPlanar) : WellFormedAR α β := ⟨A, h⟩

/-- The underlying graph of a well-formed WellFormedAR. -/
abbrev toGraph (X : WellFormedAR α β) : Graph α β := X.obj.toGraph

end WellFormedAR

end Autosegmental
