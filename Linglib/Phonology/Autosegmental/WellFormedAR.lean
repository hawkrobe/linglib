/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Linglib.Phonology.Autosegmental.AR
import Linglib.Phonology.OCP

/-!
# The well-formed autosegmental category `WellFormedAR α β`

`WellFormedAR α β` is the category of **well-formed autosegmental representations**: the
full subcategory of the base category `AR α β` (`AR.lean`) cut out by
planarity — [goldsmith-1976]'s No-Crossing Constraint, equivalently
[pulleyblank-1986]'s reformulated Well-Formedness Condition.

In mathlib's pattern, `isPlanar : ObjectProperty (AR α β)` is a property of
objects, and `WellFormedAR α β := isPlanar.FullSubcategory`. Because planarity is a
**monoidal property** (`ObjectProperty.IsMonoidal`: it holds for the unit and is
stable under `⊗`), the `MonoidalCategory (WellFormedAR α β)` instance comes for free from
`ObjectProperty.fullMonoidalSubcategory` — the inclusion `WellFormedAR ⥤ AR` is monoidal
(`monoidalι`). The bundled name `WellFormedAR` matches the field's standard
abbreviation across [jardine-2017], [chandlee-jardine-2019], [burness-mcmullin-2020].

## Constraint modularity

The monoidal product is **morpheme concatenation** (`AR.concat`,
[jardine-heinz-2015]); the second half of this file gives it linguistic meaning by
classifying constraints by how they interact with it. A constraint `P` is
**morpheme-modular** — *strictly modular* in the sense of [bermudez-otero-2012] —
when its well-formed representations are closed under `⊗`. That is exactly
`ObjectProperty.IsMonoidal`. The classification discriminates:

* The **No-Crossing Constraint** ([goldsmith-1976], [pulleyblank-1986]) *is*
  morpheme-modular (`ncc_isMonoidal`) — which is precisely the content of the
  `MonoidalCategory (WellFormedAR α β)` instance.
* The **OCP** ([mccarthy-1986]) is **not** (`ocp_not_isMonoidal`): concatenation can
  place two identical autosegments adjacent across the morpheme boundary, a
  violation present in neither factor — so the OCP-clean ARs do not form a monoidal
  subcategory, and the OCP drives a boundary *repair* (`OCP.collapse`).

## Main definitions

* `Autosegmental.isPlanar` — planarity as an `ObjectProperty (AR α β)`.
* `Autosegmental.WellFormedAR α β` — the full monoidal subcategory of planar ARs.

## Main results

* `instIsMonoidalIsPlanar` / `ncc_isMonoidal` — the NCC is morpheme-modular.
* `ocp_not_isMonoidal` — the OCP is not.
* `ncc_modular_ocp_not` — the discriminating dichotomy.
* `collapse_repairs_boundary` — fusion restores OCP-cleanness across a boundary.
-/

namespace Autosegmental

open CategoryTheory MonoidalCategory

variable {α β : Type*}

/-! ### Planarity as a monoidal object-property -/

/-- Planarity (Goldsmith's NCC) as a property of the base object `AR`. -/
def isPlanar : ObjectProperty (AR α β) := fun A => A.toGraph.IsPlanar

/-- Planarity is a **monoidal property**: the unit is planar and `concat`
    preserves planarity (using the left factor's in-boundedness via
    `Graph.isPlanar_concat`). This is the categorical content of the NCC's
    morpheme-modularity ([bermudez-otero-2012]). -/
instance instIsMonoidalIsPlanar : (isPlanar (α := α) (β := β)).IsMonoidal where
  prop_unit := Graph.isPlanar_empty
  prop_tensor X₁ _X₂ h₁ h₂ := Graph.isPlanar_concat X₁.inBounds h₁ h₂

/-- The well-formed autosegmental category `WellFormedAR α β`: the full monoidal
    subcategory of `AR` cut out by planarity. Objects are planar in-bounds graphs;
    the `MonoidalCategory` instance is inherited from `AR` via
    `ObjectProperty.fullMonoidalSubcategory`. -/
abbrev WellFormedAR (α β : Type*) := (isPlanar (α := α) (β := β)).FullSubcategory

namespace WellFormedAR

/-- Build a `WellFormedAR` from an in-bounds representation and a planarity proof. -/
abbrev mk (A : AR α β) (h : A.toGraph.IsPlanar) : WellFormedAR α β := ⟨A, h⟩

end WellFormedAR

/-! ### The No-Crossing Constraint is morpheme-modular -/

/-- The No-Crossing Constraint ([goldsmith-1976], [pulleyblank-1986]) is
    **morpheme-modular**: planarity is a monoidal property of `AR`, so the planar
    (well-formed) ARs form the monoidal subcategory `WellFormedAR`. This is the
    linguistic content witnessed by the `MonoidalCategory (WellFormedAR α β)` instance. -/
theorem ncc_isMonoidal : (isPlanar (α := α) (β := β)).IsMonoidal := inferInstance

/-! ### The OCP is not morpheme-modular -/

/-- The OCP ([mccarthy-1986]) as a property of `AR`: the autosegmental (upper)
    tier has no adjacent identical elements. -/
def upperOCPClean : ObjectProperty (AR α β) := fun A => OCP.IsClean A.upper

instance [DecidableEq α] (A : AR α β) : Decidable (upperOCPClean A) :=
  inferInstanceAs (Decidable (OCP.IsClean A.upper))

/-- A single-autosegment representation `⟨[true], [], ∅⟩`; concatenating it with
    itself produces the OCP-violating tier `[true, true]`. `Bool`/`Unit` is the
    smallest label/backbone pair admitting two equal upper elements. -/
private def ocpWitness : AR Bool Unit := ⟨⟨[true], [], ∅⟩, by decide⟩

/-- The OCP is **not** morpheme-modular: concatenation can create an adjacent
    identical autosegment pair at the morpheme boundary — a violation present in
    neither factor. Witnessed by two single-autosegment reps (`⟨[true], [], ∅⟩`)
    whose concatenation has upper tier `[true, true]`. The OCP-clean ARs are
    therefore not closed under `⊗`; the boundary violation is what forces a repair
    (`OCP.collapse`; see `collapse_repairs_boundary`). -/
theorem ocp_not_isMonoidal : ¬ (upperOCPClean (α := Bool) (β := Unit)).IsMonoidal := by
  intro h
  haveI := h.toTensorLE
  have hc : upperOCPClean (ocpWitness ⊗ ocpWitness) :=
    ObjectProperty.prop_tensor (show upperOCPClean ocpWitness by decide)
      (show upperOCPClean ocpWitness by decide)
  revert hc
  decide

/-- The discriminating dichotomy: the monoidal structure of `WellFormedAR` classifies the
    NCC as morpheme-modular (closed under `⊗`) and the OCP as not
    (boundary-spanning). The two halves cannot be interchanged — that is what
    makes the monoidal product load-bearing rather than decorative. -/
theorem ncc_modular_ocp_not :
    (isPlanar (α := Bool) (β := Unit)).IsMonoidal ∧
    ¬ (upperOCPClean (α := Bool) (β := Unit)).IsMonoidal :=
  ⟨ncc_isMonoidal, ocp_not_isMonoidal⟩

/-! ### Fusion as the forced boundary repair -/

/-- Because the OCP is not morpheme-modular, well-formedness must be *restored* at
    the morpheme boundary by a repair. [mccarthy-1986]'s fusion (`OCP.collapse`)
    is exactly such a repair: it maps the autosegmental tier of any concatenation
    back into the OCP-clean set. The non-modularity of the OCP
    (`ocp_not_isMonoidal`) is what makes a repair *necessary*; this theorem
    exhibits one. -/
theorem collapse_repairs_boundary [DecidableEq α] (A B : Graph α β) :
    OCP.IsClean (OCP.collapse (A.concat B).upper) :=
  OCP.collapse_clean _

end Autosegmental
