/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.WellFormed
import Linglib.Phonology.OCP

/-!
# Constraint modularity as monoidal-subcategory closure

The monoidal product of the autosegmental category (`Autosegmental.WellFormedAR`) is
**morpheme concatenation** (`AR.concat`, [jardine-heinz-2015]). This file gives
that product its linguistic meaning: it classifies phonological well-formedness
constraints by how they interact with concatenation.

A constraint `P` is **morpheme-modular** — *strictly modular* in the sense of
[bermudez-otero-2012] — when its well-formed representations are closed under `⊗`:
concatenating two well-formed morphemes yields a well-formed word, with no repair
at the boundary. Mathlib's name for exactly this is `ObjectProperty.IsMonoidal`:
`P` holds for the unit and is stable under `⊗`. So *morpheme-modular* **is**
`P.IsMonoidal`, and the well-formed objects form a monoidal subcategory.

The classification is not vacuous — it discriminates:

* The **No-Crossing Constraint** ([goldsmith-1976], [pulleyblank-1986]) *is*
  morpheme-modular: `IsPlanar.IsMonoidal` (`instIsMonoidalIsPlanar`). This is
  exactly the content of the `MonoidalCategory (WellFormedAR α β)` instance — `concat`
  preserves planarity, so the well-formed ARs are a monoidal subcategory of
  `AR`. The monoidal structure of `WellFormedAR` *is* this theorem.
* The **OCP** ([mccarthy-1986]) is **not** morpheme-modular
  (`ocp_not_isMonoidal`): concatenation can place two identical autosegments
  adjacent across the morpheme boundary, a violation present in neither factor.
  The OCP-clean ARs are therefore *not* a monoidal subcategory — and that failure
  is precisely why the OCP drives a boundary *repair* (`OCP.collapse`,
  [mccarthy-1986]'s fusion; `collapse_repairs_boundary`).

The test that the structure is load-bearing rather than decorative: one cannot
bundle OCP-cleanness into the `WellFormedAR` subcategory the way planarity is, because there
is no `IsMonoidal` instance for it. Inverting the constraint breaks the grounding
by construction.

## Main results

* `ncc_isMonoidal` — the NCC is morpheme-modular (the `WellFormedAR` monoidal structure).
* `ocp_not_isMonoidal` — the OCP is not.
* `ncc_modular_ocp_not` — the discriminating dichotomy.
* `collapse_repairs_boundary` — fusion restores OCP-cleanness across a boundary.
-/

namespace Autosegmental

open CategoryTheory MonoidalCategory

variable {α β : Type*}

/-! ### The No-Crossing Constraint is morpheme-modular -/

/-- The No-Crossing Constraint ([goldsmith-1976], [pulleyblank-1986]) is
    **morpheme-modular**: planarity is a monoidal property of `AR`, so the
    planar (well-formed) ARs form the monoidal subcategory `WellFormedAR`. This is the
    linguistic content witnessed by the `MonoidalCategory (WellFormedAR α β)` instance. -/
theorem ncc_isMonoidal : (IsPlanar (α := α) (β := β)).IsMonoidal := inferInstance

/-! ### The OCP is not morpheme-modular -/

/-- The OCP ([mccarthy-1986]) as a property of `AR`: the autosegmental (upper)
    tier has no adjacent identical elements. -/
def UpperOCPClean : ObjectProperty (AR α β) := fun A => OCP.IsClean A.upper

instance [DecidableEq α] (A : AR α β) : Decidable (UpperOCPClean A) :=
  inferInstanceAs (Decidable (OCP.IsClean A.upper))

/-- A single-autosegment representation `⟨[true], [], ∅⟩`; concatenating it with
    itself produces the OCP-violating tier `[true, true]`. -/
private def ocpWitness : AR Bool Unit := ⟨⟨[true], [], ∅⟩, by decide⟩

/-- The OCP is **not** morpheme-modular: concatenation can create an adjacent
    identical autosegment pair at the morpheme boundary — a violation present in
    neither factor. Witnessed by two single-autosegment reps (`⟨[true], [], ∅⟩`)
    whose concatenation has upper tier `[true, true]`. The OCP-clean ARs are
    therefore not closed under `⊗` and do not form a monoidal subcategory; the
    boundary violation is what forces a repair (`OCP.collapse`; see
    `collapse_repairs_boundary`). -/
theorem ocp_not_isMonoidal : ¬ (UpperOCPClean (α := Bool) (β := Unit)).IsMonoidal := by
  intro h
  haveI := h.toTensorLE
  have hc : UpperOCPClean (ocpWitness ⊗ ocpWitness) :=
    ObjectProperty.prop_tensor (show UpperOCPClean ocpWitness by decide)
      (show UpperOCPClean ocpWitness by decide)
  revert hc
  decide

/-- The discriminating dichotomy: the monoidal structure of `WellFormedAR` classifies the
    NCC as morpheme-modular (closed under `⊗`) and the OCP as not
    (boundary-spanning). The two halves cannot be interchanged — that is what
    makes the monoidal product load-bearing rather than decorative. -/
theorem ncc_modular_ocp_not :
    (IsPlanar (α := Bool) (β := Unit)).IsMonoidal ∧
    ¬ (UpperOCPClean (α := Bool) (β := Unit)).IsMonoidal :=
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
