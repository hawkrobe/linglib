/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.AR
import Linglib.Phonology.OCP

/-!
# Constraint modularity as monoidal-subcategory closure

The monoidal product of the category of autosegmental representations
(`Autosegmental.AR`) is **morpheme concatenation**
(`Graph.concat`, [jardine-heinz-2015]). This file gives that product
its linguistic meaning: it classifies phonological well-formedness
constraints by how they interact with concatenation.

A constraint `P` is **morpheme-modular** — *strictly modular* in the
sense of [bermudez-otero-2012] — when its well-formed
representations are closed under `⊗`: concatenating two well-formed
morphemes yields a well-formed word, with no repair at the boundary.
Equivalently, `P`'s models form a **monoidal subcategory** of
`(AR, ⊗, 𝟙)`.

The classification is not vacuous — it discriminates:

* The **No-Crossing Constraint** ([goldsmith-1976],
  [pulleyblank-1986]) *is* morpheme-modular (`ncc_isConcatStable`).
  This is exactly the content witnessed by the `MonoidalCategory
  (AR α β)` instance: `concat` preserves planarity
  (`Graph.isPlanar_concat`), so the well-formed ARs are closed under
  `⊗`. The monoidal structure of `AR` *is* this theorem.
* The **OCP** ([mccarthy-1986]) is **not** morpheme-modular
  (`ocp_not_isConcatStable`): concatenation can place two identical
  autosegments adjacent across the morpheme boundary, a violation
  present in neither factor. The OCP-clean ARs are therefore *not* a
  monoidal subcategory — and that failure is precisely why the OCP
  drives a boundary *repair* (`OCP.collapse`,
  [mccarthy-1986]'s fusion; `collapse_repairs_boundary`).

The test that the structure is load-bearing rather than decorative:
one cannot bundle OCP-cleanness into the `AR` subtype the way
planarity is bundled, because there is no `isClean_concat` to supply
to `concat`. Inverting the constraint breaks the grounding by
construction.

## Main definitions

* `IsConcatStable P` — `P` is preserved by `empty` and by `concat`
  (the morpheme-modularity / monoidal-subcategory predicate).
* `UpperOCPClean` — the OCP as a constraint on an AR's autosegmental
  (upper) tier.

## Main results

* `ncc_isConcatStable` — the NCC is morpheme-modular.
* `ocp_not_isConcatStable` — the OCP is not.
* `ncc_modular_ocp_not` — the discriminating dichotomy.
* `collapse_repairs_boundary` — fusion restores OCP-cleanness across
  a concatenation boundary.
-/

namespace Autosegmental

variable {α β : Type*}

/-! ### Morpheme-modularity of a constraint -/

/-- A phonological well-formedness constraint `P` on autosegmental
    representations is **morpheme-modular** (strictly modular in the
    sense of [bermudez-otero-2012]) when it is stable under morpheme
    concatenation: the empty representation satisfies it, and
    concatenating two in-bounds satisfying representations yields a
    satisfying one, with no repair at the morpheme boundary.

    Equivalently, `P`'s models form a **monoidal subcategory** of
    `(AR, ⊗, 𝟙)` — closed under the tensor product `Graph.concat` and
    containing the tensor unit `Graph.empty`. The `A.InBounds`
    precondition mirrors `Graph.isPlanar_concat`: it is the structural
    requirement that `A`'s links fall within its tier lengths, so that
    `B`'s shifted links land clear of `A`'s. -/
def IsConcatStable (P : Graph α β → Prop) : Prop :=
  P Graph.empty ∧
  ∀ A B : Graph α β, A.InBounds → P A → P B → P (A.concat B)

/-! ### The No-Crossing Constraint is modular -/

/-- The No-Crossing Constraint ([goldsmith-1976],
    [pulleyblank-1986]) is morpheme-modular. This is the linguistic
    content witnessed by the `MonoidalCategory (AR α β)` instance:
    `Graph.concat` preserves planarity, so the well-formed ARs are
    closed under `⊗`. -/
theorem ncc_isConcatStable : IsConcatStable (α := α) (β := β) Graph.IsPlanar :=
  ⟨Graph.isPlanar_empty, fun A B hA hPA hPB => Graph.isPlanar_concat A B hA hPA hPB⟩

/-! ### The OCP is not modular -/

/-- The OCP ([mccarthy-1986]) as a constraint on autosegmental
    representations: the autosegmental (upper) tier has no adjacent
    identical elements. -/
def UpperOCPClean (g : Graph α β) : Prop := OCP.IsClean g.upper

instance [DecidableEq α] (g : Graph α β) : Decidable (UpperOCPClean g) :=
  inferInstanceAs (Decidable (OCP.IsClean g.upper))

/-- The OCP is **not** morpheme-modular: concatenation can create an
    adjacent identical autosegment pair at the morpheme boundary —
    a violation present in neither factor. Witnessed by two
    single-autosegment representations (`⟨[true], [], ∅⟩`) whose
    concatenation has upper tier `[true, true]`. The OCP-clean ARs are
    therefore not closed under `⊗` and do not form a monoidal
    subcategory; the boundary violation is what forces a repair
    (`OCP.collapse`; see `collapse_repairs_boundary`). -/
theorem ocp_not_isConcatStable :
    ¬ IsConcatStable (UpperOCPClean (α := Bool) (β := Unit)) := by
  rintro ⟨-, hstable⟩
  have h := hstable ⟨[true], [], ∅⟩ ⟨[true], [], ∅⟩ (by decide) (by decide) (by decide)
  revert h
  decide

/-- The discriminating dichotomy: the monoidal structure of `AR`
    classifies the NCC as morpheme-modular (closed under `⊗`) and the
    OCP as not (boundary-spanning). The two halves cannot be
    interchanged — that is what makes the monoidal product
    load-bearing rather than decorative. -/
theorem ncc_modular_ocp_not :
    IsConcatStable (Graph.IsPlanar (α := Bool) (β := Unit)) ∧
    ¬ IsConcatStable (UpperOCPClean (α := Bool) (β := Unit)) :=
  ⟨ncc_isConcatStable, ocp_not_isConcatStable⟩

/-! ### Fusion as the forced boundary repair -/

/-- Because the OCP is not concat-stable, well-formedness must be
    *restored* at the morpheme boundary by a repair. [mccarthy-1986]'s
    fusion (`OCP.collapse`) is exactly such a repair: it maps the
    autosegmental tier of any concatenation back into the OCP-clean
    set. The non-modularity of the OCP (`ocp_not_isConcatStable`) is
    what makes a repair *necessary*; this theorem exhibits one. -/
theorem collapse_repairs_boundary [DecidableEq α] (A B : Graph α β) :
    OCP.IsClean (OCP.collapse (A.concat B).upper) :=
  OCP.collapse_clean _

end Autosegmental
