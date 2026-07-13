/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.Language
import Linglib.Phonology.Autosegmental.NormalForm

/-!
# Autosegmental Strictly Local stringsets

[jardine-2019]'s class `ASL^g`: a stringset described by a forbidden-subgraph grammar
`B` over autosegmental representations, interpreted through a realization `g`
(`Realization.lean`). A string is in the class iff its realization avoids every
forbidden subgraph in `B`.

This unifies the autosegmental and subregular layers. It is the *same construction* as
the tier-based strictly local sets: both a subregular class as the **preimage of a
local base condition along a free-monoid homomorphism**.

```
  TSL  =  tierProject ⁻¹' (SL-language)        -- string→tier-string projection
  ASL  =  AR.realize g₀  ⁻¹' { A | isFreeOf B A } -- string→AR realization
```

`tierProject` (`Core/Computability/Subregular/Language/TierStrictlyLocal.lean`) and
`AR.realize` (`Realization.lean`) are
both concat-distributing free-monoid homs; the difference is only the codomain — a
tier string (discarding off-tier material) vs an AR (keeping the association lines).
That extra structure is why [jardine-2019] finds `ASL` and `TSL` incomparable.
-/

namespace Autosegmental

variable {S : Type*} {α β : Type*}

/-! ### ASL in coordinates -/

section Coordinate

variable {ι : Type*} [Finite ι] {τ : ι → Type*}

/-- **The Autosegmental Strictly Local stringset** on the graph foundation:
    strings whose realization avoids every forbidden factor — the preimage of
    the banned-subgraph object property along `realize`, the same shape as
    `TSL.lang = tierProject ⁻¹' (SL-language)`. -/
def AR.ASL (g₀ : S → AR (Sigma.fst : ((i : ι) × τ i) → ι))
    [∀ s, Finite (g₀ s).obj.V]
    (B : List {F : AR (Sigma.fst : ((i : ι) × τ i) → ι) // Finite F.obj.V}) :
    Language S :=
  { w | (realize g₀ w).Free B }

@[simp] theorem AR.mem_ASL
    {g₀ : S → AR (Sigma.fst : ((i : ι) × τ i) → ι)}
    [∀ s, Finite (g₀ s).obj.V]
    {B : List {F : AR (Sigma.fst : ((i : ι) × τ i) → ι) // Finite F.obj.V}}
    {w : List S} : w ∈ AR.ASL g₀ B ↔ (realize g₀ w).Free B := Iff.rfl

end Coordinate

end Autosegmental
