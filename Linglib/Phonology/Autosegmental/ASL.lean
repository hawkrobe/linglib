/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.Language
import Linglib.Phonology.Autosegmental.Realization
import Linglib.Phonology.Autosegmental.Embedding

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
  ASL  =  realize g₀  ⁻¹' { A | isFreeOf B A } -- string→AR realization
```

`tierProject` (`Core/Computability/Subregular/Language/TierStrictlyLocal.lean`) and
`realize` (`Realization.lean`) are
both concat-distributing free-monoid homs; the difference is only the codomain — a
tier string (discarding off-tier material) vs an AR (keeping the association lines).
That extra structure is why [jardine-2019] finds `ASL` and `TSL` incomparable.
-/

namespace Autosegmental

variable {S : Type*} {α β : Type*}

/-- A banned-subgraph grammar as an AR **object-property**: the ARs free of every
    forbidden pattern in `B` ([jardine-2016-diss] Ch. 5's `L^NL_G`, packaged for `AR`). -/
def isFreeOf (B : List (Graph α β)) (A : AR α β) : Prop := A.toGraph.Free B

instance [DecidableEq α] [DecidableEq β] (B : List (Graph α β)) (A : AR α β) :
    Decidable (isFreeOf B A) := inferInstanceAs (Decidable (A.toGraph.Free B))

/-- **The Autosegmental Strictly Local stringset** of a realization `g₀` and a forbidden
    grammar `B` ([jardine-2019]): the strings whose realization avoids `B`. The preimage
    of the AR object-property `isFreeOf B` along `realize g₀` — the same shape as
    `TSL.lang = tierProject ⁻¹' (SL-language)`, with the AR realization in place of the
    tier projection. -/
def ASL (g₀ : S → AR α β) (B : List (Graph α β)) : Language S :=
  realize g₀ ⁻¹' { A | isFreeOf B A }

@[simp] theorem mem_ASL (g₀ : S → AR α β) (B : List (Graph α β)) (w : List S) :
    w ∈ ASL g₀ B ↔ isFreeOf B (realize g₀ w) := Iff.rfl

instance [DecidableEq α] [DecidableEq β] (g₀ : S → AR α β) (B : List (Graph α β))
    (w : List S) : Decidable (w ∈ ASL g₀ B) :=
  inferInstanceAs (Decidable (isFreeOf B (realize g₀ w)))

/-- A stringset is **autosegmental strictly local** when some realization and forbidden
    grammar present it ([jardine-2019]). -/
def IsASL (L : Language S) : Prop :=
  ∃ (α β : Type) (g₀ : S → AR α β) (B : List (Graph α β)), L = ASL g₀ B

end Autosegmental
