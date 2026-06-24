/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Language.StrictlyLocalStarFree
import Linglib.Core.Computability.Subregular.Language.TierStrictlyLocal

/-!
# Tier-based strictly local languages are star-free

Over a finite alphabet, every tier-based strictly `k`-local language is star-free:
`Language.IsTierStrictlyLocal.isStarFree`. This places `TSL_k ⊆ SF` inside the subregular
hierarchy ([heinz-rawal-tanner-2011]), completing `SL_k ⊆ TSL_k ⊆ SF` (the first inclusion is
`Language.IsStrictlyLocal.toIsTierStrictlyLocal`).

## Construction

A TSL grammar's language is the preimage `tierProject T ⁻¹' (permitted.language k)` under tier
erasure. Tier erasure is `List.filter`, hence a **monoid hom** `Subregular.tierProjectHom`
(`map_mul'` is `List.filter_append`). The permitted-factor language is `SL_k`, so star-free by
`Language.IsStrictlyLocal.isStarFree`; star-freeness is closed under inverse homomorphism
(`Language.IsStarFree.comap`), so the preimage is star-free.

`[Finite α]` flows in from `IsStrictlyLocal.isStarFree`: SL (and so TSL) over an infinite
alphabet need not even be regular.

## Main results

* `Subregular.tierProjectHom` — tier erasure bundled as `FreeMonoid α →* FreeMonoid α`.
* `Language.IsTierStrictlyLocal.isStarFree` — `IsTierStrictlyLocal k L → IsStarFree L` (finite `α`).
-/

namespace Subregular

variable {α : Type*} (T : α → Prop) [DecidablePred T]

/-- **Tier erasure as a monoid hom** `FreeMonoid α →* FreeMonoid α`: `tierProject T` is
`List.filter`, which preserves `1` (`[]`) and `*` (`++`, via `List.filter_append`). -/
def tierProjectHom : FreeMonoid α →* FreeMonoid α where
  toFun := tierProject T
  map_one' := tierProject_nil T
  map_mul' u v := List.filter_append u v

@[simp] lemma tierProjectHom_apply (w : FreeMonoid α) :
    tierProjectHom T w = tierProject T w := rfl

end Subregular

namespace Language

variable {α : Type*} [Finite α] {k : ℕ} {L : Language α}

open Subregular

/-- **Tier-based strictly local languages are star-free** ([heinz-rawal-tanner-2011]). Over a
finite alphabet, a TSL language is the inverse image of an `SL_k` language under the
tier-erasure homomorphism, and star-freeness is closed under inverse homomorphism
(`IsStarFree.comap`), so `TSL_k ⊆ SF`. -/
theorem IsTierStrictlyLocal.isStarFree (h : IsTierStrictlyLocal k L) : L.IsStarFree := by
  obtain ⟨G, rfl⟩ := h
  have hsf : (G.permitted.language k).IsStarFree :=
    IsStrictlyLocal.isStarFree ⟨G.permitted, rfl⟩
  have := hsf.comap (tierProjectHom G.tier)
  rwa [show {w : List α | tierProjectHom G.tier (FreeMonoid.ofList w) ∈ G.permitted.language k}
      = G.lang from rfl] at this

end Language
