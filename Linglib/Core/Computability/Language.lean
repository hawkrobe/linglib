module

public import Mathlib.Computability.Language

/-!
# Inverse images of languages

Mathlib's `Language.map f` takes the image of a language under a letter-to-letter map
`f : α → β`. This file adds its dual, the inverse image `Language.comap f`, the words whose
image lies in a language. The two form a Galois connection. A class of languages closed under
`comap` is invariant under a change of alphabet that reads each letter through `f`, such as a
projection of segments to the values of a feature.

[UPSTREAM] candidate for `Mathlib/Computability/Language.lean`.

## Main definitions

* `Language.comap`: the inverse image of a language under a letter-to-letter map.

## Main results

* `Language.gc_map_comap`: `map f` is left adjoint to `comap f`.
-/

@[expose] public section

namespace Language

variable {α β γ : Type*}

/-- The inverse image of a language under a letter-to-letter map of alphabets. -/
def comap (f : α → β) (L : Language β) : Language α := List.map f ⁻¹' L

@[simp] theorem mem_comap {f : α → β} {L : Language β} {w : List α} :
    w ∈ L.comap f ↔ w.map f ∈ L :=
  Iff.rfl

@[simp] theorem comap_id (L : Language α) : L.comap id = L := by
  simp [comap]

theorem comap_comap (g : β → γ) (f : α → β) (L : Language γ) :
    (L.comap g).comap f = L.comap (g ∘ f) := by
  simp [comap, Set.preimage_preimage]

theorem gc_map_comap (f : α → β) : GaloisConnection (map f) (comap f) :=
  fun _ _ ↦ Set.image_subset_iff

end Language
