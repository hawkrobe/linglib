module

public import Mathlib.Order.Hom.Basic

/-!
# Products of order isomorphisms

[UPSTREAM] Mathlib has `Equiv.prodCongr` and the lexicographic `OrderIso.prodLexCongr`, but no
order isomorphism between products ordered componentwise. This file supplies it.
-/

@[expose] public section

namespace OrderIso

variable {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

/-- The componentwise product of two order isomorphisms. -/
def prodCongr (e₁ : α ≃o β) (e₂ : γ ≃o δ) : α × γ ≃o β × δ where
  toEquiv := e₁.toEquiv.prodCongr e₂.toEquiv
  map_rel_iff' := and_congr e₁.map_rel_iff e₂.map_rel_iff

end OrderIso
