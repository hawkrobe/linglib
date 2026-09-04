import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Hom.Basic

/-!
# Derivational economy

Economy of derivation ([chomsky-1991], [chomsky-1995]) compares the derivations that converge on
the same string with the same interpretation and keeps the least costly. The cost of a derivation
is the number of lexical items it draws, of Merge operations, of Agree operations and of
applications of ellipsis, the four counts [citko-gracanin-yuksek-2025] weigh when they argue that
multidominance is more economical than ellipsis; a derivation is more economical than another when
it is no worse on every count and better on one, the product order on `ℕ⁴`. That order is
well-founded (Dickson's lemma, `Pi.wellFoundedLT`), so every reference set has a winner
(`WellFoundedLT.exists_minimal`).

## Main definitions

* `DerivationCost`: the four counts, partially ordered as their profile in `Fin 4 → ℕ`.

## References

* [N. Chomsky, *Some notes on economy of derivation and representation* (1991)][chomsky-1991]
* [N. Chomsky, *The Minimalist Program* (1995)][chomsky-1995]
* [B. Citko and M. Gračanin-Yuksek, *Economy in PF reduction* (2025)][citko-gracanin-yuksek-2025]
-/

namespace Minimalist

/-- The cost of a derivation: the lexical items drawn, the Merge operations, the Agree operations
and the applications of ellipsis. -/
structure DerivationCost where
  lexicalItems : ℕ
  mergeOps : ℕ
  agreeOps : ℕ
  ellipsisOps : ℕ
  deriving Repr, DecidableEq

namespace DerivationCost

/-- The four counts as a vector. -/
def profile (c : DerivationCost) : Fin 4 → ℕ :=
  ![c.lexicalItems, c.mergeOps, c.agreeOps, c.ellipsisOps]

theorem profile_injective : Function.Injective profile := by
  rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h
  simp_all [profile, Matrix.vecCons_inj]

/-- A cost is at most another when it is at most on every count. -/
instance : PartialOrder DerivationCost := PartialOrder.lift profile profile_injective

instance : DecidableLE DerivationCost := λ a b =>
  inferInstanceAs (Decidable (∀ i, a.profile i ≤ b.profile i))

instance : DecidableLT DerivationCost := λ a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

/-- The costs embed in `Fin 4 → ℕ`. -/
def profileEmbedding : DerivationCost ↪o (Fin 4 → ℕ) := ⟨⟨profile, profile_injective⟩, Iff.rfl⟩

/-- Dickson's lemma: no derivation is beaten by an infinite descent of ever more economical
ones. -/
instance : WellFoundedLT DerivationCost := profileEmbedding.wellFoundedLT

end DerivationCost

end Minimalist
