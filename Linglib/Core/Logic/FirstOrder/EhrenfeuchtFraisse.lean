import Linglib.Core.Logic.FirstOrder.QuantifierRank
import Mathlib.ModelTheory.Bundled

/-!
# Ehrenfeucht–Fraïssé: n-equivalence and first-order inexpressibility

`[UPSTREAM]` candidate. `M ≡ₙ N` (`NEquiv n M N`) holds when `M` and `N` agree on
every sentence of quantifier rank ≤ `n` — the finite-rank refinement of mathlib's
`ElementarilyEquivalent` (`= ∀ n, NEquiv n`). On it rests the
**Ehrenfeucht–Fraïssé inexpressibility** corollary: a property of structures that
can be `≡ₙ`-fooled for every `n` is not first-order definable. This is the abstract
engine behind `most ∉ FO` (`Studies.BarwiseCooper1981`), parity, connectivity, etc.

mathlib has the ∞-rank apparatus (`ElementarilyEquivalent`, the unbounded
back-and-forth `IsExtensionPair`) but not this finite-rank layer; quantifier rank
itself is `BoundedFormula.qr` (this directory).

## Main definitions / results

* `FirstOrder.Language.NEquiv` — n-equivalence of structures.
* `FirstOrder.Language.FODefinable` — a structure property captured by a sentence.
* `FirstOrder.Language.not_foDefinable_of_nEquiv` — the EF inexpressibility corollary.
-/

universe u v w

namespace FirstOrder.Language

open BoundedFormula CategoryTheory
open scoped FirstOrder

variable {L : Language.{u, v}} {n m : ℕ}

/-- `n`-equivalence: `M` and `N` satisfy the same sentences of quantifier rank ≤ `n`.
The finite-rank refinement of `ElementarilyEquivalent` (`≅[L]`), which is the `n = ∞`
case (`elementarilyEquivalent_iff_forall_nEquiv`). -/
def NEquiv (n : ℕ) (M N : Bundled.{w} L.Structure) : Prop :=
  ∀ φ : L.Sentence, φ.qr ≤ n → (M ⊨ φ ↔ N ⊨ φ)

namespace NEquiv

variable {M N P : Bundled.{w} L.Structure}

@[refl] theorem refl (n : ℕ) (M : Bundled.{w} L.Structure) : NEquiv n M M :=
  fun _ _ => Iff.rfl

theorem symm (h : NEquiv n M N) : NEquiv n N M := fun φ hφ => (h φ hφ).symm

theorem trans (h₁ : NEquiv n M N) (h₂ : NEquiv n N P) : NEquiv n M P :=
  fun φ hφ => (h₁ φ hφ).trans (h₂ φ hφ)

/-- `n`-equivalence is antitone in the rank: agreeing up to rank `m` implies agreeing
up to any smaller rank `n`. -/
theorem mono (hnm : n ≤ m) (h : NEquiv m M N) : NEquiv n M N :=
  fun φ hφ => h φ (hφ.trans hnm)

end NEquiv

/-- `ElementarilyEquivalent` is exactly `n`-equivalence at every rank. -/
theorem elementarilyEquivalent_iff_forall_nEquiv (M N : Bundled.{w} L.Structure) :
    (M ≅[L] N) ↔ ∀ n, NEquiv n M N := by
  rw [elementarilyEquivalent_iff]
  exact ⟨fun h _ φ _ => h φ, fun h φ => h φ.qr φ le_rfl⟩

/-- A property of structures is *first-order definable* when some sentence captures
exactly the structures with the property. -/
def FODefinable (P : Bundled.{w} L.Structure → Prop) : Prop :=
  ∃ φ : L.Sentence, ∀ M : Bundled.{w} L.Structure, (M ⊨ φ ↔ P M)

/-- **Ehrenfeucht–Fraïssé inexpressibility.** If for every rank `n` there are
structures that are `n`-equivalent yet separated by `P` (one has it, the other does
not), then `P` is not first-order definable. The standard route to FO-inexpressibility:
the sentence's own quantifier rank is the `n` at which the witnesses fool it. -/
theorem not_foDefinable_of_nEquiv {P : Bundled.{w} L.Structure → Prop}
    (h : ∀ n, ∃ M N : Bundled.{w} L.Structure, NEquiv n M N ∧ ¬ (P M ↔ P N)) :
    ¬ FODefinable P := by
  rintro ⟨φ, hφ⟩
  obtain ⟨M, N, hMN, hne⟩ := h φ.qr
  exact hne ((hφ M).symm.trans ((hMN φ le_rfl).trans (hφ N)))

end FirstOrder.Language
