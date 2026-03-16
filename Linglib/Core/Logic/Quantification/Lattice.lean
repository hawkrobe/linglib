import Linglib.Core.Logic.Quantification.Properties

/-!
# Conservative GQ Lattice
@cite{elliott-2025}

Conservative GQs form a bounded distributive sublattice of `GQ α`.
The `DistribLattice` instance is inherited from Mathlib's Pi instances
(`Bool` is a `DistribLattice`, and `(α → Bool) → (α → Bool) → Bool`
lifts pointwise). Closure under `⊔`/`⊓` follows from
`conservative_gqJoin`/`conservative_gqMeet`.
-/

namespace Core.Quantification

variable {α : Type*}

-- ============================================================================
-- §12 — Conservative GQ Lattice (@cite{elliott-2025})
-- ============================================================================

/-- Conservative GQs form a sublattice of `GQ α`. The `DistribLattice`
    on `GQ α` is inherited from Mathlib's Pi instances (`Bool` is a
    `DistribLattice`, and `(α → Bool) → (α → Bool) → Bool` lifts
    pointwise). Closure under `⊔`/`⊓` follows from
    `conservative_gqJoin`/`conservative_gqMeet` (§8).

    Reference: Elliott, P. (2025). Determiners as predicates. SALT 35. -/
def conservativeSublattice : Sublattice (GQ α) where
  carrier := { q | Conservative q }
  supClosed' q₁ hq₁ q₂ hq₂ := conservative_gqJoin q₁ q₂ hq₁ hq₂
  infClosed' q₁ hq₁ q₂ hq₂ := conservative_gqMeet q₁ q₂ hq₁ hq₂

/-- Conservative GQs: the subtype of `GQ α` satisfying conservativity.
    Forms a bounded distributive lattice under pointwise Boolean operations. Meet is `∧`, join is `∨`, the order is
    pointwise implication. The Birkhoff representation theorem applied to
    this lattice yields polarized individuals as join-irreducible elements.

    The `DistribLattice` instance is inherited from `GQ α` via
    `Sublattice.instDistribLatticeCoe` — no manual axiom proofs needed. -/
abbrev ConsGQ (α : Type*) := conservativeSublattice (α := α)

namespace ConsGQ

variable {α : Type*}

-- Lattice operations agree with gqJoin/gqMeet (definitional)

/-- The join of conservative GQs agrees with `gqJoin`. -/
theorem sup_eq_gqJoin (q₁ q₂ : ConsGQ α) : (q₁ ⊔ q₂).1 = gqJoin q₁.1 q₂.1 := rfl

/-- The meet of conservative GQs agrees with `gqMeet`. -/
theorem inf_eq_gqMeet (q₁ q₂ : ConsGQ α) : (q₁ ⊓ q₂).1 = gqMeet q₁.1 q₂.1 := rfl

-- Bounds

instance : Bot (ConsGQ α) := ⟨⟨⊥, λ _ _ => rfl⟩⟩
instance : Top (ConsGQ α) := ⟨⟨⊤, λ _ _ => rfl⟩⟩

instance : OrderBot (ConsGQ α) where
  bot_le q := show ⊥ ≤ q.1 from bot_le

instance : OrderTop (ConsGQ α) where
  le_top q := show q.1 ≤ ⊤ from le_top

-- Simp API for downstream use

@[simp] theorem sup_val (q₁ q₂ : ConsGQ α) (R S : α → Bool) :
    (q₁ ⊔ q₂).1 R S = (q₁.1 R S || q₂.1 R S) := rfl

@[simp] theorem inf_val (q₁ q₂ : ConsGQ α) (R S : α → Bool) :
    (q₁ ⊓ q₂).1 R S = (q₁.1 R S && q₂.1 R S) := rfl

@[simp] theorem top_val (R S : α → Bool) : (⊤ : ConsGQ α).1 R S = true := rfl

@[simp] theorem bot_val (R S : α → Bool) : (⊥ : ConsGQ α).1 R S = false := rfl

end ConsGQ

end Core.Quantification
