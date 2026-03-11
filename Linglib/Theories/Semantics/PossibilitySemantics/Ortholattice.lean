import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Disjoint

/-!
# Orthocomplemented Lattices
@cite{holliday-mandelkern-2024}

An orthocomplemented lattice (ortholattice) is a bounded lattice equipped with
an involutive, order-reversing complement satisfying non-contradiction and
excluded middle. Ortholattices generalize Boolean algebras by dropping
distributivity — the algebraic foundation of possibility semantics.

## Main definitions

* `OrthocomplementedLattice` — typeclass for ortholattices

## Main results

* De Morgan laws: `compl_sup`, `compl_inf`
* `ComplementedLattice` instance
* Every `BooleanAlgebra` is an `OrthocomplementedLattice`

## What fails

Not every ortholattice satisfies distributivity (`a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)`),
pseudocomplementation (`a ⊓ b = ⊥ → b ≤ aᶜ`), or orthomodularity
(`a ≤ b → b = a ⊔ (aᶜ ⊓ b)`). Concrete counterexamples live in
`PossibilitySemantics/Epistemic.lean`.
-/

namespace Semantics.PossibilitySemantics

/-- An orthocomplemented lattice (ortholattice) is a bounded lattice with a
    complement `ᶜ` that is involutive and order-reversing, satisfying
    non-contradiction and excluded middle.

    Every `BooleanAlgebra` is an ortholattice. The converse fails:
    ortholattices need not be distributive. -/
class OrthocomplementedLattice (α : Type*) extends Lattice α, BoundedOrder α, Compl α where
  /-- Complement is involutive: `aᶜᶜ = a`. -/
  compl_compl (a : α) : aᶜᶜ = a
  /-- Complement is order-reversing. -/
  compl_antitone {a b : α} : a ≤ b → bᶜ ≤ aᶜ
  /-- Non-contradiction: `a ⊓ aᶜ ≤ ⊥`. -/
  inf_compl_le_bot (a : α) : a ⊓ aᶜ ≤ ⊥
  /-- Excluded middle: `⊤ ≤ a ⊔ aᶜ`. -/
  top_le_sup_compl (a : α) : ⊤ ≤ a ⊔ aᶜ

namespace OrthocomplementedLattice

variable {α : Type*} [OrthocomplementedLattice α] {a b : α}

-- ════════════════════════════════════════════════════
-- § 1. Basic Identities
-- ════════════════════════════════════════════════════

@[simp]
theorem inf_compl_eq_bot (a : α) : a ⊓ aᶜ = ⊥ :=
  le_antisymm (OrthocomplementedLattice.inf_compl_le_bot a) bot_le

@[simp]
theorem sup_compl_eq_top (a : α) : a ⊔ aᶜ = ⊤ :=
  le_antisymm le_top (OrthocomplementedLattice.top_le_sup_compl a)

@[simp]
theorem compl_bot : (⊥ : α)ᶜ = ⊤ := by
  have h := sup_compl_eq_top (⊥ : α); rwa [bot_sup_eq] at h

@[simp]
theorem compl_top : (⊤ : α)ᶜ = ⊥ := by
  have h := inf_compl_eq_bot (⊤ : α); rwa [top_inf_eq] at h

-- ════════════════════════════════════════════════════
-- § 2. Order Properties
-- ════════════════════════════════════════════════════

theorem compl_le_compl_iff_le : aᶜ ≤ bᶜ ↔ b ≤ a :=
  ⟨fun h => OrthocomplementedLattice.compl_compl b ▸
            OrthocomplementedLattice.compl_compl a ▸
            OrthocomplementedLattice.compl_antitone h,
   fun h => OrthocomplementedLattice.compl_antitone h⟩

theorem compl_injective : Function.Injective (compl : α → α) :=
  fun _ _ h => by
    have := congrArg compl h
    rwa [OrthocomplementedLattice.compl_compl, OrthocomplementedLattice.compl_compl] at this

theorem compl_surjective : Function.Surjective (compl : α → α) :=
  fun a => ⟨aᶜ, OrthocomplementedLattice.compl_compl a⟩

theorem compl_eq_iff_eq_compl : aᶜ = b ↔ a = bᶜ := by
  constructor
  · intro h; rw [← h, OrthocomplementedLattice.compl_compl]
  · intro h; rw [h, OrthocomplementedLattice.compl_compl]

-- ════════════════════════════════════════════════════
-- § 3. De Morgan Laws
-- ════════════════════════════════════════════════════

theorem compl_sup (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by
  apply le_antisymm
  · exact le_inf (compl_antitone le_sup_left) (compl_antitone le_sup_right)
  · -- aᶜ ⊓ bᶜ ≤ aᶜ, so aᶜᶜ = a ≤ (aᶜ ⊓ bᶜ)ᶜ; similarly for b
    have ha : a ≤ (aᶜ ⊓ bᶜ)ᶜ := by
      have h1 : aᶜ ⊓ bᶜ ≤ aᶜ := inf_le_left
      have h2 : aᶜᶜ ≤ (aᶜ ⊓ bᶜ)ᶜ := compl_antitone h1
      rwa [OrthocomplementedLattice.compl_compl] at h2
    have hb : b ≤ (aᶜ ⊓ bᶜ)ᶜ := by
      have h1 : aᶜ ⊓ bᶜ ≤ bᶜ := inf_le_right
      have h2 : bᶜᶜ ≤ (aᶜ ⊓ bᶜ)ᶜ := compl_antitone h1
      rwa [OrthocomplementedLattice.compl_compl] at h2
    have hab : a ⊔ b ≤ (aᶜ ⊓ bᶜ)ᶜ := sup_le ha hb
    have h3 : (aᶜ ⊓ bᶜ)ᶜᶜ ≤ (a ⊔ b)ᶜ := compl_antitone hab
    rwa [OrthocomplementedLattice.compl_compl] at h3

theorem compl_inf (a b : α) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := by
  have h := compl_sup aᶜ bᶜ
  rw [OrthocomplementedLattice.compl_compl, OrthocomplementedLattice.compl_compl] at h
  rw [← h, OrthocomplementedLattice.compl_compl]

-- ════════════════════════════════════════════════════
-- § 4. IsCompl and ComplementedLattice
-- ════════════════════════════════════════════════════

theorem isCompl_compl (a : α) : IsCompl a aᶜ where
  disjoint := disjoint_iff.mpr (inf_compl_eq_bot a)
  codisjoint := codisjoint_iff.mpr (sup_compl_eq_top a)

instance instComplementedLattice : ComplementedLattice α :=
  ⟨fun a => ⟨aᶜ, isCompl_compl a⟩⟩

end OrthocomplementedLattice

-- ════════════════════════════════════════════════════
-- § 5. BooleanAlgebra → OrthocomplementedLattice
-- ════════════════════════════════════════════════════

/-- Every Boolean algebra is an orthocomplemented lattice. The converse fails:
    ortholattices need not be distributive. -/
instance (priority := 100) instBooleanOrtho {α : Type*} [BooleanAlgebra α] :
    OrthocomplementedLattice α where
  compl_compl := _root_.compl_compl
  compl_antitone := fun h => _root_.compl_le_compl h
  inf_compl_le_bot := BooleanAlgebra.inf_compl_le_bot
  top_le_sup_compl := BooleanAlgebra.top_le_sup_compl

end Semantics.PossibilitySemantics
