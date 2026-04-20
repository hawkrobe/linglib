import Linglib.Core.Logic.PolarizedIndividuals

/-!
# Determiners via Polarized Individuals @cite{elliott-2025}
@cite{barwise-cooper-1981}

Connects standard quantifier denotations to the polarized individual
decomposition from `Core.Logic.PolarizedIndividuals`.

The four corners of the square of opposition arise from entity-polarity
pairs via the `ConsGQ` Boolean algebra:

- `some = ⋁_e (e, +)` — existential: at least one positive witness
- `every = (⋁_e (e, -))ᶜ` — universal: no negative witness
- `no = (⋁_e (e, +))ᶜ` — negative universal: no positive witness
- `not_all = ⋁_e (e, -)` — negative existential: at least one negative

The key compositional fact for split scope is `pos_sup_neg`:
`(e,+) ⊔ (e,-) = λR S. R(e)`, already proved in
`Core.Logic.PolarizedIndividuals`.

-/

namespace Semantics.Quantification.Polarized

open Core.Quantification

variable {α : Type*}

-- ============================================================================
-- §1 — Quantifiers as PolInd Joins (Concrete, Finite Domain)
-- ============================================================================

/-- On a concrete list of entities, `some(R,S) = ⋁_e R(e) ∧ S(e)`,
    which is the join of positive polarized individuals. -/
theorem some_as_polInd_join (entities : List α) (R S : α → Prop) :
    (∃ e ∈ entities, R e ∧ S e) ↔
    (∃ e ∈ entities, PolInd.toGQ (e, true) R S) := by
  apply exists_congr; intro e
  apply and_congr_right; intro _
  exact (PolInd.toGQ_pos e R S).symm

/-- On a concrete list of entities, `no(R,S) = ⋀_e ¬(R(e) ∧ S(e))`,
    which is the meet of complements of positive polarized individuals. -/
theorem no_as_polInd_neg (entities : List α) (R S : α → Prop) :
    (∀ e ∈ entities, ¬ R e ∨ ¬ S e) ↔
    (∀ e ∈ entities, ¬ PolInd.toGQ (e, true) R S) := by
  apply forall_congr'; intro e
  apply forall_congr'; intro _
  rw [PolInd.toGQ_pos]
  tauto

/-- On a concrete list, `every(R,S) = ⋀_e ¬(R(e) ∧ ¬S(e))`,
    which is the meet of complements of negative polarized individuals. -/
theorem every_as_polInd_neg (entities : List α) (R S : α → Prop) :
    (∀ e ∈ entities, ¬ R e ∨ S e) ↔
    (∀ e ∈ entities, ¬ PolInd.toGQ (e, false) R S) := by
  apply forall_congr'; intro e
  apply forall_congr'; intro _
  rw [PolInd.toGQ_neg]
  tauto

-- ============================================================================
-- §2 — Inner Negation Swaps Polarity
-- ============================================================================

/-- Inner negation (negating the scope) swaps the polarity of a
    polarized individual: `⟦(e,+)⟧(R, ¬S) ↔ ⟦(e,-)⟧(R, S)`. -/
theorem inner_neg_swaps_polarity (e : α) (R S : α → Prop) :
    PolInd.toGQ (e, true) R (λ x => ¬ S x) ↔
    PolInd.toGQ (e, false) R S := by
  simp [PolInd.toGQ]

/-- Inner negation on a quantifier built from positive PolInds yields
    the corresponding negative-PolInd quantifier. -/
theorem inner_neg_pos_list_eq_neg_list (entities : List α) (R S : α → Prop) :
    (∃ e ∈ entities, PolInd.toGQ (e, true) R (λ x => ¬ S x)) ↔
    (∃ e ∈ entities, PolInd.toGQ (e, false) R S) := by
  apply exists_congr; intro e
  apply and_congr_right; intro _
  exact inner_neg_swaps_polarity e R S

-- ============================================================================
-- §3 — Complement and the Duality Square
-- ============================================================================

/-- Outer negation (negating the result) + inner negation (negating the
    scope) = dual. Applied to `some`, this gives `every`:
    `¬some(R, ¬S) ↔ every(R, S)`. -/
theorem dual_some_eq_every (entities : List α) (R S : α → Prop) :
    ¬ (∃ e ∈ entities, R e ∧ ¬ S e) ↔
    (∀ e ∈ entities, ¬ R e ∨ S e) := by
  simp only [not_exists, not_and]
  apply forall_congr'; intro e
  apply forall_congr'; intro _
  by_cases hR : R e <;> simp [hR]

/-- Outer negation of `some` = `no`: `¬(∃e. R(e) ∧ S(e)) ↔ ∀e. R(e) → ¬S(e)`. -/
theorem outer_neg_some_eq_no (entities : List α) (R S : α → Prop) :
    ¬ (∃ e ∈ entities, R e ∧ S e) ↔
    (∀ e ∈ entities, ¬ R e ∨ ¬ S e) := by
  simp only [not_exists, not_and]
  apply forall_congr'; intro e
  apply forall_congr'; intro _
  by_cases hR : R e
  · simp [hR]
  · simp [hR]

-- ============================================================================
-- §4 — Split Scope via PolInd Complementarity
-- ============================================================================

/-- The split scope reading: `(e,+) ⊔ (e,-) = λR S. R(e)`.
    Re-exported from `Core.Logic.PolarizedIndividuals` for convenience.
    This is the lattice-theoretic content of split scope: scope is
    "split" between the positive and negative polarities, yielding a
    quantifier that ignores scope entirely. -/
theorem split_scope (e : α) :
    PolInd.toConsGQ (e, true) ⊔ PolInd.toConsGQ (e, false) =
    (⟨λ R _ => R e, λ R _ => Iff.rfl⟩ : ConsGQ α) :=
  PolInd.pos_sup_neg e

end Semantics.Quantification.Polarized
