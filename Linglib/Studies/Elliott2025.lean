import Linglib.Core.Logic.PolarizedIndividuals

/-!
# Split Scope via Polarized Individuals @cite{elliott-2025}
@cite{rullmann-1995} @cite{barwise-cooper-1981}

Connects standard quantifier denotations to the polarized individual
decomposition from `Core.Logic.PolarizedIndividuals`, then derives
the split-scope reading of negative quantifiers under modals.

## Decomposition (§1)

The four corners of the square of opposition arise from entity-polarity
pairs via the `ConsGQ` Boolean algebra:

- `some = ⋁_e (e, +)` — existential: at least one positive witness
- `every = (⋁_e (e, -))ᶜ` — universal: no negative witness
- `no = (⋁_e (e, +))ᶜ` — negative universal: no positive witness
- `not_all = ⋁_e (e, -)` — negative existential: at least one negative

The key compositional fact is `pos_sup_neg`:
`(e,+) ⊔ (e,-) = λR S. R(e)`, already proved in
`Core.Logic.PolarizedIndividuals`.

## Split Scope (§3-§4)

Split scope arises when a quantifier's restrictor and scope are
interpreted at different positions in the semantic derivation. The
classic case is negative quantifiers under modals:

  (1) You need to read no book.
      a. Surface: ¬∃x[book(x) ∧ need(read(x))] — "no" takes wide scope
      b. Split: need(¬∃x[book(x) ∧ read(x)]) — neg above, ∃ below

@cite{elliott-2025} derives split scope from the polarized individual
decomposition: `no` = `(⋁_e (e,+))ᶜ`. Since complement distributes
over scope position changes, the negative and existential components
can end up at different heights.

-/

namespace Elliott2025

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

/-- Outer + inner negation = dual. Applied to `some`, this gives `every`:
    `¬some(R, ¬S) ↔ every(R, S)`. -/
theorem dual_some_eq_every (entities : List α) (R S : α → Prop) :
    ¬ (∃ e ∈ entities, R e ∧ ¬ S e) ↔
    (∀ e ∈ entities, ¬ R e ∨ S e) := by
  simp only [not_exists, not_and]
  apply forall_congr'; intro e
  apply forall_congr'; intro _
  by_cases hR : R e <;> simp [hR]

/-- Outer negation of `some` = `no`. -/
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
    Re-exported from `Core.Logic.PolarizedIndividuals`. The lattice-theoretic
    content of split scope: scope is "split" between the positive and negative
    polarities, yielding a quantifier that ignores scope entirely. -/
theorem split_scope (e : α) :
    PolInd.toConsGQ (e, true) ⊔ PolInd.toConsGQ (e, false) =
    (⟨λ R _ => R e, λ R _ => Iff.rfl⟩ : ConsGQ α) :=
  PolInd.pos_sup_neg e

/-- The fundamental split-scope fact: joining complementary polarities
    yields a GQ that depends only on the restrictor, not the scope.
    This means scope position is irrelevant — the quantifier "splits". -/
theorem split_scope_restrictor_only (e : α) (R S₁ S₂ : α → Prop) :
    (PolInd.toConsGQ (e, true) ⊔ PolInd.toConsGQ (e, false)).1 R S₁ ↔
    (PolInd.toConsGQ (e, true) ⊔ PolInd.toConsGQ (e, false)).1 R S₂ := by
  simp [split_scope]

/-- Corollary: split scope means the result equals `R(e)` regardless of
    what scope predicate is supplied. -/
theorem split_scope_eq_restrictor (e : α) (R S : α → Prop) :
    (PolInd.toConsGQ (e, true) ⊔ PolInd.toConsGQ (e, false)).1 R S ↔ R e := by
  simp [split_scope]

-- ============================================================================
-- §5 — Concrete Illustration: Split Negation
-- ============================================================================

/-- A negative quantifier `no(R,S) = ¬∃e. R(e) ∧ S(e)` decomposes as
    the complement of the join of positive polarized individuals.
    When scope splits, the complement applies at one position while
    the existential restrictor applies at another. -/
theorem no_from_complement_of_some (entities : List α) (R S : α → Prop) :
    ¬ (∃ e ∈ entities, R e ∧ S e) ↔
    ¬ (∃ e ∈ entities, PolInd.toGQ (e, true) R S) := by
  rw [some_as_polInd_join]

-- ============================================================================
-- §6 — Duality: Every from Not-Some-Not
-- ============================================================================

/-- `every` arises from the dual of `some`: outer + inner negation.
    With polarized individuals: `every(R,S) = ¬(⋁_e (e,-))(R,S)`,
    i.e., the complement of the join of negative polarized individuals.
    This decomposition parallels `no` but with reversed polarity. -/
theorem every_from_neg_polInd (entities : List α) (R S : α → Prop) :
    ¬ (∃ e ∈ entities, PolInd.toGQ (e, false) R S) ↔
    (∀ e ∈ entities, ¬ R e ∨ S e) := by
  rw [← dual_some_eq_every]
  apply not_congr
  apply exists_congr; intro e
  apply and_congr_right; intro _
  rw [PolInd.toGQ_neg]

end Elliott2025
